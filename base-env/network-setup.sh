#!/bin/bash
set -euo pipefail

# Enable command printing only if DEBUG=true
if [[ "${DEBUG:-false}" == "true" ]]; then
    set -x
fi

# Check required environment variables
if [ -z "${SPRITE_WRITE_DIR:-}" ]; then
    echo "Error: SPRITE_WRITE_DIR environment variable is not set" >&2
    exit 1
fi

# Configuration (must match server policy manager defaults)
NS_NAME=sprite
VETH_HOST=spr0-host
VETH_CONT=spr0
IPV4_CIDR=10.0.0.0/30
IPV4_HOST=10.0.0.2
IPV4_CONT=10.0.0.1

IPV6_CIDR=fdf::/120
IPV6_HOST=fdf::2
IPV6_CONT=fdf::1

OUT_IF=eth0  # change if your uplink is different

# Enable kernel forwarding settings
setup_sysctl() {
    sysctl -w net.ipv4.ip_forward=1 >/dev/null
    sysctl -w net.ipv6.conf.all.forwarding=1 >/dev/null
}

# Configure namespace-specific sysctl settings
setup_namespace_sysctl() {
    # Allow routing to 127/8 on non-lo (required for DNAT -> 127.0.0.1)
    ip netns exec $NS_NAME sysctl -w net.ipv4.conf.spr0.route_localnet=1 >/dev/null
    ip netns exec $NS_NAME sysctl -w net.ipv4.conf.all.route_localnet=1 >/dev/null
    
    # Avoid strict source validation drops
    ip netns exec $NS_NAME sysctl -w net.ipv4.conf.spr0.rp_filter=2 >/dev/null
}

# Note: veth creation, netns creation, addressing and routes are now handled by the policy manager.
# We only apply sysctls, expose the netns path, and set up NAT here.

# Expose netns path (best-effort)
expose_namespace_path() {
    mkdir -p /run/netns
    if [ -e /var/run/netns/$NS_NAME ] && [ ! -e /run/netns/$NS_NAME ]; then
        ln -sf /var/run/netns/$NS_NAME /run/netns/$NS_NAME || true
    fi
}

# Cleanup existing NAT tables
cleanup_nftables() {
    if ! command -v nft &>/dev/null; then
        return 0
    fi
    # Clean up host namespace NAT
    nft delete table inet sprite_nat 2>/dev/null || true
    # Clean up container namespace NAT
    if ip netns list | grep -q "^${NS_NAME}\s"; then
        ip netns exec $NS_NAME nft delete table ip nat 2>/dev/null || true
    fi
}

# Full cleanup function - removes all network configuration
cleanup() {
    set -e  # Exit on any error
    
    echo "🧹 Cleaning up network namespace '$NS_NAME'..."
    
    # Debug: Show what we can see
    echo "Debug: Checking for namespace in ip netns list..."
    ip netns list | grep "$NS_NAME" || echo "  No namespace found in ip netns list"
    
    echo "Debug: Checking for namespace files..."
    ls -la /run/netns/ 2>/dev/null || echo "  Cannot list /run/netns/"
    ls -la /var/run/netns/ 2>/dev/null || echo "  Cannot list /var/run/netns/"
    
    # Remove nftables rules
    echo "Debug: Calling cleanup_nftables..."
    cleanup_nftables
    
    # Kill any processes in the namespace (if we can)
    echo "Debug: Checking for processes in namespace..."
    if ip netns list | grep -q "^${NS_NAME}\s"; then
        echo "  Found namespace, checking for processes..."
        # List and kill processes in namespace
        ip netns pids $NS_NAME | while read pid; do
            if [[ "$pid" =~ ^[0-9]+$ ]]; then
                echo "Killing process $pid in namespace..."
                kill -TERM $pid
            fi
        done
        # Give processes time to exit
        sleep 0.5
        # Force kill any remaining
        ip netns pids $NS_NAME | while read pid; do
            if [[ "$pid" =~ ^[0-9]+$ ]]; then
                kill -KILL $pid
            fi
        done
    else
        echo "  No namespace found to check for processes"
    fi
    
    # Remove host-side veth if it still exists (do this before deleting namespace)
    echo "Debug: Checking for host veth interface $VETH_HOST..."
    if ip link show $VETH_HOST &>/dev/null; then
        echo "Deleting host veth interface $VETH_HOST..."
        ip link delete $VETH_HOST
    else
        echo "  Host veth interface not found"
    fi
    
    # Delete namespace (this also removes interfaces inside it)
    if ip netns list | grep -q "^${NS_NAME}\s"; then
        echo "Deleting network namespace $NS_NAME..."
        ip netns delete $NS_NAME
    fi
    
    # Unmount and remove namespace files
    for nsfile in "/run/netns/$NS_NAME" "/var/run/netns/$NS_NAME"; do
        if [ -e "$nsfile" ]; then
            echo "Cleaning up namespace file $nsfile..."
            # Check if it's mounted
            if mountpoint -q "$nsfile"; then
                echo "  Unmounting $nsfile..."
                umount "$nsfile" || umount -l "$nsfile"
            fi
            # Remove the file
            echo "  Removing file $nsfile..."
            rm -f "$nsfile"
        fi
    done
    
    # Verify cleanup worked
    echo "Verifying cleanup..."
    if ip netns list | grep -q "^${NS_NAME}\s"; then
        echo "❌ ERROR: Namespace '$NS_NAME' still exists after cleanup!"
        exit 1
    fi
    if [ -e "/run/netns/$NS_NAME" ] || [ -e "/var/run/netns/$NS_NAME" ]; then
        echo "❌ ERROR: Namespace files still exist after cleanup!"
        ls -la /run/netns/$NS_NAME 2>/dev/null || true
        ls -la /var/run/netns/$NS_NAME 2>/dev/null || true
        exit 1
    fi
    
    echo "✅ Network namespace '$NS_NAME' cleanup completed"
}

# Setup NAT (masquerade) using nftables. Forward filter is handled by policy manager.
setup_nat() {
    # Clean up any existing rules first
    cleanup_nftables
    
    # === Host namespace NAT ===
    # Create NAT table
    nft add table inet sprite_nat

    # POSTROUTING chain: NAT public destinations
    nft add chain inet sprite_nat postrouting { type nat hook postrouting priority 100 \; }

    # Masquerade public IPv4 (not RFC1918, loopback, link-local)
    nft add rule inet sprite_nat postrouting \
    ip saddr $IPV4_CIDR \
    ip daddr != { 10.0.0.0/8, 172.16.0.0/12, 192.168.0.0/16, 127.0.0.0/8, 169.254.0.0/16 } \
    oifname "$OUT_IF" masquerade

    # Masquerade public IPv6 (not ULA, link-local, loopback, multicast)
    nft add rule inet sprite_nat postrouting \
    ip6 saddr $IPV6_CIDR \
    ip6 daddr != { fd00::/8, fe80::/10, ::1/128, ff00::/8 } \
    oifname "$OUT_IF" masquerade

    # === Container namespace NAT (DNAT to localhost) ===
    # IPv4 NAT - redirect container IP to localhost for services
    ip netns exec $NS_NAME nft add table ip nat
    ip netns exec $NS_NAME nft add chain ip nat prerouting { type nat hook prerouting priority -100 \; }
    ip netns exec $NS_NAME nft add chain ip nat output { type nat hook output priority -100 \; }

    # DNAT: host→container traffic to 10.10.0.2 → 127.0.0.1 (for port forwarding)
    ip netns exec $NS_NAME nft add rule ip nat prerouting iifname "$VETH_CONT" ip daddr $IPV4_CONT tcp dport != 0 dnat to 127.0.0.1

    # DNAT: local container traffic to 10.10.0.2 → 127.0.0.1 (for localhost access)
    ip netns exec $NS_NAME nft add rule ip nat output ip daddr $IPV4_CONT tcp dport != 0 dnat to 127.0.0.1

    # IPv6: No DNAT needed - fd00::2 is bound directly to the interface
    # Applications can bind to fd00::2 and it will be routable from the host
}

# resolv.conf is now written by the policy manager via HostResolvPath.

# Display current network configuration
info() {
    echo "🔍 Network Configuration Status"
    echo "==============================="
    
    # Check namespace
    echo -e "\n📦 Namespace:"
    if ip netns list | grep -q "^${NS_NAME}\s"; then
        echo "  ✅ Namespace '$NS_NAME' exists"
        ip netns list | grep "^${NS_NAME}\s"
    else
        echo "  ❌ Namespace '$NS_NAME' not found"
    fi
    
    # Check host interface
    echo -e "\n🔌 Host Interface ($VETH_HOST):"
    if ip link show $VETH_HOST &>/dev/null; then
        echo "  ✅ Interface exists"
        ip addr show $VETH_HOST | grep -E "(inet|inet6|state)" | sed 's/^/  /'
    else
        echo "  ❌ Interface not found"
    fi
    
    # Check container interface
    echo -e "\n🔌 Container Interface ($VETH_CONT in namespace):"
    if ip netns list | grep -q "^${NS_NAME}\s"; then
        if ip netns exec $NS_NAME ip link show $VETH_CONT &>/dev/null; then
            echo "  ✅ Interface exists in namespace"
            ip netns exec $NS_NAME ip addr show $VETH_CONT | grep -E "(inet|inet6|state)" | sed 's/^/  /'
        else
            echo "  ❌ Interface not found in namespace"
        fi
    else
        echo "  ⚠️  Cannot check - namespace doesn't exist"
    fi
    
    # Check routes in namespace
    echo -e "\n🛣️  Routes in namespace:"
    if ip netns list | grep -q "^${NS_NAME}\s"; then
        echo "  IPv4 routes:"
        ip netns exec $NS_NAME ip route | sed 's/^/    /'
        echo "  IPv6 routes:"
        ip netns exec $NS_NAME ip -6 route | grep -v "fe80::" | sed 's/^/    /'
    else
        echo "  ⚠️  Cannot check - namespace doesn't exist"
    fi
    
    # Check nftables rules
    echo -e "\n🔥 Firewall Rules:"
    if command -v nft &>/dev/null; then
        local nat_exists=false
        local filter_exists=false
        
        if nft list tables 2>/dev/null | grep -q "inet sprite_nat"; then
            nat_exists=true
        fi
        if nft list tables 2>/dev/null | grep -q "inet sprite_filter"; then
            filter_exists=true
        fi
        
        if [[ "$nat_exists" == "true" ]] || [[ "$filter_exists" == "true" ]]; then
            if [[ "$nat_exists" == "true" ]]; then
                echo "  ✅ NAT table exists"
                nft list table inet sprite_nat 2>/dev/null | grep -E "(chain|rule)" | sed 's/^/    /'
            fi
            if [[ "$filter_exists" == "true" ]]; then
                echo "  ✅ Filter table exists"
                nft list table inet sprite_filter 2>/dev/null | grep -E "(chain|rule)" | sed 's/^/    /'
            fi
        else
            echo "  ❌ No sprite nftables rules found"
        fi
    else
        echo "  ⚠️  nft command not available"
    fi
    
    # Check DNS configuration
    echo -e "\n🌐 DNS Configuration:"
    local resolv_file="${SPRITE_WRITE_DIR}/container/resolv.conf"
    if [ -f "$resolv_file" ]; then
        echo "  ✅ Custom resolv.conf exists at: $resolv_file"
        echo "  Nameservers:"
        grep "^nameserver" "$resolv_file" | head -5 | sed 's/^/    /'
        local ns_count=$(grep -c "^nameserver" "$resolv_file")
        if [ $ns_count -gt 5 ]; then
            echo "    ... and $((ns_count - 5)) more"
        fi
    else
        echo "  ❌ Custom resolv.conf not found at: $resolv_file"
    fi
    
    # Check kernel settings
    echo -e "\n⚙️  Kernel Settings:"
    echo -n "  IPv4 forwarding: "
    cat /proc/sys/net/ipv4/ip_forward
    echo -n "  IPv6 forwarding: "
    cat /proc/sys/net/ipv6/conf/all/forwarding
    
    echo -e "\n==============================="
}

# Main function that orchestrates the setup
main() {
    setup_sysctl
    expose_namespace_path
    setup_namespace_sysctl || true
    setup_nat
    echo "✅ Host NAT configured; policy manager is responsible for veth/netns/dns"
}

# Handle command line arguments
if [[ "${1:-}" == "cleanup" ]] || [[ "${1:-}" == "clean" ]]; then
    cleanup
elif [[ "${1:-}" == "info" ]]; then
    info
else
    main
fi
