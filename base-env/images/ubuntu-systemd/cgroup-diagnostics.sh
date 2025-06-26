#!/bin/bash

echo "=== CGROUP DIAGNOSTICS SCRIPT ==="
echo "$(date)"
echo

echo "=== HOST CGROUP STRUCTURE ==="
echo "Root cgroup controllers:"
cat /sys/fs/cgroup/cgroup.controllers 2>/dev/null || echo "No controllers file"
echo
echo "Root cgroup subtree control:"
cat /sys/fs/cgroup/cgroup.subtree_control 2>/dev/null || echo "No subtree control"
echo
echo "Root cgroup processes:"
cat /sys/fs/cgroup/cgroup.procs 2>/dev/null | wc -l | xargs echo "Process count:"
echo

echo "=== EXISTING CGROUP HIERARCHY ==="
echo "All cgroup directories (max depth 3):"
find /sys/fs/cgroup -maxdepth 3 -type d | sort
echo

echo "=== DELEGATION STATUS ==="
echo "Looking for cgroup.subtree_control files:"
find /sys/fs/cgroup -name "cgroup.subtree_control" -exec sh -c 'echo "=== $1 ==="; cat "$1" 2>/dev/null' _ {} \;
echo

echo "=== CONTAINER STATUS BEFORE START ==="
echo "Sprite container status:"
sprite status 2>/dev/null || echo "No sprite status available"
echo

echo "=== STARTING CONTAINER WITH DIAGNOSTICS ==="
echo "Starting sprite container..."
sprite start
sleep 2

echo "=== CONTAINER STATUS AFTER START ==="
sprite status 2>/dev/null || echo "No sprite status available"
echo

echo "=== POST-START CGROUP STRUCTURE ==="
echo "New cgroup directories:"
find /sys/fs/cgroup -maxdepth 4 -type d | sort
echo

echo "=== CONTAINER CGROUP PLACEMENT ==="
echo "Container process cgroup info:"
sprite exec cat /proc/self/cgroup 2>/dev/null || echo "Cannot access container cgroup info"
echo
echo "Container cgroup controllers:"
sprite exec cat /sys/fs/cgroup/cgroup.controllers 2>/dev/null || echo "Cannot access container controllers"
echo
echo "Container cgroup subtree control:"
sprite exec cat /sys/fs/cgroup/cgroup.subtree_control 2>/dev/null || echo "Cannot access container subtree control"
echo

echo "=== SYSTEMD-SPECIFIC CHECKS ==="
echo "Looking for systemd-related cgroups:"
find /sys/fs/cgroup -name "*systemd*" -o -name "*container*" -o -name "*sprite*" 2>/dev/null | sort
echo

echo "=== CGROUP MOUNT INFO ==="
echo "Cgroup mount details:"
mount | grep cgroup
echo

echo "=== KERNEL CONFIGURATION ==="
echo "Kernel command line:"
cat /proc/cmdline
echo
echo "Kernel version:"
uname -a
echo
echo "Checking key cgroup kernel configs:"
if [ -f /proc/config.gz ]; then
    echo "Available via /proc/config.gz"
    zcat /proc/config.gz | grep -E "CONFIG_CGROUP|CONFIG_MEMCG|CONFIG_BLK_CGROUP" | head -10
elif [ -f "/boot/config-$(uname -r)" ]; then
    echo "Available via /boot/config"
    cat "/boot/config-$(uname -r)" | grep -E "CONFIG_CGROUP|CONFIG_MEMCG|CONFIG_BLK_CGROUP" | head -10
else
    echo "No kernel config found"
fi
echo
echo "Systemd cgroup parameters:"
find /sys/module -name "*systemd*" -o -name "*cgroup*" 2>/dev/null | head -5
echo

echo "=== SYSTEMD PROCESS CHECK ==="
echo "Checking if systemd is running in container:"
sprite exec pgrep -f systemd 2>/dev/null || echo "No systemd processes found"
echo
echo "Systemd process details:"
sprite exec ps aux | grep systemd | grep -v grep 2>/dev/null || echo "No systemd processes in ps output"
echo

echo "=== CONTROLLER AVAILABILITY IN CONTAINER ==="
echo "Available controllers in container:"
sprite exec find /sys/fs/cgroup -name "*.max" -o -name "*.current" 2>/dev/null | head -10
echo

echo "=== ERROR LOGS ==="
echo "Checking for systemd errors:"
sprite exec journalctl --no-pager -n 20 2>/dev/null || echo "No journalctl available"
echo

echo "=== SUMMARY ==="
echo "Key findings:"
echo "- Host root controllers: $(cat /sys/fs/cgroup/cgroup.controllers 2>/dev/null)"
echo "- Host root subtree: $(cat /sys/fs/cgroup/cgroup.subtree_control 2>/dev/null)"
echo "- Container running: $(sprite status 2>/dev/null | grep -q running && echo "YES" || echo "NO")"
echo "- Container cgroup path: $(sprite exec cat /proc/self/cgroup 2>/dev/null | head -1)"

echo
echo "=== DIAGNOSTICS COMPLETE ===" 