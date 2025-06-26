# Sprite OCI Configuration Recommendations for systemd

**File**: `sprite-oci.json`  
**Goal**: Make environment systemd-compatible  
**Status**: 🔧 **REQUIRES MODIFICATIONS**  

## Critical Issues Found

### 1. **Cgroup Mount Configuration** 🚨 **CRITICAL**

**Current**:
```json
{
  "destination": "/sys/fs/cgroup",
  "type": "cgroup2", 
  "source": "cgroup2",
  "options": [
    "nosuid",
    "noexec", 
    "nodev",
    "relatime"
  ]
}
```

**Required for systemd**:
```json
{
  "destination": "/sys/fs/cgroup",
  "type": "cgroup2",
  "source": "cgroup2", 
  "options": [
    "nosuid",
    "noexec",
    "nodev", 
    "relatime",
    "nsdelegate",
    "memory_recursiveprot"
  ]
}
```

### 2. **Environment Variables** ⚠️ **IMPORTANT**

**Current**:
```json
"env": [
  "PATH=/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin",
  "HOME=/root",
  "SHLVL=0",
  "K8S_VERSION=v1.14.8",
  "CONTAINER_WRAPPED=true",
  "CONSOLE_SOCKET=/var/run/sprite/container-process-1-1750943917053573988.sock"
]
```

**Required additions**:
```json
"env": [
  "PATH=/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin",
  "HOME=/root",
  "HOSTNAME=sprite-container",
  "TERM=xterm",
  "container=docker",
  "SHLVL=0",
  "K8S_VERSION=v1.14.8", 
  "CONTAINER_WRAPPED=true",
  "CONSOLE_SOCKET=/var/run/sprite/container-process-1-1750943917053573988.sock"
]
```

### 3. **Process Configuration** ⚠️ **IMPORTANT**

**Current**:
```json
"process": {
  "terminal": true,
  "args": [
    "/init",
    "tail", 
    "-f",
    "/dev/null"
  ]
}
```

**Required for systemd**:
```json  
"process": {
  "terminal": false,
  "args": [
    "/sbin/init"
  ]
}
```

### 4. **Mount Size Optimization** ✅ **OPTIONAL**

**Current `/run` mount**:
```json
{
  "destination": "/run",
  "type": "tmpfs",
  "source": "tmpfs", 
  "options": [
    "nosuid",
    "strictatime",
    "mode=755",
    "size=65536k"
  ]
}
```

**Recommended (optional increase)**:
```json
{
  "destination": "/run", 
  "type": "tmpfs",
  "source": "tmpfs",
  "options": [
    "nosuid",
    "strictatime", 
    "mode=755",
    "size=131072k"
  ]
}
```

## Complete Recommended Changes

### Priority 1: Cgroup Delegation (CRITICAL)
Add `nsdelegate` and `memory_recursiveprot` to cgroup2 mount options.

### Priority 2: Environment Variables (IMPORTANT)  
Add missing environment variables for systemd compatibility:
- `HOSTNAME=sprite-container`
- `TERM=xterm`
- `container=docker`

### Priority 3: Process Configuration (IMPORTANT)
- Change `terminal: false` for daemon mode
- Change `args: ["/sbin/init"]` for systemd

### Priority 4: Resource Optimization (OPTIONAL)
- Consider doubling `/run` tmpfs to 128MB for safety margin

## Implementation Steps

1. **Test cgroup changes first** - This is the most critical fix
2. **Add environment variables** - Required for proper systemd initialization  
3. **Update process configuration** - Change from s6-init to systemd
4. **Monitor resource usage** - Verify /run space is adequate

## Expected Outcome

With these changes, systemd should be able to:
- ✅ **Initialize properly** with delegated cgroup control
- ✅ **Manage services** with proper hierarchy 
- ✅ **Handle console output** via journald
- ✅ **Detect container environment** for optimized behavior

## Verification Commands

After implementing changes, verify with:
```bash
# Check cgroup mount options
sprite exec mount | grep cgroup2

# Verify environment variables
sprite exec env | grep -E "(HOSTNAME|TERM|container)"

# Check systemd status
sprite exec systemctl status

# Verify cgroup hierarchy  
sprite exec cat /proc/1/cgroup
``` 