# Sprite VM Environment Report

**Environment**: VM (sprite exec)  
**Status**: ⚠️ **SYSTEMD TARGET ENVIRONMENT** - environmental analysis for systemd deployment  
**Date**: 2025-06-26  

## Current Environment (Placeholder Init)

*Note: Current init system is placeholder - analyzing environment for systemd compatibility*

### Expected Standard Streams for systemd
- **stdin (fd 0)**: Should be `/dev/null` ✅ 
- **stdout (fd 1)**: Should be `/dev/null` or console ⚠️ Currently `/dev/pts/0`
- **stderr (fd 2)**: Should be `/dev/null` or console ⚠️ Currently `/dev/pts/0`

### Environment Variables Analysis
```bash
PATH=/command:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin
```
**Differences from working Docker environment**:
- ❌ **Missing**: `HOSTNAME` (Docker: `e466b12c6d8e`)
- ❌ **Missing**: `TERM` (Docker: `xterm`) 
- ❌ **Missing**: `HOME` (Docker: `/root`)
- ⚠️ **Extra**: `/command:` prefix in PATH 

## Console & TTY Setup

**Console Device**: `/dev/console`
```bash
crw--w---- 1 root tty 136, 0 Jun 26 13:18 /dev/console
```
- **Device Type**: Character device `136,0` (PTY) ✅
- **Permissions**: `0620` (crw--w----)
- **Owner**: root:tty

## Cgroups Configuration

**Current Cgroup**: `0::/` (root cgroup)

**Cgroup Mount**: 
```bash
cgroup2 on /sys/fs/cgroup type cgroup2 (rw,nosuid,nodev,noexec,relatime)
```

**Critical Differences from Docker**:
- ❌ **Missing `nsdelegate`** - systemd needs delegated cgroup control
- ❌ **Missing `memory_recursiveprot`** - systemd memory pressure handling
- ⚠️ **Flat cgroup structure** vs Docker's hierarchical (`/init.scope`)

## Critical Mounts

```bash
overlay on / type overlay (rw,relatime,lowerdir=/mnt/app-image,upperdir=/dev/fly_vol/juicefs/data/root-upper/upper,workdir=/dev/fly_vol/juicefs/data/root-upper/work)
proc on /proc type proc (rw,nosuid,nodev,noexec,relatime)
tmpfs on /dev type tmpfs (rw,nosuid,size=65536k,mode=755)  
sysfs on /sys type sysfs (rw,nosuid,nodev,noexec,relatime)
cgroup2 on /sys/fs/cgroup type cgroup2 (rw,nosuid,nodev,noexec,relatime)
tmpfs on /run type tmpfs (rw,nosuid,size=65536k,mode=755)
```

**Key Differences from Docker**:
- ✅ **Adequate `/run` tmpfs**: 64MB (Docker uses 32KB, so this is sufficient)
- ⚠️ **Complex overlay FS**: JuiceFS-backed overlay with multiple layers
- ❌ **Missing cgroup features**: No `nsdelegate`, `memory_recursiveprot`
- ⚠️ **Restricted `/proc` areas**: Multiple read-only proc mounts

## Runtime Directories

**Current `/run/` Structure**:
```bash
drwxr-xr-x 6 root root  140 Jun 26 13:18 .
drwxr-xr-x 6 root root  140 Jun 26 13:18 s6
drwxr-xr-x 2 root root   60 Jun 26 13:18 s6-linux-init-container-results
lrwxrwxrwx 1 root root   23 Jun 26 13:18 s6-rc -> s6-rc:s6-rc-init:knngLB
drwxr-xr-x 3 root root  160 Jun 26 13:18 s6-rc:s6-rc-init:knngLB
drwxr-xr-x 4 root root  120 Jun 26 13:18 service
```

**Space Analysis**:
- **Total usage**: 248KB 
- **Available**: 64MB (256x current usage)
- ✅ **Sufficient for systemd** (needs ~32KB based on Docker)  

## Standard Stream Configuration

**Current Setup**:
```bash
fd 0 -> /dev/null           ✅ Correct for systemd
fd 1 -> /dev/pts/0          ⚠️  Should be /dev/null for daemon mode
fd 2 -> /dev/pts/0          ⚠️  Should be /dev/null for daemon mode
```

**Expected for systemd**:
- All standard streams should redirect to `/dev/null` in daemon mode
- Console output handled via journald and logging subsystem

## Environmental Issues for systemd

### 1. **Cgroup Configuration** 🚨 **CRITICAL**
- ❌ Missing `nsdelegate` - systemd needs delegated cgroup control
- ❌ Missing `memory_recursiveprot` - systemd memory pressure handling  
- ❌ Flat cgroup hierarchy - systemd expects scoped structure

### 2. **Environment Variables** ⚠️ **IMPORTANT**
- ❌ Missing `HOSTNAME` - systemd uses for identification
- ❌ Missing `TERM` - affects console output formatting
- ❌ Missing `HOME` - systemd default working directory
- ⚠️ Non-standard PATH with `/command:` prefix

### 3. **Standard Stream Configuration** ⚠️ **MINOR**
- ⚠️ stdout/stderr → `/dev/pts/0` instead of `/dev/null`
- May affect daemon behavior vs interactive mode

### 4. **Filesystem Differences** ⚠️ **MINOR**
- ⚠️ Complex overlay filesystem may impact performance
- ⚠️ JuiceFS backend adds latency to /dev writes
- ⚠️ Read-only proc submounts may restrict systemd operations

## Root Cause Analysis

**Primary Issues**:
1. **Cgroup delegation missing** - systemd cannot manage child processes properly
2. **Environment variable gaps** - affects systemd initialization and operation

**Secondary Issues**:
3. **Standard stream redirection** - minor behavioral differences
4. **Filesystem complexity** - potential performance impact

## Required Configuration Changes

### **Priority 1: Cgroup Configuration** 
- ✅ **Add `nsdelegate`** to cgroup2 mount options
- ✅ **Add `memory_recursiveprot`** to cgroup2 mount options  
- **Current**: `cgroup2 (rw,nosuid,nodev,noexec,relatime)`
- **Required**: `cgroup2 (rw,nosuid,nodev,noexec,relatime,nsdelegate,memory_recursiveprot)`

### **Priority 2: Environment Variables**
- ✅ **Set `HOSTNAME`** (e.g., container ID or hostname)
- ✅ **Set `TERM=xterm`** for proper console handling
- ✅ **Set `HOME=/root`** for systemd working directory
- ⚠️ **Consider `container=docker`** for systemd container detection

### **Priority 3: Standard Streams** 
- ✅ **Redirect stdout/stderr to `/dev/null`** for daemon mode
- Keep stdin as `/dev/null` (already correct)

### **Priority 4: Runtime Optimization**
- ⚠️ Consider mounting `/run/systemd` as tmpfs if needed
- ⚠️ Ensure proper permissions on `/sys/fs/cgroup` hierarchy 