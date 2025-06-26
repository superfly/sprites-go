# Docker Systemd Environment Report

**Container ID**: `e466b12c6d8e`  
**Status**: ✅ **WORKING** - systemd successfully running as PID 1  
**Date**: 2025-06-26  

## Process Tree
```bash
USER         PID %CPU %MEM    VSZ   RSS TTY      STAT START   TIME COMMAND
root           1  0.0  0.0  21560 11392 ?        Ss   13:36   0:00 /lib/systemd/systemd --unit=basic.target
root          27  0.0  0.0  33732 11648 ?        S<s  13:36   0:00 /usr/lib/systemd/systemd-journald
systemd+      43  0.0  0.0  22568 13056 ?        Ss   13:36   0:00 /usr/lib/systemd/systemd-resolved
message+      80  0.0  0.0   8544  3968 ?        Ss   13:36   0:00 @dbus-daemon --system --address=systemd: --nofork --nopidfile --systemd-activation --syslog-only
```

## PID 1 Analysis

**Command Line**: `/lib/systemd/systemd --unit=basic.target`  
**Executable**: `/usr/lib/systemd/systemd`  
**Parent PID**: 0 (kernel - direct systemd execution)  

### Standard Streams
- **stdin (fd 0)**: `/dev/null`
- **stdout (fd 1)**: `/dev/null`  
- **stderr (fd 2)**: `/dev/null`

### Environment Variables
```bash
PATH=/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin
HOSTNAME=e466b12c6d8e
TERM=xterm
HOME=/root
```

## Console & TTY Setup

**Console Device**: `/dev/console`
```bash
crw--w---- 1 root tty 136, 0 Jun 26 13:36 /dev/console
```
- **Device Type**: Character device `136,0` (PTY)
- **Permissions**: `0620` (crw--w----)
- **Owner**: root:tty

## Cgroups Configuration

**Systemd Cgroup**: `0::/init.scope`

**Cgroup Mount**: 
```bash
cgroup on /sys/fs/cgroup type cgroup2 (rw,nosuid,nodev,noexec,relatime,nsdelegate,memory_recursiveprot)
```

**Available Controllers**:
- ✅ All standard cgroup2 controllers available
- ✅ Full read-write access to cgroup hierarchy
- ✅ `nsdelegate` and `memory_recursiveprot` enabled

## Critical Mounts

```bash
proc on /proc type proc (rw,nosuid,nodev,noexec,relatime)
tmpfs on /dev type tmpfs (rw,nosuid,size=65536k,mode=755,inode64)  
sysfs on /sys type sysfs (rw,nosuid,nodev,noexec,relatime)
cgroup on /sys/fs/cgroup type cgroup2 (rw,nosuid,nodev,noexec,relatime,nsdelegate,memory_recursiveprot)
tmpfs on /run type tmpfs (rw,nosuid,nodev,size=13142872k,nr_inodes=819200,mode=755,inode64)
tmpfs on /run/lock type tmpfs (rw,nosuid,nodev,noexec,relatime,size=5120k,inode64)
```

**Key Observations**:
- ✅ All critical filesystems mounted **read-write**
- ✅ `/run` has large tmpfs (13GB) for systemd operations
- ✅ `/sys/fs/cgroup` fully accessible
- ✅ Proper isolation with tmpfs overlays

## Runtime Directories

**`/run/` Structure**:
```bash
drwxr-xr-x 12 root root  300 Jun 26 13:36 .
drwxr-xr-x  2 root root   40 Jun 26 13:36 credentials
drwxr-xr-x  2 root root   60 Jun 26 13:36 dbus
prw-------  1 root root    0 Jun 26 13:36 initctl
drwxrwxrwt  3 root root   60 Jun 26 13:36 lock
drwxr-xr-x  3 root root   60 Jun 26 13:36 log
drwxr-xr-x 20 root root  560 Jun 26 13:36 systemd
```

**Key Features**:
- ✅ `/run/systemd/` directory exists (20 subdirectories)
- ✅ `/run/initctl` FIFO pipe for init communication
- ✅ Proper permissions and ownership

## Systemd Health

**Failed Units**: 0  
**Status**: All services running normally

## Systemd File Descriptors

Notable FDs for PID 1:
- **fd 7**: `/sys/fs/cgroup` (cgroup access)
- **fd 9**: `/usr/lib/systemd/systemd-executor`
- **fd 32**: `/sys/fs/cgroup/init.scope/memory.pressure`
- **fd 35**: `/proc/sys/fs/binfmt_misc` (autofs)
- **fd 36**: `/run/initctl`

## Success Factors

1. **Direct PID 1 execution** - No wrapper/init processes
2. **Proper cgroup2 setup** - Full controller access with delegation
3. **Read-write critical mounts** - systemd can modify system state
4. **Adequate tmpfs space** - 13GB `/run` for runtime data
5. **Console isolation** - `/dev/null` streams work fine for daemon mode
6. **Complete systemd runtime** - All necessary directories and files present 