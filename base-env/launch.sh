#!/bin/bash
set -euo pipefail

# Check required environment variables
if [ -z "${SPRITE_WRITE_DIR:-}" ]; then
    echo "Error: SPRITE_WRITE_DIR environment variable is not set" >&2
    exit 1
fi

# Debug function
function debug() {
    if [[ "${APP_STORAGE_DEBUG:-false}" == "true" ]]; then
        echo "$@"
    fi
}

# Cgroup setup is now handled by the server at startup

# Run host-side network setup (NAT only). Policy manager creates netns/veth/dns synchronously before process start.
/home/sprite/network-setup.sh

mkdir -p /dev/fly_vol/local-storage/var/lib/docker
mkdir -p /dev/fly_vol/local-storage/tmp
mkdir -p /dev/fly_vol/logs

mkdir -p /.sprite/tmp
mount -t tmpfs -o size=64M tmpfs /.sprite/tmp


# This is a prerun script to do the overlay + loopback inside the namespace
# Only copy mounts.sh if /mnt/newroot isn't already an overlayfs
if ! mount | grep -q "^overlay on /mnt/newroot type overlay"; then
  echo "Overlay is not mounted, skipping"
  exit 1
fi

# Store base config in a variable
CONFIG_JSON='{
  "ociVersion": "1.0.2",
  "process": {
    "user": {
      "uid": 0,
      "gid": 0
    },
    "terminal": false,
    "args": [],
    "cwd": "/",
    "env": [
      "PATH=/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin"
    ],
    "capabilities": {
      "bounding": [
        "CAP_CHOWN",
        "CAP_DAC_OVERRIDE",
        "CAP_FSETID",
        "CAP_FOWNER",
        "CAP_MKNOD",
        "CAP_NET_RAW",
        "CAP_SETGID",
        "CAP_SETUID",
        "CAP_SETFCAP",
        "CAP_SETPCAP",
        "CAP_NET_BIND_SERVICE",
        "CAP_SYS_CHROOT",
        "CAP_KILL",
        "CAP_AUDIT_WRITE",
        "CAP_SYS_ADMIN",
        "CAP_NET_ADMIN"
      ],
      "effective": [
        "CAP_CHOWN",
        "CAP_DAC_OVERRIDE",
        "CAP_FSETID",
        "CAP_FOWNER",
        "CAP_MKNOD",
        "CAP_NET_RAW",
        "CAP_SETGID",
        "CAP_SETUID",
        "CAP_SETFCAP",
        "CAP_SETPCAP",
        "CAP_NET_BIND_SERVICE",
        "CAP_SYS_CHROOT",
        "CAP_KILL",
        "CAP_AUDIT_WRITE",
        "CAP_SYS_ADMIN",
        "CAP_NET_ADMIN"
      ],
      "inheritable": [
        "CAP_CHOWN",
        "CAP_DAC_OVERRIDE",
        "CAP_FSETID",
        "CAP_FOWNER",
        "CAP_MKNOD",
        "CAP_NET_RAW",
        "CAP_SETGID",
        "CAP_SETUID",
        "CAP_SETFCAP",
        "CAP_SETPCAP",
        "CAP_NET_BIND_SERVICE",
        "CAP_SYS_CHROOT",
        "CAP_KILL",
        "CAP_AUDIT_WRITE",
        "CAP_SYS_ADMIN",
        "CAP_NET_ADMIN"
      ],
      "permitted": [
        "CAP_CHOWN",
        "CAP_DAC_OVERRIDE",
        "CAP_FSETID",
        "CAP_FOWNER",
        "CAP_MKNOD",
        "CAP_NET_RAW",
        "CAP_SETGID",
        "CAP_SETUID",
        "CAP_SETFCAP",
        "CAP_SETPCAP",
        "CAP_NET_BIND_SERVICE",
        "CAP_SYS_CHROOT",
        "CAP_KILL",
        "CAP_AUDIT_WRITE",
        "CAP_SYS_ADMIN",
        "CAP_NET_ADMIN"
      ],
      "ambient": [
        "CAP_CHOWN",
        "CAP_DAC_OVERRIDE",
        "CAP_FSETID",
        "CAP_FOWNER",
        "CAP_MKNOD",
        "CAP_NET_RAW",
        "CAP_SETGID",
        "CAP_SETUID",
        "CAP_SETFCAP",
        "CAP_SETPCAP",
        "CAP_NET_BIND_SERVICE",
        "CAP_SYS_CHROOT",
        "CAP_KILL",
        "CAP_AUDIT_WRITE",
        "CAP_SYS_ADMIN",
        "CAP_NET_ADMIN"
      ]
    },
    "rlimits": [
      {
        "type": "RLIMIT_NOFILE",
        "hard": 10240,
        "soft": 10240
      }
    ],
    "noNewPrivileges": false
  },
  "root": {
    "path": "/mnt/newroot",
    "readonly": false
  },
  "mounts": [
    {
      "destination": "/proc",
      "type": "proc",
      "source": "proc",
      "options": ["nosuid", "noexec", "nodev"]
    },
    {
      "destination": "/dev",
      "type": "tmpfs",
      "source": "tmpfs",
      "options": ["nosuid", "strictatime", "mode=755", "size=65536k"]
    },
    {
      "destination": "/dev/pts",
      "type": "devpts",
      "source": "devpts",
      "options": ["nosuid", "noexec", "newinstance", "ptmxmode=0666", "mode=0620", "gid=5"]
    },
    {
      "destination": "/dev/shm",
      "type": "tmpfs",
      "source": "shm",
      "options": ["nosuid", "noexec", "nodev", "mode=1777", "size=65536k"]
    },
    {
      "destination": "/dev/mqueue",
      "type": "mqueue",
      "source": "mqueue",
      "options": ["nosuid", "noexec", "nodev"]
    },
    {
      "destination": "/sys",
      "type": "sysfs",
      "source": "sysfs",
      "options": ["nosuid", "noexec", "nodev"]
    },
    {
      "destination": "/sys/fs/cgroup",
      "type": "cgroup2",
      "source": "cgroup2",
      "options": [
        "nosuid", "noexec", "nodev", "relatime",
        "nsdelegate", "memory_recursiveprot"
      ]
    },
    {
      "destination": "/run",
      "type": "tmpfs",
      "source": "tmpfs",
      "options": ["nosuid", "strictatime", "mode=755", "size=65536k"]
    },
    {
      "destination": "/mnt",
      "type": "tmpfs",
      "source": "tmpfs",
      "options": ["nosuid", "strictatime", "mode=755", "size=65536k"]
    },
    {
        "destination": "/tmp",
        "type": "tmpfs",
        "source": "tmpfs",
        "options": ["nosuid", "nodev", "mode=1777", "size=512M"]
    },
    {
        "destination": "/var/lib/docker",
        "type": "bind",
        "source": "/dev/fly_vol/local-storage/var/lib/docker",
        "options": ["rbind","nosuid", "nodev"]
    },
    {
      "destination": "/.pilot/tini",
      "source": "/.pilot/tini",
      "options": ["rbind"]
    },
    {
      "destination": "/etc/resolv.conf",
      "type": "bind",
      "source": "/system/etc/resolv.conf",
      "options": ["ro", "nosuid", "noexec", "nodev", "bind"]
    },
    {
      "destination": "/.sprite/tmp",
      "type": "bind",
      "source": "/.sprite/tmp",
      "options": ["rbind"]
    },
    {
      "destination": "/.sprite/api.sock",
      "type": "bind",
      "source": "/tmp/sprite.sock",
      "options": ["ro", "bind"]
    },
    {
      "destination": "/.sprite/checkpoints",
      "type": "bind",
      "source": "/.sprite/checkpoints",
      "options": ["rbind", "rslave"]
    },
    {
      "destination": "/.sprite/logs",
      "type": "bind",
      "source": "/dev/fly_vol/logs",
      "options": ["ro", "rbind"]
    }
  ],
  "linux": {
    "cgroupsPath": "/containers/sprite",
    "devices": [
      {
        "path": "/dev/fuse",
        "type": "c",
        "major": 10,
        "minor": 229,
        "fileMode": 0666,
        "uid": 0,
        "gid": 0
      },
      {
        "path": "/dev/net/tun",
        "type": "c",
        "major": 10,
        "minor": 200,
        "fileMode": 0666,
        "uid": 0,
        "gid": 0
      },
      {
        "path": "/dev/loop-control",
        "type": "c",
        "major": 10,
        "minor": 237,
        "fileMode": 0666,
        "uid": 0,
        "gid": 0
      },
      {
        "path": "/dev/loop0",
        "type": "b",
        "major": 7,
        "minor": 0,
        "fileMode": 0666,
        "uid": 0,
        "gid": 0
      },
      {
        "path": "/dev/loop1",
        "type": "b",
        "major": 7,
        "minor": 1,
        "fileMode": 0666,
        "uid": 0,
        "gid": 0
      },
      {
        "path": "/dev/loop2",
        "type": "b",
        "major": 7,
        "minor": 2,
        "fileMode": 0666,
        "uid": 0,
        "gid": 0
      },
      {
        "path": "/dev/loop3",
        "type": "b",
        "major": 7,
        "minor": 3,
        "fileMode": 0666,
        "uid": 0,
        "gid": 0
      },
      {
        "path": "/dev/loop4",
        "type": "b",
        "major": 7,
        "minor": 4,
        "fileMode": 0666,
        "uid": 0,
        "gid": 0
      },
      {
        "path": "/dev/loop5",
        "type": "b",
        "major": 7,
        "minor": 5,
        "fileMode": 0666,
        "uid": 0,
        "gid": 0
      },
      {
        "path": "/dev/loop6",
        "type": "b",
        "major": 7,
        "minor": 6,
        "fileMode": 0666,
        "uid": 0,
        "gid": 0
      },
      {
        "path": "/dev/loop7",
        "type": "b",
        "major": 7,
        "minor": 7,
        "fileMode": 0666,
        "uid": 0,
        "gid": 0
      }
    ],
    "namespaces": [
      {
        "type": "pid"
      },
      {
        "type": "ipc"
      },
      {
        "type": "uts"
      },
      {
        "type": "mount"
      },
      {
        "type": "cgroup"
      },
      {
        "type": "network",
        "path": "/run/netns/sprite"
      }
    ],
    "maskedPaths": [
      "/proc/acpi",
      "/proc/asound",
      "/proc/kcore",
      "/proc/keys",
      "/proc/latency_stats",
      "/proc/timer_list",
      "/proc/timer_stats",
      "/proc/sched_debug",
      "/sys/firmware",
      "/proc/scsi"
    ],
    "readonlyPaths": [
    ]
  }
}'

# Read app image config if it exists
APP_IMAGE_CONFIG_PATH="/etc/app-image.json"
if [ -f "$APP_IMAGE_CONFIG_PATH" ]; then
    debug "Using configuration from $APP_IMAGE_CONFIG_PATH"
    # Print file size
    config_size=$(stat -c %s "$APP_IMAGE_CONFIG_PATH")
    debug "Size of $APP_IMAGE_CONFIG_PATH: $config_size bytes"
    APP_IMAGE_CONFIG=$(cat "$APP_IMAGE_CONFIG_PATH")
else
    debug "Warning: $APP_IMAGE_CONFIG_PATH not found."
    APP_IMAGE_CONFIG='{}'
fi

# Extract config elements, providing defaults
# Try uppercase Config first, then lowercase config
json_entrypoint_jq=$(echo "$APP_IMAGE_CONFIG" | jq '.Config.Entrypoint // .config.Entrypoint // [] | map(select(. != ""))')
debug "Raw Entrypoint from JSON:"
debug "$json_entrypoint_jq" | jq .
json_cmd_jq=$(echo "$APP_IMAGE_CONFIG" | jq '.Config.Cmd // .config.Cmd // [] | map(select(. != ""))')
debug "Raw Cmd from JSON:"
debug "$json_cmd_jq" | jq .
# Filter APP_RUNNER_*, SPRITE_*, and FLY_* vars from JSON env
json_env_jq=$(echo "$APP_IMAGE_CONFIG" | jq '.Config.Env // .config.Env // [] | map(select(startswith("APP_RUNNER_") or startswith("SPRITE_") or startswith("FLY_") | not))')

# Determine final entrypoint and command
# Check if the variable is SET (even if empty) using +x parameter expansion
if [ -n "${APP_RUNNER_ENTRYPOINT+x}" ]; then
    # Use environment variable, splitting by space
    # If APP_RUNNER_ENTRYPOINT is empty, entrypoint_args will be empty array
    read -r -a entrypoint_args <<< "$APP_RUNNER_ENTRYPOINT"
    # Filter out empty strings from entrypoint_args
    filtered_entrypoint_args=()
    for arg in "${entrypoint_args[@]}"; do
        if [ -n "$arg" ]; then
            filtered_entrypoint_args+=("$arg")
        fi
    done
    # Convert filtered bash array to JSON array using printf and jq -R/-s (compatible with older jq)
    entrypoint_jq=$(printf '%s\n' "${filtered_entrypoint_args[@]}" | jq -R . | jq -s .)
else
    # Variable is UNSET, use JSON value
    entrypoint_jq=$json_entrypoint_jq
fi

# Check if the variable is SET (even if empty) using +x parameter expansion
if [ -n "${APP_RUNNER_CMD+x}" ]; then
    # Use environment variable, splitting by space
    # If APP_RUNNER_CMD is empty, cmd_args will be empty array
    read -r -a cmd_args <<< "$APP_RUNNER_CMD"
    # Filter out empty strings from cmd_args
    filtered_cmd_args=()
    for arg in "${cmd_args[@]}"; do
        if [ -n "$arg" ]; then
            filtered_cmd_args+=("$arg")
        fi
    done
    # Convert filtered bash array to JSON array using printf and jq -R/-s (compatible with older jq)
    cmd_jq=$(printf '%s\n' "${filtered_cmd_args[@]}" | jq -R . | jq -s .)
else
    # Variable is UNSET, use JSON value
    cmd_jq=$json_cmd_jq
fi

# Combine entrypoint and cmd for final args
combined_args_jq=$(jq -n --argjson entrypoint "$entrypoint_jq" --argjson cmd "$cmd_jq" '$entrypoint + $cmd | map(select(. != ""))')

# Prepend tini to the arguments
# final_args_jq=$(jq -n --argjson combined_args "$combined_args_jq" '[ "/.pilot/tini", "--" ] + $combined_args')

# debug "Final arguments for tini:"
# debug "$final_args_jq" | jq .

# Update the config with final args
CONFIG_JSON=$(echo "$CONFIG_JSON" | jq --argjson new_args "$combined_args_jq" '.process.args = $new_args')

# Extract WorkingDir from config, providing a default
working_dir=$(echo "$APP_IMAGE_CONFIG" | jq -r '.Config.WorkingDir // .config.WorkingDir // "/"')

# Update the config with the working directory
CONFIG_JSON=$(echo "$CONFIG_JSON" | jq --arg dir "$working_dir" '.process.cwd = $dir')

# Extract User from config, providing defaults
user_info=$(echo "$APP_IMAGE_CONFIG" | jq -r '.Config.User // .config.User // "0:0"')

# Parse UID and GID from user_info
if [[ "$user_info" == *":"* ]]; then
    # user_info is in "uid:gid" format
    IFS=':' read -r uid gid <<< "$user_info"
else
    # user_info is just a username, look it up in /mnt/system-base/etc/passwd
    if [[ -f "/mnt/system-base/etc/passwd" ]]; then
        passwd_entry=$(grep "^${user_info}:" /mnt/system-base/etc/passwd || true)
        if [[ -n "$passwd_entry" ]]; then
            # Extract uid and gid from passwd entry format: username:x:uid:gid:...
            uid=$(echo "$passwd_entry" | cut -d':' -f3)
            gid=$(echo "$passwd_entry" | cut -d':' -f4)
        else
            # User not found in passwd, use defaults
            uid=0
            gid=0
        fi
    else
        # passwd file not found, use defaults
        uid=0
        gid=0
    fi
fi

# Update the config with the user
CONFIG_JSON=$(echo "$CONFIG_JSON" | jq --argjson uid "$uid" --argjson gid "$gid" '.process.user = {"uid": $uid, "gid": $gid}')

# Use only the environment variables from the config file (json_env_jq)
# Don't merge in current environment - keep container environment clean and explicit
CONFIG_JSON=$(echo "$CONFIG_JSON" | jq --argjson env_vars "$json_env_jq" '.process.env = $env_vars')

# If PATH_APP is set, ensure it overrides PATH in the merged env
# Note: This comes *after* merging to ensure PATH_APP takes ultimate precedence
if [ -n "${PATH_APP:-}" ]; then
    # Add PATH if it doesn't exist, otherwise update it.
    CONFIG_JSON=$(echo "$CONFIG_JSON" | jq --arg path "$PATH_APP" '
        .process.env = ([.process.env[] | select(startswith("PATH=") | not)] + ["PATH=" + $path])
    ')
fi

# Write the final config to file
mkdir -p "${SPRITE_WRITE_DIR}/tmp"

# Generate template process.json mirroring env and cwd from the OCI config
PROCESS_JSON=$(echo "$CONFIG_JSON" | jq '{terminal:false,args:[],env:.process.env,cwd:.process.cwd}')
echo "$PROCESS_JSON" > "${SPRITE_WRITE_DIR}/tmp/process.json"

echo "$CONFIG_JSON" > "${SPRITE_WRITE_DIR}/tmp/config.json"

if [ -n "${CONSOLE_SOCKET:-}" ]; then
    if [ -n "${CRUN_PID_FILE:-}" ]; then
        exec crun run --pid-file="${CRUN_PID_FILE}" --console-socket="${CONSOLE_SOCKET}" -f "${SPRITE_WRITE_DIR}/tmp/config.json" app
    else
        exec crun run --console-socket="${CONSOLE_SOCKET}" -f "${SPRITE_WRITE_DIR}/tmp/config.json" app
    fi
else
    if [ -n "${CRUN_PID_FILE:-}" ]; then
        exec crun run --pid-file="${CRUN_PID_FILE}" -f "${SPRITE_WRITE_DIR}/tmp/config.json" app
    else
        exec crun run -f "${SPRITE_WRITE_DIR}/tmp/config.json" app
    fi
fi