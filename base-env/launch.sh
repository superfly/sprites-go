#!/bin/bash
set -euo pipefail

# Debug function
function debug() {
    if [[ "${APP_STORAGE_DEBUG:-false}" == "true" ]]; then
        echo "$@"
    fi
}

# Check if cgroup2 is mounted, if not mount it
if ! mountpoint -q /sys/fs/cgroup; then
    mkdir -p /sys/fs/cgroup
    mount -t cgroup2 none /sys/fs/cgroup
fi

# Define paths based on SPRITE_WRITE_DIR
JUICEFS_BASE="${SPRITE_WRITE_DIR}/juicefs"
JUICEFS_DATA="${JUICEFS_BASE}/data"
ROOT_OVERLAY_IMG="${JUICEFS_DATA}/active/root-overlay.img"
ROOT_OVERLAY_MOUNT="${JUICEFS_DATA}/root-overlay"


# This is a prerun script to do the overlay + loopback inside the namespace
# Only copy mounts.sh if /mnt/newroot isn't already an overlayfs
if ! mount | grep -q "^overlay on /mnt/newroot type overlay"; then
    # Create directories for overlay
  mkdir -p ${ROOT_OVERLAY_MOUNT}/{upper,work}

  mkdir -p /mnt/newroot

  # Mount the overlay
  mount -t overlay overlay \
    -o lowerdir=/mnt/app-image,upperdir=${ROOT_OVERLAY_MOUNT}/upper,workdir=${ROOT_OVERLAY_MOUNT}/work \
    /mnt/newroot
fi

# Store base config in a variable
CONFIG_JSON='{
  "ociVersion": "1.0.2",
  "process": {
    "user": {
      "uid": 0,
      "gid": 0
    },
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
        "hard": 1024,
        "soft": 1024
      }
    ],
    "noNewPrivileges": true
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
      "options": ["nosuid", "noexec", "nodev", "ro"]
    },
    {
      "destination": "/sys/fs/cgroup",
      "type": "cgroup2",
      "source": "cgroup2",
      "options": [
        "nosuid",
        "noexec",
        "nodev",
        "relatime",
        "ro"
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
        "destination": "/data",
        "type": "bind",
        "source": "/dev/fly_vol/juicefs/data/active/fs",
        "options": ["rbind"]
    },
    {
      "destination": "/.pilot/swapon",
      "source": "/.pilot/swapon",
      "options": ["rbind"]
    },
    {
      "destination": "/.pilot/tini",
      "source": "/.pilot/tini",
      "options": ["rbind"]
    },
    {
      "destination": "/etc/resolv.conf",
      "type": "bind",
      "source": "/etc/resolv.conf",
      "options": ["ro", "nosuid", "noexec", "nodev", "bind"]
    }
  ],
  "linux": {
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
      "/proc/bus",
      "/proc/fs",
      "/proc/irq",
      "/proc/sysrq-trigger"
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

# No additional mounts needed - the overlay provides the writable filesystem

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
IFS=':' read -r uid gid <<< "$user_info"

# Update the config with the user
CONFIG_JSON=$(echo "$CONFIG_JSON" | jq --argjson uid "$uid" --argjson gid "$gid" '.process.user = {"uid": $uid, "gid": $gid}')

# Prepare current environment variables, filtering APP_RUNNER_*, SPRITE_*, FLY_* and PATH
# Exclude variables that might interfere with jq processing if they contain newlines or quotes improperly
current_env_vars=$(env | grep -v '^APP_RUNNER_' | grep -v '^SPRITE_' | grep -v '^FLY_' | grep -v '^PATH=' | grep -v '^CONFIG_JSON=' | grep -v '^APP_IMAGE_CONFIG=' | grep -v '^_=' | grep -v '^PWD=')

# Convert current env and json env to objects, merge them (current overrides json), then back to array
# This jq command builds KEY:VALUE objects from both env sources, merges them,
# favouring the current env ($current_obj) over the JSON one ($json_obj),
# then converts back to ["KEY=VALUE", ...] format. Handles values containing '='.
merged_env_jq=$(jq -n \
    --argjson json_env "$json_env_jq" \
    --arg current_env "$current_env_vars" \
    'def to_object: map( index("=") as $i | {(.[0:$i]): .[$i+1:]} ) | add;
     ($json_env | to_object) as $json_obj |
     ($current_env | split("\n") | map(select(. != "")) | to_object) as $current_obj |
     ($json_obj + $current_obj) | to_entries | map("\( .key )=\( .value )")')

# Update the config with merged environment variables
CONFIG_JSON=$(echo "$CONFIG_JSON" | jq --argjson env_vars "$merged_env_jq" '.process.env = $env_vars')

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
echo "$CONFIG_JSON" > "${SPRITE_WRITE_DIR}/tmp/config.json"

crun run -f "${SPRITE_WRITE_DIR}/tmp/config.json" app &
pid=$!

# Trap SIGTERM and SIGINT to handle clean unmount
cleanup() {
  kill $pid 2>/dev/null
  umount /mnt/newroot
  umount /mnt/app-storage
  exit 0
}

trap cleanup SIGTERM SIGINT