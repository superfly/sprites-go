#!/bin/bash
# browser-wrapper.sh - Emits terminal escape sequence for browser open requests

# Logging function
log() {
    echo "$(date '+%Y-%m-%d %H:%M:%S') [PID:$$,PPID:$PPID] $*" >> /tmp/xdg-open.log
}

# Log script start with parent process info
PARENT_CMD=""
if [ -r "/proc/$PPID/cmdline" ]; then
    PARENT_CMD=$(tr '\0' ' ' < "/proc/$PPID/cmdline" 2>/dev/null | head -c 200)
fi

log "START: Args=($*) Parent=$PPID($PARENT_CMD)"

# Get the URL to open
URL=""
for arg in "$@"; do
    # Check if the argument looks like a URL
    if [[ "$arg" =~ ^https?:// ]] || [[ "$arg" =~ ^file:// ]] || [[ "$arg" =~ ^www\. ]]; then
        URL="$arg"
        log "FOUND_URL: $URL"
        break
    fi
done

# If no URL found, check if it's a help/version command
if [ -z "$URL" ]; then
    case "$1" in
        --help|-h|--version|-v)
            log "HELP_REQUEST: $1"
            echo "Sprite browser wrapper (redirects to local browser)"
            echo "Usage: $0 [URL]"
            exit 0
            ;;
    esac
    # Default to opening about:blank if no URL specified
    URL="about:blank"
    log "DEFAULT_URL: $URL"
fi

# Function to get parent PID from /proc/PID/stat
get_parent_pid() {
    local pid=$1
    if [ -r "/proc/$pid/stat" ]; then
        awk '{print $4}' "/proc/$pid/stat" 2>/dev/null
    fi
}

# Function to check if a process has a TTY
check_process_tty() {
    local pid=$1
    local tty_found=""
    
    # Check stdin (fd/0)
    if [ -L "/proc/$pid/fd/0" ]; then
        local stdin_target=$(readlink "/proc/$pid/fd/0" 2>/dev/null)
        if [[ "$stdin_target" =~ ^/dev/pts/ ]] || [[ "$stdin_target" =~ ^/dev/tty ]]; then
            tty_found="$stdin_target"
        fi
    fi
    
    # Check stdout (fd/1) if stdin didn't have TTY
    if [ -z "$tty_found" ] && [ -L "/proc/$pid/fd/1" ]; then
        local stdout_target=$(readlink "/proc/$pid/fd/1" 2>/dev/null)
        if [[ "$stdout_target" =~ ^/dev/pts/ ]] || [[ "$stdout_target" =~ ^/dev/tty ]]; then
            tty_found="$stdout_target"
        fi
    fi
    
    # Check stderr (fd/2) if neither stdin nor stdout had TTY
    if [ -z "$tty_found" ] && [ -L "/proc/$pid/fd/2" ]; then
        local stderr_target=$(readlink "/proc/$pid/fd/2" 2>/dev/null)
        if [[ "$stderr_target" =~ ^/dev/pts/ ]] || [[ "$stderr_target" =~ ^/dev/tty ]]; then
            tty_found="$stderr_target"
        fi
    fi
    
    echo "$tty_found"
}

# Walk up the process tree to find a TTY
FOUND_TTY=""
FOUND_PID=""
current_pid=$PPID

log "WALKING_PROCESS_TREE: Starting from PID $current_pid"

while [ -n "$current_pid" ] && [ "$current_pid" -gt 1 ]; do
    log "CHECKING_PID: $current_pid"
    
    # Check if this process has a TTY
    tty_result=$(check_process_tty "$current_pid")
    if [ -n "$tty_result" ]; then
        FOUND_TTY="$tty_result"
        FOUND_PID="$current_pid"
        log "FOUND_TTY: PID=$current_pid TTY=$FOUND_TTY"
        break
    fi
    
    # Get parent PID and continue up the tree
    parent_pid=$(get_parent_pid "$current_pid")
    if [ -z "$parent_pid" ] || [ "$parent_pid" = "$current_pid" ]; then
        log "PROCESS_TREE_END: No parent found for PID $current_pid"
        break
    fi
    
    current_pid="$parent_pid"
done

# Check TTY status and log the decision
TTY_STATUS=""
OUTPUT_TARGET=""

# Send escape sequence to found TTY if available and writable
if [ -n "$FOUND_TTY" ] && [ -w "$FOUND_TTY" ]; then
    TTY_STATUS="found_ancestor_tty"
    OUTPUT_TARGET="$FOUND_TTY (PID:$FOUND_PID)"
    printf '\033]9999;browser-open;%s\033\\' "$URL" > "$FOUND_TTY"
elif [ -t 0 ] && [ -w /dev/tty ]; then
    # Fallback: We have a TTY, write directly to it
    TTY_STATUS="fallback_stdin_tty_writable"
    OUTPUT_TARGET="/dev/tty"
    printf '\033]9999;browser-open;%s\033\\' "$URL" > /dev/tty
elif [ -t 1 ]; then
    # Fallback: stdout is a TTY, use it
    TTY_STATUS="fallback_stdout_tty"
    OUTPUT_TARGET="stdout"
    printf '\033]9999;browser-open;%s\033\\' "$URL"
elif [ -t 2 ]; then
    # Fallback: stderr is a TTY, use it
    TTY_STATUS="fallback_stderr_tty"
    OUTPUT_TARGET="stderr"
    printf '\033]9999;browser-open;%s\033\\' "$URL" >&2
else
    # No TTY available, write to stdout anyway (might not work)
    TTY_STATUS="no_tty_fallback"
    OUTPUT_TARGET="stdout_fallback"
    printf '\033]9999;browser-open;%s\033\\' "$URL"
fi

log "ESCAPE_SENT: URL=$URL TTY_STATUS=$TTY_STATUS OUTPUT=$OUTPUT_TARGET"

# Exit with success to match xdg-open behavior
log "EXIT: success"
exit 0 