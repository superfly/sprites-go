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

# Detect ports the parent process is listening on
LISTENING_PORTS=""
if command -v ss >/dev/null 2>&1; then
    # Use ss (modern netstat replacement) to find listening ports for parent PID
    PORTS=$(ss -tlnp 2>/dev/null | grep "pid=$PPID," | sed -n 's/.*:\([0-9]*\).* pid=.*/\1/p' | sort -n | uniq | tr '\n' ',' | sed 's/,$//')
    if [ -n "$PORTS" ]; then
        LISTENING_PORTS="$PORTS"
    fi
elif command -v netstat >/dev/null 2>&1; then
    # Fallback to netstat if ss not available
    PORTS=$(netstat -tlnp 2>/dev/null | grep "$PPID/" | sed -n 's/.*:\([0-9]*\).*/\1/p' | sort -n | uniq | tr '\n' ',' | sed 's/,$//')
    if [ -n "$PORTS" ]; then
        LISTENING_PORTS="$PORTS"
    fi
fi

log "START: Args=($*) Parent=$PPID($PARENT_CMD) Listening_Ports=($LISTENING_PORTS)"

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

# Check TTY status and log the decision
TTY_STATUS=""
OUTPUT_TARGET=""

# Check parent process's file descriptors for TTY
PARENT_TTY=""
if [ -L "/proc/$PPID/fd/0" ]; then
    PARENT_STDIN=$(readlink "/proc/$PPID/fd/0" 2>/dev/null)
    if [[ "$PARENT_STDIN" =~ ^/dev/pts/ ]] || [[ "$PARENT_STDIN" =~ ^/dev/tty ]]; then
        PARENT_TTY="$PARENT_STDIN"
        TTY_STATUS="parent_stdin_tty"
        OUTPUT_TARGET="$PARENT_TTY"
    fi
fi

if [ -z "$PARENT_TTY" ] && [ -L "/proc/$PPID/fd/1" ]; then
    PARENT_STDOUT=$(readlink "/proc/$PPID/fd/1" 2>/dev/null)
    if [[ "$PARENT_STDOUT" =~ ^/dev/pts/ ]] || [[ "$PARENT_STDOUT" =~ ^/dev/tty ]]; then
        PARENT_TTY="$PARENT_STDOUT"
        TTY_STATUS="parent_stdout_tty"
        OUTPUT_TARGET="$PARENT_TTY"
    fi
fi

if [ -z "$PARENT_TTY" ] && [ -L "/proc/$PPID/fd/2" ]; then
    PARENT_STDERR=$(readlink "/proc/$PPID/fd/2" 2>/dev/null)
    if [[ "$PARENT_STDERR" =~ ^/dev/pts/ ]] || [[ "$PARENT_STDERR" =~ ^/dev/tty ]]; then
        PARENT_TTY="$PARENT_STDERR"
        TTY_STATUS="parent_stderr_tty"
        OUTPUT_TARGET="$PARENT_TTY"
    fi
fi

# Send escape sequence to parent's TTY if found, otherwise fallback to our own TTY
if [ -n "$PARENT_TTY" ] && [ -w "$PARENT_TTY" ]; then
    printf '\033]9999;browser-open;%s;%s\033\\' "$URL" "$LISTENING_PORTS" > "$PARENT_TTY"
elif [ -t 0 ] && [ -w /dev/tty ]; then
    # Fallback: We have a TTY, write directly to it
    TTY_STATUS="fallback_stdin_tty_writable"
    OUTPUT_TARGET="/dev/tty"
    printf '\033]9999;browser-open;%s;%s\033\\' "$URL" "$LISTENING_PORTS" > /dev/tty
elif [ -t 1 ]; then
    # Fallback: stdout is a TTY, use it
    TTY_STATUS="fallback_stdout_tty"
    OUTPUT_TARGET="stdout"
    printf '\033]9999;browser-open;%s;%s\033\\' "$URL" "$LISTENING_PORTS"
elif [ -t 2 ]; then
    # Fallback: stderr is a TTY, use it
    TTY_STATUS="fallback_stderr_tty"
    OUTPUT_TARGET="stderr"
    printf '\033]9999;browser-open;%s;%s\033\\' "$URL" "$LISTENING_PORTS" >&2
else
    # No TTY available, write to stdout anyway (might not work)
    TTY_STATUS="no_tty_fallback"
    OUTPUT_TARGET="stdout_fallback"
    printf '\033]9999;browser-open;%s;%s\033\\' "$URL" "$LISTENING_PORTS"
fi

log "ESCAPE_SENT: URL=$URL TTY_STATUS=$TTY_STATUS OUTPUT=$OUTPUT_TARGET LISTENING_PORTS=($LISTENING_PORTS)"

# Exit with success to match xdg-open behavior
log "EXIT: success"
exit 0 