# Default bash configuration for sprite

# Set terminal title to show current directory and running command
case "$TERM" in
xterm*|rxvt*|screen*)
    # Show current directory in title when idle (just the path)
    PROMPT_COMMAND='echo -ne "\033]0;${PWD/#$HOME/\~}\007"'
    
    # Show running command in title while executing (just the command)
    trap 'echo -ne "\033]0;${BASH_COMMAND}\007"' DEBUG
    ;;
*)
    ;;
esac

# Set a simple but nice prompt with colors
PS1='\[\033[01;32m\]\u@\h\[\033[00m\]:\[\033[01;34m\]\w\[\033[00m\]\$ '

# Enable color output
export CLICOLOR=1

# History settings
HISTSIZE=1000
HISTFILESIZE=2000
HISTCONTROL=ignoredups

# Basic aliases
alias ls='ls --color=auto'
alias ll='ls -la'
alias l='ls -l'
