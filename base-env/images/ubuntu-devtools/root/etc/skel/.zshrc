# Default zsh configuration for sprite
# This prevents the zsh-newuser-install prompt

# Enable command completion
autoload -Uz compinit && compinit

# Set terminal title to show current directory (just the path)
precmd() {
    print -Pn "\e]0;%~\a"
}

# Set terminal title to show running command (just the command)
preexec() {
    # Extract just the command, not the full line
    local cmd="${1[(wr)^(*=*|sudo|exec|ssh|-*)]}"
    print -Pn "\e]0;${cmd}\a"
}

# Set a simple but nice prompt with colors
PROMPT='%F{green}%n@%m%f:%F{blue}%~%f%# '

# Enable color output
export CLICOLOR=1

# Basic key bindings (emacs style)
bindkey -e

# History settings
HISTSIZE=1000
SAVEHIST=1000
HISTFILE=~/.zsh_history
setopt HIST_IGNORE_DUPS
setopt SHARE_HISTORY

# Basic aliases
alias ls='ls --color=auto'
alias ll='ls -la'
alias l='ls -l'
