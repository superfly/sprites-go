# Default zsh configuration for sprite
# This prevents the zsh-newuser-install prompt

# Enable command completion
autoload -Uz compinit && compinit

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

# Source sprite environment if available
[ -r /.sprite/etc/profile.d/sprite.sh ] && . /.sprite/etc/profile.d/sprite.sh
