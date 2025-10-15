# ~/.bashrc — minimal defaults for interactive shells

# If not running interactively, don't do anything
[[ $- != *i* ]] && return

# -----------------------------------------------------------------------------
# Prompt
# -----------------------------------------------------------------------------
# Colorful PS1 with git branch
parse_git_branch() {
  git branch --show-current 2>/dev/null
}

# Colors
RED="\[\033[0;31m\]"
GREEN="\[\033[0;32m\]"
YELLOW="\[\033[0;33m\]"
BLUE="\[\033[0;34m\]"
BOLD="\[\033[1m\]"
RESET="\[\033[0m\]"

PS1="${BOLD}${GREEN}\u${RESET}@${BLUE}\h${RESET}:${YELLOW}\w${RESET}\$([[ \$(parse_git_branch) ]] && echo \" (${BOLD}\$(parse_git_branch)${RESET})\")\$ "

# -----------------------------------------------------------------------------
# History
# -----------------------------------------------------------------------------
HISTCONTROL=ignoredups:erasedups
HISTSIZE=1000
HISTFILESIZE=10000
shopt -s histappend
PROMPT_COMMAND="history -a; history -n; $PROMPT_COMMAND"

# -----------------------------------------------------------------------------
# Environment tweaks
# -----------------------------------------------------------------------------
export EDITOR=vim
export PAGER=less
export LESS="-R"
export LS_COLORS=$LS_COLORS:'di=1;34:ln=36:so=35:pi=33:ex=32:bd=1;33:cd=1;33:su=37:sg=30:tw=30:ow=34'

# -----------------------------------------------------------------------------
# Bash options
# -----------------------------------------------------------------------------
shopt -s checkwinsize       # update LINES and COLUMNS after each command
shopt -s extglob            # extended pattern matching
shopt -s globstar           # recursive globbing (**)
shopt -s autocd             # cd by typing directory name
shopt -s cdspell            # auto-correct minor typos in cd
