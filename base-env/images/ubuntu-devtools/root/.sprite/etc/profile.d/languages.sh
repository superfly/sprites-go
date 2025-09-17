#!/bin/bash
# PATH setup for language-specific binaries and global packages

# Add all common language binary directories to PATH
export PATH="$HOME/.local/bin:$HOME/.cargo/bin:$HOME/go/bin:$HOME/.bun/bin:$HOME/.deno/bin:$HOME/.composer/vendor/bin:$HOME/.config/composer/vendor/bin:$PATH"

# Add npm global bin directory to PATH dynamically (needs command substitution)
if command -v npm >/dev/null 2>&1; then
    NPM_GLOBAL_BIN="$(npm bin -g 2>/dev/null)"
    [ -n "$NPM_GLOBAL_BIN" ] && export PATH="$NPM_GLOBAL_BIN:$PATH"
fi

# Add Ruby gem paths dynamically (needs command substitution)
if command -v gem >/dev/null 2>&1; then
    GEM_BIN_PATH="$(gem environment gemdir 2>/dev/null)/bin"
    [ -n "$GEM_BIN_PATH" ] && export PATH="$GEM_BIN_PATH:$PATH"
fi

if command -v ruby >/dev/null 2>&1; then
    GEM_USER_BIN="$(ruby -r rubygems -e 'puts Gem.user_dir' 2>/dev/null)/bin"
    [ -n "$GEM_USER_BIN" ] && export PATH="$GEM_USER_BIN:$PATH"
fi
