# Default fish configuration for sprite


# Enable colors
set -g fish_color_normal normal
set -g fish_color_command green
set -g fish_color_param cyan
set -g fish_color_redirection normal
set -g fish_color_comment red
set -g fish_color_error red --bold
set -g fish_color_escape cyan
set -g fish_color_operator cyan
set -g fish_color_quote yellow
set -g fish_color_autosuggestion 555 yellow
set -g fish_color_valid_path --underline
set -g fish_color_cwd green
set -g fish_color_cwd_root red

# Simple prompt
function fish_prompt
    echo -n (whoami)'@'(hostname)':'(prompt_pwd)'$ '
end

# Note: Fish doesn't source bash scripts directly
# You would need bass or similar to source sprite.sh if needed
