export BROWSER="/usr/local/bin/sprite-browser"

# Copy default tool versions if user's .tool-versions doesn't exist
if [ ! -f "$HOME/.tool-versions" ] && [ -f "/etc/asdf-default-tool-versions" ]; then
    cp /etc/asdf-default-tool-versions "$HOME/.tool-versions"
fi