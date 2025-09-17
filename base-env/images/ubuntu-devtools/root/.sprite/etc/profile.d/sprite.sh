# Add /.sprite/bin to PATH if not already present
case ":$PATH:" in
  *":/.sprite/bin:"*) ;;
  *) export PATH="/.sprite/bin:$PATH" ;;
esac

export BROWSER="/usr/local/bin/sprite-browser"