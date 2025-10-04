#!/bin/bash

echo "Testing installed languages in sprite-languages-split image..."
echo "=================================================="

docker run --rm --entrypoint "" sprite-languages-split bash -lc '
echo "Testing as root (non-interactive)..."
echo ""

# Test each language
echo "Node.js:"
which node && node --version || echo "  Not found"
echo ""

echo "Python:"
which python3 && python3 --version || echo "  Not found"
echo ""

echo "Ruby:"
if which ruby >/dev/null 2>&1; then
  ruby --version || true
  echo "RubyGems:" && (which gem && gem --version) || true
  echo "Bundler:" && (which bundle && bundle --version) || true
  echo "rbenv:" && (which rbenv && rbenv --version) || true
  echo "Ruby quick script:"
  ruby -e "require 'json'; puts JSON.generate({ok: true})" || echo "  Ruby JSON failed"
else
  echo "  Not found"
fi
echo ""

echo "Go:"
which go && go version || echo "  Not found"
echo ""

echo "Rust:"
which rustc && rustc --version || echo "  Not found"
echo ""

echo "Elixir:"
which elixir && elixir --version || echo "  Not found"
echo ""

echo "Java:"
which java && java -version 2>&1 | head -1 || echo "  Not found"
echo ""

echo "Java compile/run:"
cat > /tmp/Hello.java << 'JAVAEOF'
public class Hello { public static void main(String[] args) { System.out.println("ok"); } }
JAVAEOF
javac /tmp/Hello.java && java -cp /tmp Hello || echo "  Compile/run failed"
rm -f /tmp/Hello.java /tmp/Hello.class
echo ""

echo "Bun:"
which bun && bun --version || echo "  Not found"
echo ""

echo "Deno:"
which deno && deno --version || echo "  Not found"
echo ""

echo "=================================================="
echo "Environment PATH:"
echo "$PATH"
'

