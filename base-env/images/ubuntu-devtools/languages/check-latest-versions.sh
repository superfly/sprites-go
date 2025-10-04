#!/usr/bin/env bash
set -euo pipefail

print_kv() { printf "%-14s %s\n" "$1:" "${2:-unknown}"; }

curl_s() {
  curl -fsSL --connect-timeout 10 --max-time 20 "$@"
}

# Generic: resolve GitHub latest release tag via redirect
github_latest_tag() {
  local owner="$1" repo="$2"
  local final
  final=$(curl -sI -L -o /dev/null -w '%{url_effective}' "https://github.com/${owner}/${repo}/releases/latest" || true)
  # final like: https://github.com/owner/repo/releases/tag/v1.2.3
  printf '%s\n' "${final##*/}"
}

latest_go() {
  if command -v jq >/dev/null 2>&1; then
    curl_s 'https://go.dev/dl/?mode=json' | jq -r '[.[] | select(.stable==true)][0].version' | sed 's/^go//'
  else
    curl_s 'https://go.dev/dl/?mode=json' | tr '\n' ' ' | \
      grep -o '"version":"go[0-9.]*","stable":true' | head -1 | sed -E 's/.*go([0-9.]*).*/\1/'
  fi
}

latest_node_current() {
  if command -v jq >/dev/null 2>&1; then
    curl_s 'https://nodejs.org/dist/index.json' | jq -r '.[0].version' | sed 's/^v//'
  else
    curl_s 'https://nodejs.org/dist/index.tab' | awk 'NR==2 {gsub(/^v/, "", $1); print $1}'
  fi
}

latest_node_lts() {
  if command -v jq >/dev/null 2>&1; then
    curl_s 'https://nodejs.org/dist/index.json' | jq -r '[.[] | select(.lts!=false)][0].version' | sed 's/^v//'
  else
    # Fallback using index.tab (LTS name in last column). First line is header.
    curl_s 'https://nodejs.org/dist/index.tab' | awk 'NR>1 && $NF != "-" {gsub(/^v/, "", $1); print $1; exit}'
  fi
}

latest_ruby() {
  local v
  v=$(curl_s 'https://www.ruby-lang.org/en/downloads/' | grep -Eo 'The current stable version is [^<]+' | grep -Eo '[0-9]+\.[0-9]+\.[0-9]+' || true)
  if [ -z "${v}" ]; then
    v=$(curl_s 'https://raw.githubusercontent.com/rbenv/ruby-build/master/share/ruby-build' | \
        grep -E '^[0-9]+\.[0-9]+\.[0-9]+$' | tail -1 || true)
  fi
  printf '%s\n' "${v:-}"
}

latest_python3() {
  # Parse Python ftp listing (stable releases only)
  curl_s 'https://www.python.org/ftp/python/' | \
    grep -Eo '>3\.[0-9]+\.[0-9]+/' | sed -E 's/[^0-9.]+//g' | sort -V | tail -1
}

latest_rust() {
  # Extract version from rustc tarball URLs in stable channel TOML
  curl_s 'https://static.rust-lang.org/dist/channel-rust-stable.toml' | \
    grep -Eo 'rustc-[0-9]+\.[0-9]+\.[0-9]+' | head -1 | sed 's/rustc-//'
}

latest_erlang() {
  local tag
  tag=$(github_latest_tag erlang otp)
  printf '%s\n' "${tag#OTP-}"
}

latest_elixir() {
  local tag
  tag=$(github_latest_tag elixir-lang elixir)
  printf '%s\n' "${tag#v}"
}

latest_java_temurin_feature() {
  if command -v jq >/dev/null 2>&1; then
    curl_s 'https://api.adoptium.net/v3/info/available_releases' | jq -r '.most_recent_feature_release'
  else
    curl_s 'https://api.adoptium.net/v3/info/available_releases' | grep -Eo '"most_recent_feature_release"\s*:\s*[0-9]+' | head -1 | sed -E 's/.*: *([0-9]+)/\1/'
  fi
}

latest_java_temurin_lts() {
  if command -v jq >/dev/null 2>&1; then
    curl_s 'https://api.adoptium.net/v3/info/available_releases' | jq -r '.most_recent_lts'
  else
    curl_s 'https://api.adoptium.net/v3/info/available_releases' | grep -Eo '"most_recent_lts"\s*:\s*[0-9]+' | head -1 | sed -E 's/.*: *([0-9]+)/\1/'
  fi
}

latest_bun() {
  local tag
  tag=$(github_latest_tag oven-sh bun)
  tag=${tag#bun-}
  printf '%s\n' "${tag#v}"
}

latest_deno() {
  local tag
  tag=$(github_latest_tag denoland deno)
  printf '%s\n' "${tag#v}"
}

echo "Latest upstream releases (network required):"

tmpdir=$(mktemp -d)
cleanup() { rm -rf "$tmpdir"; }
trap cleanup EXIT

run_task() {
  local name="$1" func="$2" out="$tmpdir/$1"
  {
    set +e
    val="$($func 2>/dev/null || true)"
    printf '%s' "$val" > "$out"
  } &
}

run_task "Go"            latest_go
run_task "Node_current"  latest_node_current
run_task "Node_LTS"      latest_node_lts
run_task "Ruby"          latest_ruby
run_task "Python"        latest_python3
run_task "Rust"          latest_rust
run_task "Erlang_OTP"    latest_erlang
run_task "Elixir"        latest_elixir
run_task "Java_feat"     latest_java_temurin_feature
run_task "Java_LTS"      latest_java_temurin_lts
run_task "Bun"           latest_bun
run_task "Deno"          latest_deno

wait

read_out() { local f="$tmpdir/$1"; if [ -s "$f" ]; then cat "$f"; else echo "unknown"; fi; }

print_kv "Go"            "$(read_out Go)"
print_kv "Node (curr)"   "$(read_out Node_current)"
print_kv "Node (LTS)"    "$(read_out Node_LTS)"
print_kv "Ruby"          "$(read_out Ruby)"
print_kv "Python"        "$(read_out Python)"
print_kv "Rust"          "$(read_out Rust)"
print_kv "Erlang/OTP"    "$(read_out Erlang_OTP)"
print_kv "Elixir"        "$(read_out Elixir)"
print_kv "Java (feat)"   "$(read_out Java_feat)"
print_kv "Java (LTS)"    "$(read_out Java_LTS)"
print_kv "Bun"           "$(read_out Bun)"
print_kv "Deno"          "$(read_out Deno)"

exit 0


