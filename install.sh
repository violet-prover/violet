#!/bin/sh
# Violet installer. POSIX sh — no bashisms.
# Usage: curl -fsSL https://violet-lang.org/install.sh | sh
#
# Env vars:
#   VIOLET_VERSION         pin a release tag (e.g. v0.2.0); default: latest
#   VIOLET_PREFIX          install root; default: $HOME/.violet
#   VIOLET_NO_MODIFY_PATH  if set, skip rc-file editing
set -eu

GITHUB_REPO="violet-prover/violet"
PREFIX="${VIOLET_PREFIX:-$HOME/.violet}"

# Print "curl" or "wget" based on what's available. Used by resolve_version
# and download. Exits 1 if neither is installed.
fetcher() {
  if command -v curl >/dev/null 2>&1; then
    printf 'curl\n'
  elif command -v wget >/dev/null 2>&1; then
    printf 'wget\n'
  else
    printf 'error: neither curl nor wget is installed\n' >&2
    return 1
  fi
}

# Print a URL's body to stdout. Honors HTTP errors.
http_get() {
  url="$1"
  tool=$(fetcher) || return 1
  case "$tool" in
    curl) curl -fsSL "$url" ;;
    wget) wget -qO- "$url" ;;
  esac
}

detect_platform() {
  os=$(uname -s)
  arch=$(uname -m)
  case "$os/$arch" in
    Linux/x86_64|Linux/amd64)    printf 'violet-linux-x86_64\n' ;;
    Linux/aarch64|Linux/arm64)   printf 'violet-linux-aarch64\n' ;;
    Darwin/arm64)                printf 'violet-macos-arm64\n' ;;
    *)
      printf 'error: unsupported platform: %s/%s\n' "$os" "$arch" >&2
      printf 'see https://github.com/%s/releases for available builds\n' "$GITHUB_REPO" >&2
      return 1
      ;;
  esac
}

resolve_version() {
  if [ -n "${VIOLET_VERSION:-}" ]; then
    printf '%s\n' "$VIOLET_VERSION"
    return 0
  fi
  api_url="https://api.github.com/repos/$GITHUB_REPO/releases/latest"
  body=$(http_get "$api_url") || {
    printf 'error: could not fetch latest release from GitHub API\n' >&2
    printf 'retry, or pin a version: VIOLET_VERSION=vX.Y.Z\n' >&2
    return 1
  }
  # Pull "tag_name":"vX.Y.Z" from the JSON. POSIX sed/grep — no jq.
  tag=$(printf '%s' "$body" | sed -n 's/.*"tag_name"[[:space:]]*:[[:space:]]*"\([^"]*\)".*/\1/p' | head -n1)
  if [ -z "$tag" ]; then
    printf 'error: could not parse tag_name from GitHub API response\n' >&2
    return 1
  fi
  printf '%s\n' "$tag"
}

# download <tag> <asset_name> <dest_dir>
# Downloads $asset_name and $asset_name.sha256 from the release tagged $tag
# into $dest_dir.
download() {
  tag="$1"; asset="$2"; dest="$3"
  base="https://github.com/$GITHUB_REPO/releases/download/$tag"
  tool=$(fetcher) || return 1
  for name in "$asset" "$asset.sha256"; do
    url="$base/$name"
    out="$dest/$name"
    case "$tool" in
      curl) curl -fsSL -o "$out" "$url" ;;
      wget) wget -qO "$out" "$url" ;;
    esac || {
      printf 'error: download failed: %s\n' "$url" >&2
      return 1
    }
  done
}

# verify <asset_path> <sha256_path>
# Recomputes sha256 of $asset_path and compares with the hex in $sha256_path.
# The .sha256 file is in `sha256sum` format: "<hex>  <filename>".
verify() {
  asset="$1"; sumfile="$2"
  expected=$(awk '{print $1}' "$sumfile")
  if command -v sha256sum >/dev/null 2>&1; then
    actual=$(sha256sum "$asset" | awk '{print $1}')
  elif command -v shasum >/dev/null 2>&1; then
    actual=$(shasum -a 256 "$asset" | awk '{print $1}')
  else
    printf 'error: neither sha256sum nor shasum is available\n' >&2
    return 1
  fi
  if [ "$expected" != "$actual" ]; then
    printf 'error: checksum mismatch\n  expected: %s\n  actual:   %s\n' "$expected" "$actual" >&2
    return 1
  fi
}

# install_binary <src> <tag>
# Moves $src to $PREFIX/bin/violet, making it executable. Logs old-vs-new
# version if an existing binary supports --version. Reads VIOLET_PREFIX
# dynamically so tests can set a fake prefix per case (unlike the
# script-load-time `$PREFIX`, which is frozen when install.sh is sourced).
install_binary() {
  src="$1"; tag="$2"
  prefix="${VIOLET_PREFIX:-$HOME/.violet}"
  dest_dir="$prefix/bin"
  dest="$dest_dir/violet"
  mkdir -p "$dest_dir"
  if [ -x "$dest" ]; then
    old=$("$dest" --version 2>/dev/null || printf 'unknown')
    printf 'replacing existing install: %s -> %s\n' "$old" "$tag"
  fi
  chmod +x "$src"
  mv "$src" "$dest"
}

# Print the snippet to inject into shell rc files. Uses $PREFIX so a custom
# VIOLET_PREFIX is respected.
path_snippet_posix() {
  cat <<EOF
# >>> violet path >>>
export PATH="$PREFIX/bin:\$PATH"
# <<< violet path <<<
EOF
}

path_snippet_fish() {
  cat <<EOF
# >>> violet path >>>
fish_add_path "$PREFIX/bin"
# <<< violet path <<<
EOF
}

# Append $1 (snippet) to $2 (rc file) if the marker isn't already present.
# Returns 0 if appended or already present; returns 1 if the write fails.
append_if_missing() {
  snippet="$1"; rc="$2"
  if [ -f "$rc" ] && grep -q '>>> violet path >>>' "$rc" 2>/dev/null; then
    return 0
  fi
  mkdir -p "$(dirname "$rc")" 2>/dev/null || true
  if printf '\n%s\n' "$snippet" >> "$rc" 2>/dev/null; then
    return 0
  fi
  return 1
}

wire_path() {
  if [ -n "${VIOLET_NO_MODIFY_PATH:-}" ]; then
    return 0
  fi
  shell_name="${SHELL##*/}"
  case "$shell_name" in
    zsh)
      rc="$HOME/.zshrc"
      snippet=$(path_snippet_posix)
      ;;
    bash)
      if [ "$(uname -s)" = "Darwin" ]; then
        rc="$HOME/.bash_profile"
      else
        rc="$HOME/.bashrc"
      fi
      snippet=$(path_snippet_posix)
      ;;
    fish)
      rc="$HOME/.config/fish/config.fish"
      snippet=$(path_snippet_fish)
      ;;
    *)
      printf 'unknown shell (%s) — add this line to your shell rc manually:\n' "$shell_name"
      path_snippet_posix
      return 0
      ;;
  esac
  if append_if_missing "$snippet" "$rc"; then
    printf 'updated %s\n' "$rc"
  else
    printf 'could not write %s — add this line manually:\n' "$rc"
    printf '%s\n' "$snippet"
  fi
}

report() {
  tag="$1"; rc_modified="$2"
  prefix="${VIOLET_PREFIX:-$HOME/.violet}"
  printf '\n'
  printf 'installed violet %s\n' "$tag"
  printf 'location:  %s/bin/violet\n' "$prefix"
  if [ "$rc_modified" = "1" ]; then
    printf 'PATH:      added to your shell rc\n'
    printf 'next:      open a new shell, or run `source` on the rc file shown above\n'
  else
    printf 'PATH:      unchanged (set VIOLET_NO_MODIFY_PATH or shell unknown)\n'
  fi
}

main() {
  main_asset=$(detect_platform)       # exits non-zero on unsupported platform
  main_tag=$(resolve_version)         # exits non-zero on API failure
  printf 'installing violet %s for %s\n' "$main_tag" "$main_asset"

  # Put the temp dir inside $PREFIX so the final `mv` stays on one filesystem
  # and is truly atomic. $TMPDIR is the POSIX way to redirect `mktemp -d`.
  mkdir -p "$PREFIX"
  main_tmp=$(TMPDIR="$PREFIX" mktemp -d)
  trap 'rm -rf "$main_tmp"' EXIT INT TERM HUP

  download "$main_tag" "$main_asset" "$main_tmp"
  verify "$main_tmp/$main_asset" "$main_tmp/$main_asset.sha256"
  install_binary "$main_tmp/$main_asset" "$main_tag"

  if [ -z "${VIOLET_NO_MODIFY_PATH:-}" ]; then
    wire_path
    main_rc_modified=1
  else
    main_rc_modified=0
  fi
  report "$main_tag" "$main_rc_modified"
}

main "$@"
