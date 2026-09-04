#!/usr/bin/env bash
# Verify Solution.lean against Challenge.lean with the Lean comparator.
set -Eeuo pipefail
umask 077

readonly EXPECTED_TOOLCHAIN="leanprover/lean4:v4.28.0"

# These are the commits to which the v4.28.0 tags resolve.
readonly COMPARATOR_REV="7a0cae3df7a0200ff330c82420b8d88a51c9cac7"
readonly LEAN4EXPORT_REV="d065b0009aed0520e9e99752847a33b337661690"

readonly LANDRUN_VERSION="v0.1.14"
readonly LANDRUN_SHA256="645178e3239cd33760560834e50efea0864183a2a8a82faf199760dffee6dd71"

SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)"
cd "$SCRIPT_DIR"

for required_command in curl git install jq lake mktemp sha256sum uname; do
  if ! command -v "$required_command" >/dev/null 2>&1; then
    printf 'Required command is unavailable: %s\n' "$required_command" >&2
    exit 1
  fi
done

project_toolchain="$(tr -d '[:space:]' < lean-toolchain)"
if [[ "$project_toolchain" != "$EXPECTED_TOOLCHAIN" ]]; then
  printf 'Expected %s, but lean-toolchain contains %s\n' \
    "$EXPECTED_TOOLCHAIN" "$project_toolchain" >&2
  exit 1
fi

case "$(uname -m)" in
  x86_64 | amd64) ;;
  *)
    printf 'The pinned landrun artifact supports x86-64 only.\n' >&2
    exit 1
    ;;
esac

if [[ -n "${COMPARATOR_WORK:-}" ]]; then
  WORK="$COMPARATOR_WORK"
else
  : "${HOME:?HOME must be set when COMPARATOR_WORK is not provided}"
  WORK="${XDG_CACHE_HOME:-$HOME/.cache}/sumsquares-revised-verifier"
fi

readonly WORK
readonly COMPARATOR_DIR="$WORK/comparator"
readonly LEAN4EXPORT_DIR="$WORK/lean4export"
readonly BIN_DIR="$WORK/bin"
readonly LANDRUN_BIN="$WORK/landrun-linux-amd64"
readonly LANDRUN_WRAPPER="$BIN_DIR/landrun"

mkdir -p "$WORK" "$BIN_DIR"

checkout_pinned_revision() {
  local repository_url="$1"
  local revision="$2"
  local destination="$3"

  if [[ -e "$destination" && ! -d "$destination/.git" ]]; then
    printf '%s exists but is not a Git repository\n' "$destination" >&2
    exit 1
  fi

  if [[ ! -d "$destination/.git" ]]; then
    git init --quiet "$destination"
    git -C "$destination" remote add origin "$repository_url"
  else
    git -C "$destination" remote set-url origin "$repository_url"
  fi

  git -C "$destination" fetch --quiet --depth=1 --no-tags origin "$revision"
  git -C "$destination" checkout --quiet --detach FETCH_HEAD
  git -C "$destination" reset --quiet --hard "$revision"

  # Retain only the cached Lake build directory; remove other untracked files.
  git -C "$destination" clean -ffdx -e .lake/

  local actual_revision
  actual_revision="$(git -C "$destination" rev-parse HEAD)"
  if [[ "$actual_revision" != "$revision" ]]; then
    printf 'Revision verification failed for %s\n' "$repository_url" >&2
    exit 1
  fi

  if ! git -C "$destination" diff --quiet ||
      ! git -C "$destination" diff --cached --quiet; then
    printf 'The cached checkout is not clean: %s\n' "$destination" >&2
    exit 1
  fi
}

checkout_pinned_revision \
  "https://github.com/leanprover/comparator.git" \
  "$COMPARATOR_REV" \
  "$COMPARATOR_DIR"

checkout_pinned_revision \
  "https://github.com/leanprover/lean4export.git" \
  "$LEAN4EXPORT_REV" \
  "$LEAN4EXPORT_DIR"

(
  cd "$COMPARATOR_DIR"
  lake build comparator
)

(
  cd "$LEAN4EXPORT_DIR"
  lake build lean4export
)

landrun_is_valid() {
  [[ -f "$LANDRUN_BIN" && ! -L "$LANDRUN_BIN" ]] || return 1
  local actual_hash
  read -r actual_hash _ < <(sha256sum "$LANDRUN_BIN")
  [[ "$actual_hash" == "$LANDRUN_SHA256" ]]
}

if ! landrun_is_valid; then
  if [[ -L "$LANDRUN_BIN" ]]; then
    printf 'Refusing to overwrite a symbolic link: %s\n' "$LANDRUN_BIN" >&2
    exit 1
  fi

  download="$(mktemp "$WORK/.landrun-download.XXXXXX")"
  cleanup_download() {
    [[ -z "${download:-}" ]] || rm -f -- "$download"
  }
  trap cleanup_download EXIT

  curl \
    --proto '=https' \
    --tlsv1.2 \
    --fail \
    --location \
    --silent \
    --show-error \
    --retry 3 \
    --retry-all-errors \
    --output "$download" \
    "https://github.com/Zouuup/landrun/releases/download/${LANDRUN_VERSION}/landrun-linux-amd64"

  read -r downloaded_hash _ < <(sha256sum "$download")
  if [[ "$downloaded_hash" != "$LANDRUN_SHA256" ]]; then
    printf 'landrun checksum mismatch\n' >&2
    exit 1
  fi

  install -m 0755 "$download" "$LANDRUN_BIN"
  rm -f -- "$download"
  download=""
  trap - EXIT
fi

chmod 0755 "$LANDRUN_BIN"

# landrun's automatic ldd processing can miss the ELF interpreter or Nix store.
# Add their containing directories with read-and-execute permission.
cat > "$LANDRUN_WRAPPER" <<'WRAPPER'
#!/usr/bin/env bash
set -euo pipefail
: "${LANDRUN_REAL:?LANDRUN_REAL is not set}"

extra_paths=()
for directory in /lib64 /lib /usr/lib /usr/lib64 /nix/store; do
  [[ -e "$directory" ]] && extra_paths+=(--rox "$directory")
done

exec "$LANDRUN_REAL" "${extra_paths[@]}" "$@"
WRAPPER
chmod 0755 "$LANDRUN_WRAPPER"

readonly COMPARATOR_BIN="$COMPARATOR_DIR/.lake/build/bin/comparator"
readonly LEAN4EXPORT_BIN="$LEAN4EXPORT_DIR/.lake/build/bin/lean4export"

if [[ ! -x "$COMPARATOR_BIN" || ! -x "$LEAN4EXPORT_BIN" ]]; then
  printf 'A verifier executable was not built successfully.\n' >&2
  exit 1
fi

# Comparator v4.28.0 locates landrun and lean4export through PATH. The explicit
# variables also retain compatibility with comparator versions supporting them.
export LANDRUN_REAL="$LANDRUN_BIN"
export COMPARATOR_LANDRUN="$LANDRUN_WRAPPER"
export COMPARATOR_LEAN4EXPORT="$LEAN4EXPORT_BIN"
export PATH="$BIN_DIR:$LEAN4EXPORT_DIR/.lake/build/bin:$PATH"

# Guard against accidentally weakening comparator.json.
jq -e '
  .theorem_names as $names
  | .permitted_axioms as $axioms
  | (.challenge_module == "Challenge")
    and (.solution_module == "Solution")
    and (($names | type) == "array")
    and (($names | length) == 16)
    and (($names | unique | length) == 16)
    and (($axioms | sort) ==
         (["propext", "Quot.sound", "Classical.choice"] | sort))
    and (.enable_nanoda == false)
' comparator.json >/dev/null

# Fetching Mathlib's trusted cache before comparator enters the sandbox is
# permitted by comparator's threat model.
if [[ "${COMPARATOR_SKIP_CACHE:-0}" != "1" ]]; then
  lake exe cache get
fi

# Do not pre-build Challenge or Solution here. Comparator must perform both
# builds itself inside landrun.
lake env "$COMPARATOR_BIN" comparator.json
