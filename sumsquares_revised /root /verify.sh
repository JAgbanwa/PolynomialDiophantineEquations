#!/usr/bin/env bash
# Independently verify Solution.lean against Challenge.lean with
# leanprover/comparator.
#
# Trust required: the Lean kernel, Mathlib, Challenge.lean (the statements), and
# comparator itself.  The proof development in RequestProject/ does NOT need to
# be trusted: comparator rebuilds the compared declarations, checks that their
# statements agree with Challenge.lean character for character, and checks that
# their axiom closure is contained in the permitted set recorded in
# comparator.json.
set -euo pipefail

cd "$(dirname "$0")"

TOOLCHAIN_TAG=$(sed -e 's|^leanprover/lean4:||' lean-toolchain | tr -d '[:space:]')
WORK="${COMPARATOR_WORK:-$HOME/.cache/quadratic-forms-comparator}"
mkdir -p "$WORK"

# A tool need not be tagged for every Lean patch release; fall back to the .0
# tag of the same minor series.
resolve_tag() {
  local repo="$1" tag="$2"
  if git ls-remote --exit-code --tags "https://github.com/$repo" \
      "refs/tags/$tag" >/dev/null 2>&1; then
    printf '%s' "$tag"
  else
    printf '%s' "$tag" | sed -E 's/^(v[0-9]+\.[0-9]+)\.[0-9]+$/\1.0/'
  fi
}

if [ ! -d "$WORK/comparator" ]; then
  git clone --branch "$(resolve_tag leanprover/comparator "$TOOLCHAIN_TAG")" --depth 1 \
    https://github.com/leanprover/comparator "$WORK/comparator"
fi
if [ ! -d "$WORK/lean4export" ]; then
  git clone --branch "$(resolve_tag leanprover/lean4export "$TOOLCHAIN_TAG")" --depth 1 \
    https://github.com/leanprover/lean4export "$WORK/lean4export"
fi
(cd "$WORK/comparator" && lake build)
(cd "$WORK/lean4export" && lake build)

# landrun, the sandbox comparator runs the builds and exports in.  It is wrapped
# so that the dynamic loader paths its own -ldd resolution can miss (the ELF
# interpreter on Ubuntu, the Nix store on NixOS) are readable inside the
# sandbox; without execute permission on the interpreter every execve inside
# the sandbox fails with EACCES.
mkdir -p "$WORK/bin"
if [ ! -x "$WORK/landrun-bin" ]; then
  curl -sL -o "$WORK/landrun-bin" \
    https://github.com/Zouuup/landrun/releases/download/v0.1.14/landrun-linux-amd64
  chmod +x "$WORK/landrun-bin"
fi
EXTRA=""
for d in /lib64 /lib /usr/lib /nix/store; do
  [ -e "$d" ] && EXTRA="$EXTRA --rox $d"
done
printf '#!/usr/bin/env bash\nexec "%s/landrun-bin"%s "$@"\n' "$WORK" "$EXTRA" \
  > "$WORK/bin/landrun"
chmod +x "$WORK/bin/landrun"
export COMPARATOR_LANDRUN="$WORK/bin/landrun"

export PATH="$WORK/bin:$WORK/lean4export/.lake/build/bin:$PATH"

# Set COMPARATOR_SKIP_CACHE=1 to skip the Mathlib cache download, for instance
# when the dependencies have already been built locally.
if [ "${COMPARATOR_SKIP_CACHE:-0}" != "1" ]; then
  lake exe cache get
fi
lake build Challenge Solution
lake env "$WORK/comparator/.lake/build/bin/comparator" comparator.json
