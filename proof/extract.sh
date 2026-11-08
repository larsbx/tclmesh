#!/bin/sh
# Regenerates TclMeshProof/Core from kernel/core with Charon and Aeneas, and
# records the digest of the sources it was generated from.
#
# Pinned tools: proof/extraction-pins.env (Charon is the input locked by
# Aeneas' flake at AENEAS_REV, so `nix build github:AeneasVerif/aeneas/$AENEAS_REV#{aeneas,charon}`
# yields both).
#
# Usage: CHARON=/path/to/charon AENEAS=/path/to/aeneas proof/extract.sh [--check]
#   (default) overwrite TclMeshProof/Core and CORE_SOURCE.sha256
#   --check   regenerate into a scratch tree and fail if the committed
#             translation or digest differs from it (CI provenance check)
set -eu
: "${CHARON:?set CHARON to the charon binary}"
: "${AENEAS:?set AENEAS to the aeneas binary}"
mode=${1:-write}
case $mode in write|--check) ;; *) echo "usage: $0 [--check]" >&2; exit 2 ;; esac
root=$(cd "$(dirname "$0")/.." && pwd)
committed=$root/proof/TclMeshProof/Core
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

# The LLBC basename names the generated Lean module (core.llbc -> Core.lean).
(cd "$root/kernel/core" && "$CHARON" cargo --preset=aeneas --sysroot default --dest-file "$work/core.llbc")
mkdir -p "$work/TclMeshProof/Core"
"$AENEAS" -backend lean -loops-to-rec "$work/core.llbc" -dest "$work/TclMeshProof/Core"
# Templates for user-supplied externals are scaffolding, never committed.
find "$work/TclMeshProof/Core" -name '*_Template.lean' -delete
(cd "$root" && sha256sum kernel/core/Cargo.toml kernel/core/src/*.rs) > "$work/CORE_SOURCE.sha256"

if [ "$mode" = --check ]; then
  status=0
  diff -ru "$committed" "$work/TclMeshProof/Core" || status=1
  diff -u "$root/proof/CORE_SOURCE.sha256" "$work/CORE_SOURCE.sha256" || status=1
  if [ "$status" -ne 0 ]; then
    echo "proof/TclMeshProof/Core is not the pinned translation of kernel/core: run proof/extract.sh" >&2
  fi
  exit "$status"
fi
rm -rf "$committed"
cp -R "$work/TclMeshProof/Core" "$committed"
cp "$work/CORE_SOURCE.sha256" "$root/proof/CORE_SOURCE.sha256"
