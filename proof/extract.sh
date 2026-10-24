#!/bin/sh
# Regenerates TclMeshProof/Core/Core.lean from kernel/core with Charon and
# Aeneas, and records the digest of the sources it was generated from.
#
# Pinned tools (the Lean side pins Aeneas' library to the same commit in
# lakefile.toml):
#   charon  AeneasVerif/charon 260ba2c82588291b1f9efaf4f42d7100adc9c6c2,
#           built with rustup toolchain nightly-2026-09-17
#   aeneas  AeneasVerif/aeneas c49c391fc881a26bf00968e0e967afe5832b981c
#
# Usage: CHARON=/path/to/charon AENEAS=/path/to/aeneas proof/extract.sh
set -eu
: "${CHARON:?set CHARON to the charon binary}"
: "${AENEAS:?set AENEAS to the aeneas binary}"
root=$(cd "$(dirname "$0")/.." && pwd)
llbc=$(mktemp -d)/core.llbc
(cd "$root/kernel/core" && "$CHARON" cargo --preset=aeneas --sysroot default --dest-file "$llbc")
"$AENEAS" -backend lean -loops-to-rec "$llbc" -dest "$root/proof/TclMeshProof/Core"
(cd "$root" && sha256sum kernel/core/Cargo.toml kernel/core/src/*.rs > proof/CORE_SOURCE.sha256)
