#!/bin/bash
# comparator-tools.sh: build the comparator's tools into $DSV_LAB/cache/tools/comparator (lab-side only;
# sandbox.sh mounts its bin/ read-only at /opt/lab/comparator/bin in check views, never in a run's).
# With network, as the owner of DSV_LAB: elan with the runs' toolchain (etcd-grove's lean-toolchain),
# Go in /usr/local/go or on PATH; rustup is installed under cache/tools/comparator for nanoda.
# Pinned: comparator and lean4export at CMP_REV (default v4.34.0; rebuilt with the runs' toolchain:
# lean4export reads the project's .olean files, which must be of the same Lean), landrun and
# nanoda_lib at the commits below.
set -e
HERE=$(cd "$(dirname "$0")" && pwd); GROVE=$(cd "$HERE/../../.." && pwd)
LAB=$(cd "${DSV_LAB:?set DSV_LAB to the experiment directory}" && pwd)
T=$LAB/cache/tools/comparator; mkdir -p "$T/src" "$T/bin"
TCN=$(cat "$GROVE/lean-toolchain"); CMP_REV=${CMP_REV:-v4.34.0}
export PATH=$HOME/.elan/bin:/usr/local/go/bin:$PATH
get() { [ -d "$T/src/$2" ] || git clone -q "https://github.com/$1/$2.git" "$T/src/$2"; git -C "$T/src/$2" checkout -q "$3"; }
get leanprover lean4export "$CMP_REV"
get leanprover comparator "$CMP_REV"
get Zouuup landrun ec104f6
get ammkrn nanoda_lib 0da9f98
for d in lean4export comparator; do
    echo "$TCN" >"$T/src/$d/lean-toolchain"; (cd "$T/src/$d" && lake build)
done
(cd "$T/src/landrun" && go build -o "$T/bin/landrun" ./cmd/landrun)
export RUSTUP_HOME=$T/rust/rustup CARGO_HOME=$T/rust/cargo
[ -x "$CARGO_HOME/bin/cargo" ] || { curl -sSf https://sh.rustup.rs | sh -s -- -y --no-modify-path --profile minimal; }
(cd "$T/src/nanoda_lib" && "$CARGO_HOME/bin/cargo" build --release)
cp "$T/src/comparator/.lake/build/bin/comparator" "$T/src/lean4export/.lake/build/bin/lean4export" \
   "$T/src/nanoda_lib/target/release/nanoda_bin" "$T/bin/"
ls -la "$T/bin"
