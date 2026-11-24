#!/bin/sh
# The Lean transcription's differential test (notes/antithesis-check-design.md §10): export the
# fixtures of the verdicts files (default: the three committed ones) with the Go's verdicts, and
# check AntCheck.run's verdict against TLC's on each. Needs a built tree (`lake build
# Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Tla.Check`). About 10 minutes
# for the 512 committed fixtures (the interpreter).
set -e
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../../../.." && pwd)
out=$(mktemp)
trap 'rm -f "$out"' EXIT
cd "$here/.."
if [ $# -eq 0 ]; then
	set -- testdata/verdicts.txt testdata/verdicts-fuzz.txt testdata/verdicts-targeted.txt
fi
go run ./cmd/leanexport "$@" > "$out"
cd "$root"
lake env lean --run examples/raft/antithesis/check/testdata/LeanDiff.lean "$out"
