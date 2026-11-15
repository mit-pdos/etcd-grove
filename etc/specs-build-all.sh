#!/usr/bin/env bash
# Build every module of the spec plan (the SpecPlan library), serialized through the same lock as
# etc/specs-build.sh, and print only the errors and the final status.
set -uo pipefail
cd "$(dirname "$0")/.."
exec 9>.lake/specs-build.lock
flock 9
lake build SpecPlan > .lake/specs-build-all.log 2>&1
st=$?
grep -E "^error|error:" .lake/specs-build-all.log | head -200
echo "specs-build-all: lake exit $st"
exit $st
