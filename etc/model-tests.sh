#!/usr/bin/env bash
# The Go tests of the packages with a Go model overlay (a goose config's [model] table,
# perennial#692): each package's own tests, and its models' differential tests, run against the
# package with its models spliced in (`goose model-overlay`). The list, and the tests left out with
# why, is etc/gomodels.py's TESTS. Perennial's own models are tested by its etc/model-tests.sh.
#
# usage: etc/model-tests.sh [--perennial DIR] [NAME...]   (DIR: a Perennial checkout whose goose
#        to use; default: the pin's, as etc/goose.py)
set -euo pipefail
exec python3 "$(dirname "$0")/gomodels.py" test "$@"
