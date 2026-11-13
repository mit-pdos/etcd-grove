#!/bin/bash
# Run models_test.go on a filesystem of configuration C (env_config.go): make and mount one with
# notes/axiom-review/fs-config/mkfs-mount.sh, check it with check.sh (its output is the record of
# the configuration the measurements were made on), run the tests in it, unmount. Needs sudo
# (losetup, mkfs.ext4, mount, dumpe2fs).
#
#   examples/osfs/semantics/run-models-on-c.sh [go test args...]
set -eu
HERE=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
source "$HERE/../../../notes/axiom-review/fs-config/mkfs-mount.sh"
W=$(mktemp -d)
DEV=$(c_mkfs "$W/c.img")
cleanup() { sudo umount "$W/mnt" 2>/dev/null || true; sudo losetup -d "$DEV" 2>/dev/null || true; rm -rf "$W"; }
trap cleanup EXIT
c_mount "$DEV" "$W/mnt"
c_check "$W/mnt"
cd "$HERE"
SEMANTICS_C_DIR="$W/mnt" go test -count=1 "$@" .
