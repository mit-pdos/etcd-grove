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
# nobody's children (asNobody, the permission tests) must reach the mount point: mktemp makes 0700
chmod 0755 "$W"
DEV=
GOPID=
cleanup() {
  local st=$? ok=1
  trap - EXIT INT TERM
  if [ -n "$GOPID" ] && kill -0 "$GOPID" 2>/dev/null; then
    # go test and its children (the test binary, nobody's helpers) hold the mount busy
    kill -TERM -- "-$GOPID" 2>/dev/null || true
    for _ in 1 2 3 4 5 6 7 8 9 10; do kill -0 "$GOPID" 2>/dev/null || break; sleep 0.5; done
    kill -KILL -- "-$GOPID" 2>/dev/null || true
    wait "$GOPID" 2>/dev/null || true
  fi
  if mountpoint -q "$W/mnt" 2>/dev/null; then
    for _ in 1 2 3 4 5; do sudo umount "$W/mnt" 2>/dev/null && break; sleep 1; done
    if mountpoint -q "$W/mnt"; then
      echo "cleanup: umount $W/mnt failed (busy: $(sudo fuser -vm "$W/mnt" 2>&1 | tr '\n' ' ')); lazy unmount" >&2
      sudo umount -l "$W/mnt" || { echo "cleanup: could not unmount $W/mnt" >&2; ok=0; }
    fi
  fi
  if [ -n "$DEV" ]; then
    sudo losetup -d "$DEV" || { echo "cleanup: could not detach $DEV" >&2; ok=0; }
  fi
  if [ "$ok" = 1 ]; then rm -rf "$W"; else echo "cleanup: left $W in place" >&2; fi
  exit "$st"
}
trap cleanup EXIT
trap 'exit 130' INT
trap 'exit 143' TERM
DEV=$(c_mkfs "$W/c.img")
c_mount "$DEV" "$W/mnt"
c_check "$W/mnt"
cd "$HERE"
# its own process group, so that cleanup can stop it and every child
SEMANTICS_C_DIR="$W/mnt" setsid go test -count=1 "$@" . &
GOPID=$!
wait "$GOPID"
