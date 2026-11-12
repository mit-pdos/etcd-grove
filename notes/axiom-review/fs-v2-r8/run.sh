#!/bin/bash
# Round 8 (../fs-v2-r8.md): runs gocheck/ on a filesystem of configuration C (../fs-config/).
# Usage: run.sh WORKDIR
set -eu
W=${1:?workdir}; mkdir -p "$W"
H=$(cd "$(dirname "$0")" && pwd)
. "$H/../fs-config/mkfs-mount.sh"
DEV=$(c_mkfs "$W/img"); c_mount "$DEV" "$W/mnt"
trap 'sudo umount "$W/mnt"; sudo losetup -d "$DEV"' EXIT
c_check "$W/mnt"
cd "$H/gocheck" && R8_DIR="$W/mnt" GOTOOLCHAIN=go1.27.3 GOFLAGS=-count=1 go test -v ./...
