#!/bin/bash
# Make and mount a filesystem of the target configuration C (README.md) on a loop device.
# Every experiment of notes/axiom-review/ sources it, so that each one tests C and nothing else.
#
#   source mkfs-mount.sh
#   DEV=$(c_mkfs IMG [SIZE])   a sparse image file IMG (default 1G: mke2fs's "default" type, not
#                              "small"), `mkfs.ext4` with its defaults (4 KiB blocks, extents,
#                              has_journal, no bigalloc, no fast_commit, no casefold); prints the
#                              loop device
#   c_mount DEV DIR [OPTS]     mounts DEV on DIR with ext4's default options (data=ordered,
#                              dioread_nolock, delalloc, barrier); OPTS may only add what C allows
#                              (commit=N) or what an experiment contrasts with C (dioread_lock),
#                              which the experiment then says
#   c_check DIR [--allow OPT]  check.sh: exits 1 unless DIR (and this process) is C
c_mkfs() {
  local img=${1:?image} size=${2:-1G}
  rm -f "$img"; truncate -s "$size" "$img"
  local dev; dev=$(sudo losetup --find --show "$img")
  sudo mkfs.ext4 -q -F "$dev" >/dev/null
  echo "$dev"
}
c_mount() {
  local dev=${1:?device} dir=${2:?mountpoint} opts=${3:-}
  mkdir -p "$dir"
  if [ -n "$opts" ]; then sudo mount -t ext4 -o "$opts" "$dev" "$dir"; else sudo mount -t ext4 "$dev" "$dir"; fi
  sudo chmod 777 "$dir"
}
c_check() { "$(dirname "${BASH_SOURCE[0]}")/check.sh" "$@"; }
