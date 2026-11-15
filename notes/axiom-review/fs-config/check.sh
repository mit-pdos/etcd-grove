#!/bin/bash
# Check a mounted filesystem, and this process's environment, against the target configuration C
# (README.md); exit 1, listing each difference, if it is not C.
# Usage: check.sh MOUNTPOINT [--allow OPT]...   (--allow: an option the experiment contrasts with C)
set -u
M=${1:?mountpoint}; shift
ALLOW=" "
while [ $# -gt 0 ]; do case $1 in --allow) ALLOW="$ALLOW$2 "; shift 2 ;; *) shift ;; esac; done
bad=0
say() { case "$ALLOW" in *" $1 "*) echo "check: allowed: $2" ;; *) echo "check: $2"; bad=1 ;; esac; }
[ "$(uname -m)" = x86_64 ] || say arch "arch $(uname -m), not x86_64"
case "$(uname -r)" in 7.0.*) ;; *) say kernel "kernel $(uname -r), not 7.0" ;; esac
[ "$(getconf PAGESIZE)" = 4096 ] || say pagesize "page size $(getconf PAGESIZE), not 4096"
[ "$(ulimit -f)" = unlimited ] || say fsize "RLIMIT_FSIZE $(ulimit -f), not unlimited"
[ -z "$(swapon --noheadings 2>/dev/null)" ] || say swap "swap is on"
SRC=$(findmnt -no SOURCE "$M")
[ "$(findmnt -no FSTYPE "$M")" = ext4 ] || say fstype "filesystem $(findmnt -no FSTYPE "$M"), not ext4"
DEV=$(basename "$(readlink -f "$SRC")")
KOPT=",$(tr '\n' ',' < /proc/fs/ext4/"$DEV"/options)"
for o in data=ordered dioread_nolock delalloc barrier; do
  case "$KOPT" in *",$o,"*) ;; *) say "$o" "ext4 option $o missing" ;; esac
done
for o in journal_async_commit nobarrier data=journal data=writeback nodelalloc ro; do
  case "$KOPT" in *",$o,"*) say "$o" "ext4 option $o set" ;; esac
done
H=$(sudo dumpe2fs -h "$SRC" 2>/dev/null)
BS=$(echo "$H" | awk -F: '/^Block size/ {gsub(/ /, "", $2); print $2}')
[ "$BS" = 4096 ] || say blocksize "block size $BS, not 4096"
FEAT=" $(echo "$H" | awk -F: '/^Filesystem features/ {print $2}') "
for f in has_journal extent; do case "$FEAT" in *" $f "*) ;; *) say "$f" "feature $f missing" ;; esac; done
for f in bigalloc fast_commit casefold inline_data; do case "$FEAT" in *" $f "*) say "$f" "feature $f set" ;; esac; done
[ $bad = 0 ] && echo "check: $M is C (kernel $(uname -r), ext4, block size $BS, options${KOPT%,})"
exit $bad
