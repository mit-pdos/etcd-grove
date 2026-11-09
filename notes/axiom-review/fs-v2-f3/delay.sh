#!/bin/bash
# Can ext4 (default options: delalloc, dioread_nolock) commit a size grown by an append into a NEW
# block while the block's data write is still in flight? (notes/axiom-review/fs-v2.md, F3)
#
# Usage: delay.sh WORKDIR [OFF]   (OFF: where the append writes 07; default 4096, a new block)
# The data device sits behind dm-delay (writes delayed 10 s, reads and flushes not); the journal is
# an external device with no delay. A synced one-byte file 00; pwrite 07 at OFF; writeback started
# without waiting (sync_file_range -w); the journal commits every second. After 4 s, copies of both
# devices' backing files are the crash: the journal's writes are in its copy, the data's are not.
# The copy is recovered (e2fsck with the journal copy) and its size and bytes printed.
set -u
D=${1:?workdir}
OFF=${2:-4096}
mkdir -p "$D/mnt" "$D/mnt2"
DI=$D/data.img; JI=$D/jnl.img
rm -f "$DI" "$JI" "$DI.crash" "$JI.crash"
truncate -s 512M "$DI"; truncate -s 64M "$JI"
DL=$(sudo losetup --find --show "$DI"); JL=$(sudo losetup --find --show "$JI")
sudo mke2fs -q -F -O journal_dev -b 4096 "$JL"
# C's mkfs.ext4 defaults, but an external journal (so dm-delay can delay the data alone; crash.sh
# in ../fs-config does the same with C's internal journal)
sudo mkfs.ext4 -q -F -b 4096 -J device="$JL" "$DL"
SZ=$(sudo blockdev --getsz "$DL")
sudo dmsetup create f3delay --table "0 $SZ delay $DL 0 0 $DL 0 10000 $DL 0 0"
sudo mount -o data=ordered,commit=300,journal_path="$JL" /dev/mapper/f3delay "$D/mnt"
grep f3delay /proc/mounts
sudo chmod 777 "$D/mnt"
F=$D/mnt/f
printf '\x00' > "$F"; sudo sync
OLD=$(cat /proc/sys/vm/dirty_writeback_centisecs)
sudo sysctl -q vm.dirty_writeback_centisecs=0
sudo mount -o remount,commit=1 "$D/mnt"
sudo xfs_io -c "pwrite -S 0x07 $OFF 1" "$F" >/dev/null
sudo xfs_io -c "sync_range -w 0 0" "$F"
echo "in memory: size $(stat -c %s "$F")"
python3 -c 'import time; time.sleep(4)'
echo "live, before the copy: $(sudo filefrag -v "$F" | grep -E '^ +[0-9]+:' | tr -s ' ' | tr '\n' ';')"
sudo cp "$DI" "$DI.crash"; sudo cp "$JI" "$JI.crash"
sudo sysctl -q vm.dirty_writeback_centisecs="$OLD"
python3 -c 'import time; time.sleep(8)'
sudo umount "$D/mnt"; sudo dmsetup remove f3delay; sudo losetup -d "$DL" "$JL"
DL2=$(sudo losetup --find --show "$DI.crash"); JL2=$(sudo losetup --find --show "$JI.crash")
sudo e2fsck -fy -j "$JL2" "$DL2" >/dev/null 2>&1
echo "crash image: size $(sudo debugfs -R 'stat /f' "$DL2" 2>/dev/null | awk '/Size:/ {print $NF; exit}'); extents: $(sudo debugfs -R 'ex /f' "$DL2" 2>/dev/null | tail -n +2 | tr -s ' ' | tr '\n' ';')"
sudo mount -o journal_path="$JL2" "$DL2" "$D/mnt2"
F2=$D/mnt2/f
echo "after recovery: size $(stat -c %s "$F2"), byte $OFF: $(od -An -tx1 -j"$OFF" -N1 "$F2")"
sudo umount "$D/mnt2"; sudo losetup -d "$DL2" "$JL2"
