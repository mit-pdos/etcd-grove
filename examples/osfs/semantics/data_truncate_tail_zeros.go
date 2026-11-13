//go:build linux

package semantics

import (
	"os"
	"syscall"
)

// ftruncate zeroes the rest of the page holding the old end, whatever the new
// size (measured). Pending the user's review (P2 of
// notes/axiom-review/eof-page.md, 2026-11-13).
//
// Decision: an ftruncate (and open's O_TRUNC) to the same, a smaller or a
// larger size announces zero for every byte from where the old and new sizes
// part to the end of the page holding the larger of the two ends, and lands
// zero there in the page cache: past the new size in the old end's page too
// (a growth's new last page past the old end's page is a hole, zero anyway).
// A sync then makes zero those bytes' one candidate. fallocate(0) zeroes only
// up to its target (falloc-in below): its range stays [min old new, max old
// new).
//
// Lean: Impl.lean: pageEnd, OsChange.ofResize (trunc = true: hi := pageEnd
// (max f.size sz); false for fallocate), the kinds OsChangeKind.truncate and
// .falloc (FtruncateFinish needs .truncate, FallocFinish .falloc), the steps
// FtruncateStart, FallocStart and OpenEffect (O_TRUNC); the header's "An
// ftruncate zeroes the rest of the page holding the old end"; Tests.lean:
// trunc_same_synced_zero.
//
// Allowed: after ftruncate(5000) of a file of size 5000 and a sync, the bytes
// 5000..8191 have the one candidate 00; after the write and the crash below,
// size 5010 reading 00 or 42 at 5000..5009, byte by byte.
// Excluded: the stale 53 under the size (which the model allowed before: the
// sync kept the page cache's stale tail as the bytes' candidate; and which
// Linux shows without the ftruncate, pl-append in eof-page.md).
//
// Why: measured on configuration C (notes/axiom-review/eof-page/eof.sh, a file
// of size 5000 whose block holding EOF holds the stale 53 past 5000 on disk):
// trunc-eq (ftruncate(5000)), trunc-down (4500), trunc-up-in (6000) and
// trunc-up-past (9192) read 00 past the new size through a mapping and leave
// 00 on disk to the block's end after fsync; zerotoend (fileutil.ZeroToEnd:
// ftruncate(100), fallocate(0, 0, 9000), fdatasync) reads 00; pl-trunc-append
// (ftruncate(5000), then 42 x10 at 5000, power loss): size 5000 at 4 s (the
// commit waits for the ordered zeroing), size 5010 reading 42 at 26 s, never
// the 53. From the source (Linux v7.0): ext4_setattr calls ext4_truncate even
// when the size does not change (fs/ext4/inode.c:5996-6003), whose
// ext4_block_truncate_page zeroes the block holding the size to its end, "so
// it doesn't yield old data if the file is later grown" (:4140-4143, :4556),
// adding the range to the transaction's ordered data (:4096-4102); a growth
// tail-zeroes the old EOF block (:5943-5948); fallocate's
// ext4_zero_partial_blocks zeroes only up to its target (fs/ext4/extents.c:
// 4649-4658; falloc-in reads the stale 53 past 6000). Assumed: no allocation
// failure in the write path, widened to this zeroing (data_short_io.go):
// __ext4_block_zero_page_range gets the folio with FGP_CREAT under ~__GFP_FS
// and ext4_truncate ignores its failure, so a memory-cgroup at its limit could
// skip the zeroing of an uncached folio. The WAL needs it: ReadAll's
// fileutil.ZeroToEnd, then the next Save writes past an unaligned size.
func TruncateTailZeros(dir string) {
	f, _ := os.OpenFile(dir+"/f", os.O_RDWR, 0)
	// Set-up (eof.sh plants it): size 5000, the block holding EOF holding the
	// stale 53 past 5000 on disk, all of it durable.
	f.Truncate(5000) // zeroes 5000..8191 in the page cache, ordered on disk
	f.Sync()         // 5000..8191: the one candidate 00
	f.WriteAt(fill(10, 0x42), 5000)
	// crash here
	// allowed: size 5000; size 5010 reading 00 or 42 at 5000..5009
	// excluded: 53 at 5000..5009
	syscall.Fdatasync(int(f.Fd()))
}
