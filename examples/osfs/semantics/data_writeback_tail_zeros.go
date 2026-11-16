//go:build linux

package semantics

import (
	"os"
)

// Writeback zeroes the page holding the end past the size, so a byte past the
// smallest size since the last sync may come back zero after a crash, whatever
// its candidates (measured). Pending the user's review (P1 of
// notes/axiom-review/eof-page.md, 2026-11-13).
//
// Decision: a crash leaves each byte one of its candidates, or zero if the byte
// is at or past the smallest size the file had since its last successful sync
// (OsFile.sizeLo). A byte below sizeLo was below the size throughout and is
// never zeroed so; after a sync sizeLo is the size, so the stale candidate the
// sync keeps past the size (the page cache's tail) is covered too.
//
// Lean: Impl.lean: CrashFile (the disjunct f.sizeLo ≤ b ∧ img b = 0), the
// header's "Writeback zeroes the page holding the end past the size";
// Bridge.lean: crash_byte; CrashFiles.lean: FileCrashedR; Tests.lean:
// crash_wb_tail_zero.
//
// Allowed: after the crash below, size 5020 with bytes 5010..5019 reading 00,
// though their candidates are only the stale byte S and 43 (the fsync made S,
// the page cache's value past the size then, their candidate as of the sync).
// Excluded: nothing new; the model used to exclude the 00 above (unsound).
//
// Why: measured on configuration C (notes/axiom-review/eof-page/eof.sh
// pl-wb-zero, results/power-loss.txt: the journal linear, every other block
// behind dm-delay; size 5020 reading 00 at 5010..5019 both 4 s and 26 s after
// the change). ext4_bio_write_folio (fs/ext4/page-io.c:476-483, v7.0): "The
// folio straddles i_size. It must be zeroed out on each and every writepage
// invocation", folio_zero_segment(folio, len, folio_size(folio)): the page
// cache's folio itself is zeroed past the size of the moment and the block is
// written with those zeros; the second write's size can then commit before its
// data (data_append_old_block.go).
func WritebackTailZeros(dir string) {
	f, _ := os.Create(dir + "/f")
	// Set-up (eof.sh plants it): size 5000, the block holding EOF holding the
	// stale S past 5000 on disk, all of it durable.
	f.WriteAt(fill(10, 0x42), 5000)
	f.Sync() // writeback zeroes 5010.. on disk and in the page cache
	f.WriteAt(fill(10, 0x43), 5010)
	// crash here
	// allowed: size 5020, 5010..5019 = 00 (or S or 43, byte by byte)
}
