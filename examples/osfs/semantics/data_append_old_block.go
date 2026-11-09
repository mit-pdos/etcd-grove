//go:build linux

package semantics

import (
	"os"
)

// An append into the block that holds the end is not ordered (model decision,
// the exception to ordered growth).
//
// Decision: a sector whose page already had a block (it holds the file's end,
// or lies below it) is not fresh: a crash may keep a grown size with that
// sector's synced version, whose bytes past the old end are whatever the block
// holds (zeros, or stale bytes a crash left there).
//
// Lean: Impl.lean: Sector.fresh (false for a page below the size at the
// sync), CovCand; Tests.lean: crash_append_old_block.
//
// Allowed: after the crash below, size 1 (00); size 2 with 00 05; and size 2
// with 00 00: the new size without the data.
// Excluded: nothing more; the rule keeps all three.
//
// Why: measured on Linux 7.0 ext4 data=ordered
// (notes/axiom-review/fs-v2-f3/ordered.sh append-alloc; with STALE=1 the
// block held 00 07 on disk and the crash image read 00 07 under size 2). A
// write that allocates nothing joins no ordered-data list, and the next
// journal commit can carry the new size alone. A rule "a byte below the size
// comes from a version whose size covered it, or is zero" would wrongly
// exclude the stale-byte outcome. Programs must not trust a grown length:
// etcd's WAL checks every record's CRC and treats a zero sector as torn.
func AppendOldBlock(dir string) {
	f, _ := os.Create(dir + "/f")
	f.Write([]byte{0x00})
	f.Sync() // size 1; block 0 allocated
	f.WriteAt([]byte{0x05}, 1)
	// crash here
	// allowed: size 1; size 2 = 00 05; size 2 = 00 00 (or 00 <stale byte>)
}
