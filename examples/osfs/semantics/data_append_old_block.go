//go:build linux

package semantics

import (
	"os"
)

// An append into the block that holds the end is not ordered (model decision,
// a consequence of durable zeros covering only the pages past the size).
//
// Decision: the page that holds the file's end keeps its bytes past the size
// as they are on disk (OsFile.ofDisk: diskByte gives img b for a page with a
// byte below the size), stale bytes a crash left there included; a crash may
// keep a grown size with those bytes' synced values.
//
// Lean: Impl.lean: diskByte, OsFile.ofDisk, CrashFile; Tests.lean:
// crash_append_old_block.
//
// Allowed: after the crash below, size 1 (00); size 2 with 00 05; and size 2
// with 00 00 or 00 <stale byte>: the new size without the data.
//
// Why: measured on configuration C (notes/axiom-review/fs-v2-f3/ordered.sh
// append-alloc: size 2 reading 00 00; with STALE=1, the block holding 00 07
// on disk, size 2 reading 00 07). A write into an allocated block updates the
// size at write_end, and the next journal commit can carry it without the
// data. Programs must not trust a grown length: etcd's WAL checks every
// record's CRC (and treats a zero sector as torn, premise_sector_whole.go).
func AppendOldBlock(dir string) {
	f, _ := os.Create(dir + "/f")
	f.Write([]byte{0x00})
	f.Sync() // size 1; block 0 allocated
	f.WriteAt([]byte{0x05}, 1)
	// crash here
	// allowed: size 1; size 2 = 00 05; size 2 = 00 00 (or 00 <stale byte>)
}
