//go:build linux

package semantics

import (
	"os"
)

// Crash sizes: any size between the smallest and largest since the last sync
// (model decision).
//
// Decision: a file records the smallest and largest sizes it had since its
// last successful sync (sizeLo, sizeHi); a crash gives it any size in that
// range, or between it and the target of a change in flight. The size is
// chosen independently of the bytes (data_durable_zeros.go: no ordering of
// sizes against data).
//
// Lean: Impl.lean: OsFile.sizeLo, OsFile.sizeHi, OsFile.change (widens),
// OsFile.synced (collapses), CrashFile (the `sz` bounds), OsChange.target.
//
// Allowed: after the crash below, any size in [100, 300], e.g. 250, which the
// file never had.
// Excluded: a size below 100 or above 300.
//
// Why: the on-disk size (ext4's i_disksize) moves at writeback, a range of
// pages at a time (delayed allocation writes extents in chunks), so it can stop
// at sizes the program never set; a shrink's orphan-list completion changes
// the size before freeing blocks (the audit's "Crash sizes"). Any size in the range covers all of these without
// modelling which. etcd's WAL and bbolt never trust a file's length: they
// check records by CRC and checksummed metas.
func SizesSinceSync(dir string) {
	f, _ := os.Create(dir + "/f")
	f.WriteAt(fill(100, 'a'), 0)
	f.Sync()                       // size 100: sizeLo = sizeHi = 100
	f.WriteAt(fill(200, 'b'), 100) // 300
	f.Truncate(150)                // 150; range [100, 300]
	// crash here
	// allowed:  any size in [100, 300]
	// excluded: 99, 301
}
