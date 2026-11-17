//go:build linux

package semantics

import (
	"os"
)

// Crash candidates, byte by byte (model decision).
//
// Decision: a file is its page cache and, for each byte, its crash
// candidates: the value as of the last successful sync, then the value each
// change since announced for it (stamped with the change's number). A change
// announces all of its data when it starts; a successful fsync collapses each
// byte to its page-cache value. A crash leaves each byte any one of its
// candidates, independently of every other byte, or zero at or past the
// smallest size since the last sync (data_writeback_tail_zeros.go). Nothing
// groups bytes into sectors or pages.
//
// Lean: Impl.lean: OsFile (cache, cand), OsFile.announce, OsChange.ofWrite/
// ofResize, OsFile.land, OsFile.synced, CrashFile; Tests.lean: crash_mix,
// crash_loses_unsynced, crash_after_sync; notes/fs-semantics-v2.md,
// "Byte-level crash candidates" (it supersedes V5's sector versions).
//
// Allowed: after the crash below, each byte of [0,1024) holds A, B or C, each
// independently (a byte A next to a byte C is allowed).
// Excluded: Z anywhere (overwritten before the last successful sync), or any
// value never written there since that sync (the bytes here are below the
// synced size 1024, which no writeback zeroes).
//
// Why: measured. One pwrite can reach disk mixed with what was there, mid-sector
// (data_torn_source_page.go, data_mixed_writeback.go); writeback may write a
// page at any time between writes, so any intermediate value can be on disk.
// The candidates of a byte are exactly the values it can have on disk; the
// stamps record which values existed together, for the premises of the
// clients that need more (premise_sector_whole.go; bbolt's P1).
func CrashCandidates(dir string) {
	f, _ := os.Create(dir + "/f")
	f.WriteAt(fill(1024, 'Z'), 0)
	f.WriteAt(fill(1024, 'A'), 0)
	f.Sync() // each byte: [A]
	f.WriteAt(fill(1024, 'B'), 0)
	f.WriteAt(fill(1024, 'C'), 0) // each byte: [A, B (change 1), C (change 2)]
	// crash here
	// allowed:  each byte A, B or C, independently
	// excluded: Z anywhere
}
