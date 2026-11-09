//go:build linux

package semantics

import (
	"os"
)

// Sector versions since the last sync, no separate page cache (model decision).
//
// Decision: a file is a map from 512-byte sector numbers to sectors; a sector
// holds every version of its contents since the file's last successful sync,
// oldest first, the last the page cache's. There is no separate `cur`
// (page cache) or `durable` (disk) copy. A crash leaves each sector one of its
// versions, chosen per sector. A successful fsync collapses the list to its
// last version.
//
// Lean: Impl.lean: Sector (vers, dirty), Sector.last, OsFile.change (appends a
// version), OsFile.synced (collapses), SecCand, CrashFile; Tests.lean:
// crash_loses_unsynced; notes/fs-semantics-v2.md, V5.
//
// Allowed: after the crash below, sector 0 holds A, B or C (any version since
// the sync), and sector 1 independently X or Y.
// Excluded: anything written before the last successful sync's version (Z).
//
// Why: writeback may write a page at any time between writes (so any
// intermediate version can be on disk), and pages are written back in no fixed
// order (so sectors are chosen independently: the audit's "Sector versions
// against page writeback"). A single "durable" copy cannot express "an
// intermediate version may be on disk"; a single "current" copy is the last
// version, so storing it separately would only add an invariant.
func SectorVersions(dir string) {
	f, _ := os.Create(dir + "/f")
	f.WriteAt(append(fill(512, 'Z'), fill(512, 'Z')...), 0)
	f.WriteAt(fill(512, 'A'), 0)
	f.WriteAt(fill(512, 'X'), 512)
	f.Sync() // sector 0: [A], sector 1: [X]
	f.WriteAt(fill(512, 'B'), 0)
	f.WriteAt(fill(512, 'C'), 0)
	f.WriteAt(fill(512, 'Y'), 512) // sector 0: [A, B, C], sector 1: [X, Y]
	// crash here
	// allowed:  sector 0 in {A, B, C}, sector 1 in {X, Y}, independently
	// excluded: Z anywhere
}
