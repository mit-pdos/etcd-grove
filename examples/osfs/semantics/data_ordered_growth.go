//go:build linux

package semantics

import (
	"os"
)

// Ordered growth: a new block is on disk before a size that covers it (model
// decision, ext4 data=ordered and xfs).
//
// Decision: a sector is *fresh* if its 4096-byte page had no block at the
// file's last successful sync (or the boot or crash the file comes from), and
// no size since has reached the page except by a change that gave this sector
// a newer version. Under a crash size that covers a fresh sector, the sector
// is never its first (synced) version.
//
// Lean: Impl.lean: Sector.fresh, pageIn, OsFile.ofDisk and OsFile.synced (set
// it), OsFile.change (clears it for a page newly reached without writing this
// sector), Sector.covVers, CovCand, CrashFile (`512 * n < sz → CovCand`); the
// header's "Ordered growth"; Tests.lean: crash_fresh_written, crash_current,
// FreshOk.
//
// Allowed: after the crash below, size 0; or size 4096 holding the page.
// Excluded: size 4096 holding zeros (or any part of it zeros).
//
// Why: measured on Linux 7.0 (notes/axiom-review/fs-v2-f3/ordered.sh,
// delay.sh; results in notes/axiom-review/fs-v2.md, F3): ext4 data=ordered
// allocates a block the file did not have in the transaction that commits the
// size covering it, after writing its data (with the data write held 10 s by
// dm-delay, a crash kept size 1 and no extent); xfs commits a write's size at
// I/O completion (size 1 in all write cases). Without this rule the model
// allowed the zeros, and bbolt's init was unprovable: init writes the four
// first pages of an empty file at once and fdatasyncs; a crash in between
// could leave a 16 KiB file of zeros, both metas invalid, and the database
// unopenable, which ext4 never does. Not covered: ext4 data=writeback (the
// size may commit first; outside the environment assumption).
func OrderedGrowth(dir string) {
	f, _ := os.OpenFile(dir+"/db", os.O_RDWR|os.O_CREATE, 0o600)
	// the directory entry is durable; the file is empty and synced
	page := make([]byte, 4096)
	copy(page, "MAGIC")
	f.WriteAt(page, 0)
	// crash here, before any f.Sync()
	// allowed:  size 0; size 4096 starting with MAGIC
	// excluded: size 4096 of zeros
}
