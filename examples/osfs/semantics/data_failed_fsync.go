//go:build linux

package semantics

import (
	"os"
)

// A failed fsync leaves lost sectors, which no later sync writes (model
// decision).
//
// Decision: a failed fsync clears the dirty bit of every dirty sector not under
// an in-flight change, keeping its versions: the sector is *lost*. A later
// successful fsync writes only dirty sectors, so a lost sector stays
// uncertain (any of its versions after a crash) until it is written again.
// A failed fsync is never EINTR.
//
// Lean: Impl.lean: Sector.dirty, OsFile.syncFailed, OsFile.synced (only
// `s.dirty`), the Fsync step's failure branch; Tests.lean:
// crash_lost_after_sync.
//
// Allowed: after the crash below, sector 0 holds A or B, although the second
// Sync returned nil.
// Excluded: sector 0 anything else; the second Sync making B durable is
// allowed but not promised.
//
// Why: documented. Linux clears the dirty state of pages whose writeback
// failed and reports the error once per file description (errseq); a retried
// fsync does not write them again (the 2018 "fsyncgate", LWN "PostgreSQL's
// fsync() surprise"). This is the only reason the model has a dirty bit:
// without failed fsyncs "dirty" would equal "more than one version". EINTR is
// excluded because ext4's and xfs's fsync waits are uninterruptible and Go's
// File.Sync retries EINTR. (Under the no-failed-writeback assumption the
// failure branch is an extra behaviour of the model, sound to keep.)
func FailedFsync(dir string) {
	f, _ := os.Create(dir + "/f")
	f.WriteAt(fill(512, 'A'), 0)
	f.Sync() // sector 0: [A], clean
	f.WriteAt(fill(512, 'B'), 0)
	if err := f.Sync(); err != nil {
		// sector 0 is lost: [A, B], not dirty
		f.Sync() // returns nil: nothing dirty to write
		// crash here
		// allowed: sector 0 = A or B
	}
}
