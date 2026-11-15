//go:build linux

package semantics

import (
	"os"
)

// A failed fsync changes nothing (model decision, under the no-failed-writeback
// assumption).
//
// Decision: a failed fsync leaves every byte's crash candidates as they were;
// a later successful fsync makes everything durable. A failed fsync is never
// EINTR.
//
// Lean: Impl.lean: the Fsync step's failure branch (st' = st); OsFile.synced.
//
// Allowed: after the first crash below, byte 0 holds A or B; after the second
// (the later Sync returned nil), B.
// Excluded: B lost after a later successful Sync.
//
// Why: under the no-failed-writeback assumption (env_no_failed_writeback.go),
// a failed fsync's error does not come from a failed writeback, so whatever it
// started either completed (the bytes are on disk) or left them dirty (a later
// sync writes them). Linux does lose data whose writeback failed (it marks the
// pages clean; the 2018 "fsyncgate", LWN "PostgreSQL's fsync() surprise"): the
// assumption excludes that, as it excludes the page cache dropping such data.
// EINTR is excluded because ext4's fsync waits are uninterruptible and Go's
// File.Sync retries EINTR.
func FailedFsync(dir string) {
	f, _ := os.Create(dir + "/f")
	f.WriteAt(fill(512, 'A'), 0)
	f.Sync()
	f.WriteAt(fill(512, 'B'), 0)
	if err := f.Sync(); err != nil {
		// crash here: each byte A or B
		if f.Sync() == nil {
			// crash here: B
		}
	}
}
