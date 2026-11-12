//go:build linux

package semantics

import (
	"os"
)

// No failed writeback (environment assumption, audit F1).
//
// Decision: no writeback of a file in the roots' trees fails: the device
// returns no I/O error, and ext4's delayed allocation never fails at
// writeback. The model still lets `fsync` fail (more behaviours), which changes
// nothing: a read after it sees the page cache, and a later successful
// `fsync` makes everything durable.
//
// Lean: Impl.lean header ("No failed writeback"); OsFile.contents and
// ReadSees read OsFile.cache; the Fsync step's failure branch (st' = st);
// notes/axiom-review/fs-v2.md, F1.
//
// Excluded (under the assumption): the read below returning A.
//
// Why: Linux marks a page whose writeback failed clean, and can then drop it
// (memory pressure; ext4 invalidates the pages of a failed delayed
// allocation, "Delayed block allocation failed ... Data will be lost"), so a
// later read returns the disk's older contents. Documented: the 2018
// PostgreSQL "fsyncgate" (LWN, "PostgreSQL's fsync() surprise"), and
// Rebello et al., "Can Applications Recover from fsync Failures?" (ATC'20).
// The model does not describe that read. Neither etcd nor bbolt keeps using a
// file after a failed Sync (etcd panics, bbolt closes the DB).
func NoFailedWriteback(dir string) {
	f, _ := os.Create(dir + "/f")
	f.WriteAt(fill(512, 'A'), 0)
	f.Sync()
	f.WriteAt(fill(512, 'B'), 0)
	if err := f.Sync(); err != nil {
		buf := make([]byte, 512)
		f.ReadAt(buf, 0)
		// the model:          buf is B (the page cache's version)
		// Linux after an EIO: buf may be A (the page was dropped)
		// so the assumption excludes the EIO, and this branch is the model's
		// extra behaviour, reached only through the model's failing fsync
	}
}
