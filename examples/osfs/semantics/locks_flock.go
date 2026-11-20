//go:build linux

package semantics

import (
	"os"
	"syscall"
)

// flock locks: per open file description, whole file, conflicting within one
// process (2026-11-15, pending review, notes/wal-units/locks.md).
//
// Decision: the description's flock lock is a field of it (OsFd.flk: none,
// LOCK_SH or LOCK_EX). flock(fd, how) for how LOCK_SH, LOCK_EX or LOCK_UN,
// each with or without LOCK_NB, follows the same rule as the OFD lock
// (LockStep): a lock on a description with none of this kind succeeds only
// with no conflicting flock lock on another description, and fails with any
// errno and no change (EWOULDBLOCK, from LOCK_NB, included even with no
// conflict in the model: locks_spurious_eagain.go);
// LOCK_UN releases. flock needs no access mode. Another how is stuck (Linux:
// EINVAL; LOCK_MAND succeeds with no lock). Re-locking a description is stuck
// (Linux converts, not atomically, dropping the old lock first).
//
// Lean: Impl.lean: OsFd.flk, LockStep, flockReq, IsFsStep "Flock";
// TrustedCode/syscall.lean: Flock.impl.
//
// Allowed: minibolt's (examples/osfs/bboltfs) flock(LOCK_EX|LOCK_NB) loop
// retrying on EWOULDBLOCK, and its LOCK_UN before Close; etcd's fileutil
// fallback (lock_flock.go) when the kernel has no OFD locks.
// Excluded: two descriptions holding conflicting flock locks.
//
// Why: measured on C (locks_test.go: TestLocksFlock); fs/locks.c:
// flock_lock_inode returns -EAGAIN only on a conflict without FL_SLEEP (a
// conflict the model may not see: a description another process keeps alive
// past its close, locks_spurious_eagain.go, so the model allows EAGAIN from a
// non-blocking request at any time); the
// flock(2) man page (conversions not atomic).
func FlockLocks(dir string) {
	a, _ := os.Open(dir + "/db")
	b, _ := os.Open(dir + "/db")
	_ = syscall.Flock(int(a.Fd()), syscall.LOCK_EX|syscall.LOCK_NB) // nil, or an errno and no lock
	_ = syscall.Flock(int(b.Fd()), syscall.LOCK_EX|syscall.LOCK_NB) // if a holds it: an errno (EWOULDBLOCK, ...)
	_ = syscall.Flock(int(a.Fd()), syscall.LOCK_UN)                 // releases (or an errno)
	a.Close()
	b.Close()
}
