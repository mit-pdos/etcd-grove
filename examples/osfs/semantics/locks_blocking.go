//go:build linux

package semantics

import (
	"os"
	"syscall"

	"golang.org/x/sys/unix"
)

// Blocking lock requests wait (2026-11-15, pending review,
// notes/wal-units/locks.md).
//
// Decision: F_OFD_SETLKW and flock without LOCK_NB follow the non-blocking
// rule (LockStep with nb false): success only when no other description holds
// a conflicting lock, so while one does the call takes no successful step (it
// waits); it may fail at any time with any nonzero errno and no change.
//
// Lean: Impl.lean: LockStep (nb), IsFsStep "OfdLock" (cmd 38), "Flock" (no
// LOCK_NB).
//
// Allowed: below, LockFile waits until the other goroutine closes its fd, then
// succeeds; or it fails with an errno at any point.
// Excluded: LockFile succeeding while the other description holds the lock.
//
// Why: measured on C (locks_test.go: TestLocksBlocking: a waiting
// F_OFD_SETLKW and a waiting flock(LOCK_EX) return nil once the holder's fd is
// closed by another goroutine, and 20 SIGUSR1s with a Go handler, and the
// runtime's SIGURG preemption signals, meanwhile never made them return: Go
// installs its handlers with SA_RESTART, and signal(7) lists F_OFD_SETLKW and
// flock as restarted). The failures kept: ENOLCK/ENOMEM from the lock's
// allocation at the call's entry (fs/fcntl.c fcntl_setlk: locks_alloc_lock;
// excluding them would need an allocation assumption), EINTR under a handler
// without SA_RESTART. [user] option not taken (notes/wal-units/locks.md 2.4):
// no failure while waiting, so that a LockFile on a held lock never returns.
func BlockingLock(dir string) {
	a, _ := os.OpenFile(dir+"/0.wal", os.O_RDWR|os.O_CREATE, 0o600)
	lk := syscall.Flock_t{Type: syscall.F_WRLCK}
	_ = syscall.FcntlFlock(a.Fd(), unix.F_OFD_SETLK, &lk)
	go func() { a.Close() }() // releases
	b, _ := os.OpenFile(dir+"/0.wal", os.O_RDWR, 0o600)
	lk2 := syscall.Flock_t{Type: syscall.F_WRLCK}
	_ = syscall.FcntlFlock(b.Fd(), unix.F_OFD_SETLKW, &lk2) // waits for the close (or fails)
	b.Close()
}
