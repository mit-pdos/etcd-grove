//go:build linux

package semantics

import (
	"os"
	"syscall"

	"golang.org/x/sys/unix"
)

// Blocking lock requests wait (2026-11-15, pending review,
// notes/wal-units/locks.md); waiting is a step (2026-11-20, the user's
// approval of option (A), via etcd-grove-03; notes/specs-only/ledger.md,
// "a blocking lock request in conflict may fail").
//
// Decision: F_OFD_SETLKW and flock without LOCK_NB follow the same rule as
// the non-blocking requests (LockStep, locks_spurious_eagain.go): success only
// when no other description holds a conflicting lock; while one does, the call
// waits: it steps to itself (the same call, nothing changed), as mmap without
// room does (MmapStall); it may also fail at any time with any nonzero errno
// and no change. Under the premises on steps, a covered blocking request never
// fails: it ends with errno 0 or waits (NoIoErr's OfdLock clause, NoMapLockErr's
// Flock clause), which needs the wait to be a step so that the premises always
// leave one (StepKeeps).
//
// Lean: Impl.lean: LockStep (nb, self: the third outcome, the wait),
// IsFsStep "OfdLock" (cmd 38), "Flock" (no LOCK_NB); Premises.lean: ErrnoZero
// "OfdLock", MapLockOk "Flock" (the wait counted as no error).
//
// Allowed: below, LockFile waits (steps to itself) until the other goroutine
// closes its fd, then succeeds; or, outside the premises, it fails with an
// errno at any point. Under the premises (a covered file), it does not fail.
// Excluded: LockFile succeeding while the other description holds the lock.
//
// Why: measured on configuration C (locks_test.go: TestLocksBlocking: a waiting
// F_OFD_SETLKW and a waiting flock(LOCK_EX) return nil once the holder's fd is
// closed by another goroutine, and 20 SIGUSR1s with a Go handler, and the
// runtime's SIGURG preemption signals, meanwhile never made them return: Go
// installs its handlers with SA_RESTART, and signal(7) lists F_OFD_SETLKW and
// flock as restarted). The failures the base semantics keeps: ENOLCK/ENOMEM
// from the lock's allocation at the call's entry (fs/fcntl.c fcntl_setlk:
// locks_alloc_lock), EINTR under a handler without SA_RESTART; the premises
// exclude them on covered files (assumed: no allocation failure, as for the
// write path; Go's SA_RESTART handlers, measured). EDEADLK is not an outcome:
// OFD lock requests are exempt from the kernel's deadlock detection (fcntl(2):
// "not subject to deadlock detection"; fs/locks.c posix_locks_deadlock returns
// 0 for an FL_OFDLCK request) and flock has none (documented, cited); a
// deadlock of two waiting requests in the model is two threads stepping to
// themselves (no failure under the premises), as on Linux two hung calls. An
// ENOLCK after a wakeup (the lock allocated again on each retry) is the
// allocation failure above.
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
