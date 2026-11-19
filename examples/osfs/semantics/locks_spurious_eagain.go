//go:build linux

package semantics

import (
	"os"
	"syscall"

	"golang.org/x/sys/unix"
)

// A non-blocking lock request may fail with EAGAIN although the model sees no
// conflict (2026-11-19, the user's decision via etcd-grove-03, option (b),
// after the attack on F1's fix: notes/wal-units/noioerr.md, session 7).
//
// Decision: LockStep's failure arm allows any nonzero errno, EAGAIN included,
// for a non-blocking request (flock with LOCK_NB, fcntl F_OFD_SETLK) as for a
// blocking one, whether or not LockConflict holds. Before, EAGAIN was allowed
// only on a conflict. The model does not track a description's references held
// outside the process, so it cannot say when such a conflict exists; it lets
// the request fail instead. A blocking request (flock without LOCK_NB,
// F_OFD_SETLKW) has the same outcomes: on Linux it waits for the reference to
// go and then succeeds, which the model has as a later success.
//
// Lean: Impl.lean: LockStep (the failure arm: no condition on EAGAIN), the
// header's "Locks", IsFsStep "Close"'s comment. Premises.lean: IoCovers covers
// a lock call only when it is blocking (flock without LOCK_NB, F_OFD_SETLKW),
// so NoIoErr promises success only to those.
//
// Allowed: below, b's non-blocking request fails with EAGAIN although a, the
// only other description the process had, is closed and no mapping holds it.
// Excluded: nothing new (the change only allows more).
//
// Why: measured on C (locks_test.go: TestLocksProcReaderEagain; first on this
// host by the attack, /shared/tmp/wallink-attack3/procrace, 200000 rounds: OFD
// 837 and 6261, flock 3312 and 18583 EAGAINs with the reader, 0 without):
// another process reading /proc/<pid>/fdinfo/<fd> (or readlink of
// /proc/<pid>/fd/<fd>, pidfd_getfd(2), ptrace; lsof and monitoring agents do
// the first two) takes a reference on the struct file (fs/proc/fd.c seq_show:
// get_file ... fput); when the process's close(2) comes in between, the
// description's last reference is the reader's, and its OFD and flock locks go
// only at that fput (__fput -> locks_remove_file). posix_lock_inode and
// flock_lock_inode then return -EAGAIN for a conflict with a description the
// process no longer has. No environment assumption excludes such readers
// (option (a), not taken: "no other process takes a reference to the process's
// files").
func LocksSpuriousEagain(dir string) {
	a, _ := os.OpenFile(dir+"/0.wal", os.O_RDWR|os.O_CREATE, 0o600)
	lk := syscall.Flock_t{Type: syscall.F_WRLCK}
	_ = syscall.FcntlFlock(a.Fd(), unix.F_OFD_SETLK, &lk)
	a.Close() // another process may be reading /proc/self/fdinfo/<a's fd> now
	b, _ := os.OpenFile(dir+"/0.wal", os.O_RDWR, 0o600)
	if err := syscall.FcntlFlock(b.Fd(), unix.F_OFD_SETLK, &lk); err != nil {
		// may be EAGAIN, with no conflict in the model
		_ = syscall.FcntlFlock(b.Fd(), unix.F_OFD_SETLKW, &lk) // waits, then succeeds (or any errno)
	}
	b.Close()
}
