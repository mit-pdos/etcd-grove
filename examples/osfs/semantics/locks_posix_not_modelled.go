//go:build linux

package semantics

import (
	"os"
	"syscall"
)

// Classic POSIX record locks (F_SETLK, F_SETLKW) are not modelled (2026-11-15,
// pending review, notes/wal-units/locks.md).
//
// Decision: syscall.FcntlFlock and unix.FcntlFlock panic on F_SETLK (6) and
// F_SETLKW (7). Until 2026-11-15 they were the extension's trivial OfdLock (any
// errno, no state), which was sound only because it kept no state: these locks
// belong to the process, not to the description, so they never conflict within
// one process, and closing any fd of the file releases the process's lock;
// the OFD rule would exclude both behaviours.
//
// Lean: TrustedCode/syscall.lean, TrustedCode/golang_org/x/sys/unix.lean:
// FcntlFlock.impl (the panic).
//
// Allowed: nothing (a proved program never issues them; etcd's fileutil uses
// F_OFD_SETLK/F_OFD_SETLKW, examples/osfs/walfs F_OFD_SETLK).
// Excluded: nothing a proved program does.
//
// Why: measured on C (locks_test.go: TestLocksPosixPerProcess: two F_SETLK
// write locks through two opens in one process both succeed; an OFD lock
// conflicts with the process's lock; closing one of the fds releases it);
// fcntl(2), "Advisory record locking".
func PosixLocks(dir string) {
	a, _ := os.OpenFile(dir+"/LOCK", os.O_RDWR|os.O_CREATE, 0o600)
	lk := syscall.Flock_t{Type: syscall.F_WRLCK}
	_ = syscall.FcntlFlock(a.Fd(), syscall.F_SETLK, &lk) // the model panics
	a.Close()
}
