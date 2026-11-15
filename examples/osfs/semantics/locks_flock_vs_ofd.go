//go:build linux

package semantics

import (
	"os"
	"syscall"

	"golang.org/x/sys/unix"
)

// flock and OFD locks are independent (2026-11-15, pending review,
// notes/wal-units/locks.md).
//
// Decision: a description's flock lock and its OFD lock are two fields
// (OsFd.flk, OsFd.ofd), and a request of one kind is checked only against the
// other descriptions' locks of the same kind (LockConflict's kind).
//
// Lean: Impl.lean: LockKind, OsFd.lk, LockConflict.
//
// Allowed: below, both locks succeed.
// Excluded: nothing a Linux run does on C: making the kinds conflict would
// exclude that run.
//
// Why: measured on C (locks_test.go: TestLocksFlockVsOFD); fs/locks.c keeps
// flock locks and POSIX/OFD locks on separate lists of the inode's lock
// context (flc_flock, flc_posix) and checks a request against its own list.
// (NFS, and some other filesystems, make flock emulate fcntl locks; not C.)
func FlockVsOFD(dir string) {
	a, _ := os.OpenFile(dir+"/LOCK", os.O_RDWR|os.O_CREATE, 0o600)
	b, _ := os.OpenFile(dir+"/LOCK", os.O_RDWR, 0o600)
	_ = syscall.Flock(int(a.Fd()), syscall.LOCK_EX|syscall.LOCK_NB)
	lk := syscall.Flock_t{Type: syscall.F_WRLCK}
	_ = syscall.FcntlFlock(b.Fd(), unix.F_OFD_SETLK, &lk) // succeeds too (or any errno)
	a.Close()
	b.Close()
}
