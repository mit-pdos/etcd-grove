//go:build linux

package semantics

import (
	"os"
	"syscall"

	"golang.org/x/sys/unix"
)

// OFD locks: per open file description, whole file, conflicting within one
// process (2026-11-15, the user's approval of lock state; the semantics
// pending review, notes/wal-units/locks.md).
//
// Decision: each fd is its own open file description (no step dups one), and
// the description's OFD lock is a field of it (OsFd.ofd: none, shared, or
// exclusive). fcntl(fd, F_OFD_SETLK, {F_WRLCK or F_RDLCK, whole file}) on a
// description with no OFD lock succeeds only when no other description of the
// file holds a conflicting OFD lock (exclusive against any, shared against
// exclusive), and then the description holds it; it fails with any nonzero
// errno and no change, EAGAIN (= EWOULDBLOCK) only when there is a conflict.
// F_UNLCK releases (success also with no lock). F_WRLCK needs a writable fd,
// F_RDLCK a readable one; the other case is stuck (Linux: EBADF). Re-locking a
// description (the same type or a conversion; Linux accepts both) is stuck:
// etcd never does it. Only whole-file locks with l_pid 0 are modelled (the
// trusted models panic on a byte range, which Linux accepts, and on l_pid not
// 0, which Linux refuses with EINVAL). dup and fork are not modelled: a dup'd
// fd would share the description, and its lock.
//
// Lean: Impl.lean: OsFd.ofd, OsFd.lk, OsFd.setLk, LockConflict, LockStep,
// IsFsStep "OfdLock"; TrustedCode/syscall.lean and
// TrustedCode/golang_org/x/sys/unix.lean: FcntlFlock.impl.
//
// Allowed: below, the second lock fails (EAGAIN or another errno) while the
// first fd is open, and may succeed once it is closed or unlocked.
// Excluded: the second lock succeeding while the first is held; EAGAIN from a
// lock with no conflict.
//
// Why: measured on C (locks_test.go: TestLocksOFDConflict,
// TestLocksOFDRemoveThenClose, TestLocksOFDSameDescription,
// TestLocksOFDMisuse); fs/locks.c: posix_lock_inode returns -EAGAIN only on
// a conflicting lock when the request may not sleep, and inserts the lock
// after its checks and allocations; fs/fcntl.c: check_fmode_for_setlk
// (EBADF), the l_pid check of the OFD commands (EINVAL). etcd's fileutil
// (client/pkg/fileutil/lock_linux.go) takes F_OFD_SETLK/F_OFD_SETLKW write
// locks on the whole file; the WAL and its purger conflict through two opens
// of one segment.
func OFDLocks(dir string) {
	a, _ := os.OpenFile(dir+"/0.wal", os.O_RDWR|os.O_CREATE, 0o600)
	b, _ := os.OpenFile(dir+"/0.wal", os.O_WRONLY, 0o600)
	lk := syscall.Flock_t{Type: syscall.F_WRLCK, Whence: 0, Start: 0, Len: 0}
	_ = syscall.FcntlFlock(a.Fd(), unix.F_OFD_SETLK, &lk) // nil, or an errno and no lock
	lk2 := lk
	_ = syscall.FcntlFlock(b.Fd(), unix.F_OFD_SETLK, &lk2) // if a holds it: an errno (EAGAIN, ...)
	a.Close()                                             // releases a's lock
	lk3 := lk
	_ = syscall.FcntlFlock(b.Fd(), unix.F_OFD_SETLK, &lk3) // may succeed now
	b.Close()
}
