//go:build linux

package semantics

import (
	"os"
	"syscall"

	"golang.org/x/sys/unix"
)

// syscall.FcntlFlock: the lock commands as unix.FcntlFlock, and the
// F_OFD_GETLK query on any fd (trusted model; a draft pending review,
// 2026-11-13).
//
// Decision: F_SETLK, F_SETLKW, F_OFD_SETLK and F_OFD_SETLKW are the
// extension's OfdLock (any errno, no lock state; stuck on an fd that is not a
// file's), as unix.FcntlFlock's model. F_OFD_GETLK, on any fd (one the process
// opened or not), takes no extension step and returns nil or any errno; on
// success it writes arbitrary values into the description's Type, Whence,
// Start, Len and Pid (Linux writes F_UNLCK, or the conflicting lock), and
// leaves its padding as it was; on failure the description is unchanged. A
// nil description is stuck (Linux: EFAULT). Other commands panic (not
// modelled). The lock state stays unmodelled (the user's decision is pending,
// notes/wal-fsext-plan.md Q1).
//
// Lean: LinuxFs/TrustedCode/syscall.lean: FcntlFlock.impl, model.Flock_t;
// Impl.lean: OfdLock.
//
// Allowed: below, fileutil's choice of OFD locks or flock either way.
// Excluded: nothing a Linux run does: a query changes no state.
//
// Why: documented (fcntl(2): F_OFD_GETLK "If the lock could be placed, fcntl()
// does not actually place it, but returns F_UNLCK in the l_type field of lock
// and leaves the other fields of the structure unchanged"; otherwise it
// describes the conflicting lock, l_pid -1; EBADF on a fd that is not open)
// and measured (TestOFDGetlk: on a closed fd, EBADF; on /dev/null and on a
// regular file, nil with Type F_UNLCK; TestOFDGetlkPadding: the padding bytes
// are unchanged). etcd's fileutil runs this query in its package initializer
// on fd 0 (client/pkg/fileutil/lock_linux.go:46-52), whatever fd 0 is, so the
// model cannot require an fd it knows.
func OFDGetlk(dir string) {
	getlk := syscall.Flock_t{Type: syscall.F_RDLCK}
	if err := syscall.FcntlFlock(0, unix.F_OFD_GETLK, &getlk); err == nil {
		// fileutil uses OFD locks
	}
	f, _ := os.Create(dir + "/LOCK")
	lk := syscall.Flock_t{Type: syscall.F_WRLCK}
	syscall.FcntlFlock(f.Fd(), unix.F_OFD_SETLK, &lk) // any errno
	f.Close()
}
