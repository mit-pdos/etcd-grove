//go:build linux

package semantics

import (
	"os"
	"syscall"

	"golang.org/x/sys/unix"
)

// No fd is closed while a lock call on it is in flight (environment
// assumption; 2026-11-19, the user's decision via etcd-grove-03 on the
// attack's finding F1', notes/wal-units/noioerr.md, session 7).
//
// Decision: configuration C's environment includes "the program never closes
// an fd while a flock(2) or fcntl lock command (F_OFD_SETLK, F_OFD_SETLKW) on
// that fd, made by another of its threads, has not returned". The model's
// lock request (Flock, OfdLock) is one step that needs the fd open (FdOpen)
// and, to succeed, no conflicting lock (LockConflict); a close removes the fd
// at once. Not taken: a lock call as begin/end steps with Close stuck while
// one is in flight (a restriction on programs in the semantics itself).
//
// Lean: Impl.lean: the header's "Environment" and "Locks", LockStep's
// docstring, IsFsStep "Close"'s comment; Premises.lean: NoIoErr's docstring
// ("Fds and locks").
//
// Excluded (by the environment, so the model need not describe it): below,
// goroutine T blocks in F_OFD_SETLKW on b while a holds the lock; the main
// goroutine closes b (close returns 0), then closes a; T's call then returns
// 0. The model has no run with that outcome: T's success step needs b open
// (before b's close) and no conflict (after a's close, which follows b's).
// Also excluded: the same with a live mapping of b (the lock lands on the
// description the mapping keeps, MapDesc.held, and outlives the fd), and a
// non-blocking request whose conflict check falls after the close.
// Allowed: everything else; a program that meets the assumption sees each
// lock call return before the close of its fd begins.
//
// Why: measured on C (locks_test.go: TestLocksCloseDuringLock; first by the
// attack, /shared/tmp/walfsfix-attack4/closewait, 4 of 4 cases: flock and
// OFD, the conflict released by close or by unlock): the lock call took its
// own reference to the description at entry (fdget in the flock and fcntl
// system calls), close(2) drops only the fd table's (filp_close), so the
// waiting call takes the lock on the description, returns 0, and the lock
// goes at its fdput (__fput -> locks_remove_file). Who meets it: the WAL
// (fileutil.LockFile and TryLockFile open the file and lock it in one call;
// the *LockedFile, the only way to close it, exists only once the lock call
// has returned) and bbolt (flock in Open before the db is returned, funlock
// in Close before the file's close, on the same goroutine). A program that
// closes a file another goroutine is locking is outside the model.
func NoCloseDuringLock(dir string) {
	a, _ := os.OpenFile(dir+"/0.wal", os.O_RDWR|os.O_CREATE, 0o600)
	lk := syscall.Flock_t{Type: syscall.F_WRLCK}
	_ = syscall.FcntlFlock(a.Fd(), unix.F_OFD_SETLK, &lk)
	b, _ := os.OpenFile(dir+"/0.wal", os.O_RDWR, 0o600)
	fd := b.Fd()
	done := make(chan error)
	go func() {
		lk2 := syscall.Flock_t{Type: syscall.F_WRLCK}
		done <- syscall.FcntlFlock(fd, unix.F_OFD_SETLKW, &lk2) // T: waits for a
	}()
	b.Close() // violates the assumption: T's lock call on b's fd is in flight
	a.Close()
	<-done // on Linux: nil (the model: no run returns nil here)
}
