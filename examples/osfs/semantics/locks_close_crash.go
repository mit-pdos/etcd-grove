//go:build linux

package semantics

import (
	"os"
	"syscall"

	"golang.org/x/sys/unix"
)

// Locks go with their description: released at its close and at a crash
// (2026-11-15, pending review, notes/wal-units/locks.md).
//
// Decision: the locks are fields of the description (OsFd), so the Close step,
// which removes the fd's entry, releases them when no live mapping made
// through the fd holds the description (with one, the description and its
// locks live until the last such mapping goes: locks_mmap_close.go, since
// 2026-11-19), and a crash, which empties the process's state, releases every
// lock; a program starts with none.
//
// Lean: Impl.lean: OsFd.ofd/flk, IsFsStep "Close", MachineCrash
// (st'.proc = ProcState.empty), FsInit.
//
// Allowed: below, after the crash the restarted program's lock succeeds (or
// fails with an errno).
// Excluded: a lock surviving a crash, or its fd's close when no mapping made
// through the fd is live.
//
// Why: measured on C (locks_test.go: TestLocksOFDConflict and TestLocksFlock:
// closing the holder's only fd releases its lock; TestLocksOFDRemoveThenClose:
// also after its name is removed, the purger's order); fs/locks.c:
// locks_remove_file, from __fput when the description's last reference goes
// (task work run before close(2) returns to user space; a mapping holds a
// reference too, locks_mmap_close.go); locks are kernel
// memory, never written to disk, and a process's exit closes its fds
// (env_restarts.go: a restart is a machine crash).
func LocksCloseCrash(dir string) {
	a, _ := os.OpenFile(dir+"/0.wal", os.O_RDWR|os.O_CREATE, 0o600)
	lk := syscall.Flock_t{Type: syscall.F_WRLCK}
	_ = syscall.FcntlFlock(a.Fd(), unix.F_OFD_SETLK, &lk)
	// crash here: after the restart, nothing holds the lock
	a.Close() // or: released here
}
