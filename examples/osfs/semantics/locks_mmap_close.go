//go:build linux

package semantics

import (
	"os"
	"syscall"

	"golang.org/x/sys/unix"
)

// A live mapping keeps its open file description, and the description's
// locks, alive after the fd's close, until the last mapping made through it is
// unmapped (2026-11-19, the user's approval via etcd-grove-03, after the attack
// F1 on NoIoErr's lock coverage: notes/wal-units/noioerr.md, sessions 4-6).
//
// Decision: each mapping holds the description it was made through
// (ProcState.mapDesc: MapDesc.live fd while the fd is open; Close turns it into
// MapDesc.held d, the description as it was at the close, locks included);
// Munmap removes it with the mapping; LockConflict counts the locks of a held
// description like another fd's. Close is never stuck and frees the fd
// whatever happens; without a live mapping of it, the description and its
// locks go as before (locks_close_crash.go).
//
// Lean: Impl.lean: MapDesc, MapDesc.close, ProcState.mapDesc, IsFsStep
// "Close"/"Mmap"/"Munmap", LockConflict; Locks.lean: wp_osClose (the lock
// tokens are spent: no token stands for a held description's locks).
//
// Allowed: below, b's requests fail with EAGAIN (non-blocking) while m1 or m2
// is mapped, and succeed after both are unmapped.
// Excluded: b's exclusive OFD or flock lock succeeding after a.Close() while a
// mapping made through a is live (the model before 2026-11-19 allowed it:
// Close released the locks).
//
// Why: measured on C (locks_test.go: TestLocksMmapKeepsDescription, OFD and
// flock, with two mappings, unmapped one at a time); fs/locks.c:
// locks_remove_file runs from __fput when the description's last reference
// goes, and mmap takes a reference on the struct file (vma->vm_file,
// get_file in mmap_region, fs/mm), dropped when the vma goes (remove_vma:
// fput); close(2) drops only the fd table's reference (filp_close:
// locks_remove_posix removes classic POSIX locks only, whose owner is the fd
// table, not OFD or flock locks, whose owner is the description).
func LocksMmapClose(dir string) {
	a, _ := os.OpenFile(dir+"/f", os.O_RDWR|os.O_CREATE, 0o600)
	a.Write([]byte("hello"))
	lk := syscall.Flock_t{Type: syscall.F_WRLCK}
	_ = syscall.FcntlFlock(a.Fd(), unix.F_OFD_SETLK, &lk)
	m1, _ := syscall.Mmap(int(a.Fd()), 0, 5, syscall.PROT_READ, syscall.MAP_SHARED)
	m2, _ := syscall.Mmap(int(a.Fd()), 0, 5, syscall.PROT_READ, syscall.MAP_SHARED)
	a.Close() // the description lives on in m1 and m2, with its lock
	b, _ := os.OpenFile(dir+"/f", os.O_RDWR, 0o600)
	_ = syscall.FcntlFlock(b.Fd(), unix.F_OFD_SETLK, &lk) // EAGAIN
	syscall.Munmap(m1)
	_ = syscall.FcntlFlock(b.Fd(), unix.F_OFD_SETLK, &lk) // EAGAIN: m2 holds it
	syscall.Munmap(m2)
	_ = syscall.FcntlFlock(b.Fd(), unix.F_OFD_SETLK, &lk) // succeeds (or any errno but EAGAIN)
	b.Close()
}
