//go:build linux

package semantics

import (
	"os"
	"syscall"

	"golang.org/x/sys/unix"
)

// NoMapLockErr: a client premise, an environment assumption (2026-11-17,
// pending the user's review), beside NoIoErr (premise_no_io_err.go).
//
// Decision: not part of the semantics. A theorem may assume, of its steps, that
// flock, mmap and munmap on a chosen set of files (IoSet, by inode at the
// step) return no error of the environment whenever the semantics lets them:
// flock succeeds where it can (no conflicting lock; LOCK_UN always), and a
// non-blocking one that cannot fails with EWOULDBLOCK only; mmap succeeds or
// fails with ENOMEM only; munmap of a whole mapping succeeds (and unmaps). The
// semantics alone lets each of them fail with any errno (locks_flock.go; Impl.lean's
// "Mmap" and "Munmap", where a failing munmap may or may not have unmapped);
// NoIoErr deliberately does not name them.
//
// Lean: Premises.lean: MapLockCovers, MapLockOk, ENOMEM, NoMapLockErr (a
// premise on steps, a filter of fsSemWithS); NoMapLockErr.lean:
// noMapLockErr_keeps (it keeps a step from every state the semantics steps
// from), noIoErr_noMapLockErr_keeps (with NoIoErr, StepPrem.and).
//
// Excluded under the premise, on a covered file: flock(LOCK_EX|LOCK_NB) failing
// with ENOLCK, EINTR or any errno but EWOULDBLOCK, or with EWOULDBLOCK when no
// other description holds a conflicting lock; flock(LOCK_UN) failing; mmap
// (PROT_READ, MAP_SHARED) failing with EAGAIN, ENFILE, ENODEV, EOVERFLOW, EPERM
// or any errno but ENOMEM; munmap failing.
//
// Still allowed (the semantics has no success there, or the premise cannot
// say): a blocking flock on a conflict; mmap's ENOMEM. The mappings and the Go
// heap share the address space (0, maxAddr], and a premise on steps sees the
// extension's state but not the heap: it cannot say when the address space has
// room, and excluding ENOMEM would leave no step from a state where it has none
// (StepKeeps). bbolt's Open therefore may still fail with an mmap ENOMEM under
// the premise.
//
// Why: etcd's backend panics when bolt.Open fails (backend.go: "cannot open
// database") and applySnapshot when the old backend's Close fails; bbolt's
// Open calls flock and mmap, its Close munmap and flock(LOCK_UN). With these
// calls allowed to fail the panics are reachable, and the server's theorems
// need an assumption excluding them; this one assumes only what the
// environment does.
// Evidence: assumed (no claim that Linux on configuration C behaves so: kernel
// memory exhaustion, a sealed memfd or a file system without mmap violate it).
func NoMapLockErrPremise(dir string) {
	f, _ := os.OpenFile(dir+"/db", os.O_RDWR|os.O_CREATE, 0o600)
	f.Truncate(1 << 16)
	if err := syscall.Flock(int(f.Fd()), syscall.LOCK_EX|syscall.LOCK_NB); err != nil && err != syscall.EWOULDBLOCK {
		// the semantics: reachable; under the premise (f's inode covered): excluded
		panic(err)
	}
	b, err := unix.Mmap(int(f.Fd()), 0, 1<<16, unix.PROT_READ, unix.MAP_SHARED)
	if err != nil && err != unix.ENOMEM {
		// the semantics: reachable; under the premise: excluded (ENOMEM stays)
		panic(err)
	}
	if err == nil {
		if err := unix.Munmap(b); err != nil {
			// the semantics: reachable (and the mapping may stay); under the premise: excluded
			panic(err)
		}
	}
	if err := syscall.Flock(int(f.Fd()), syscall.LOCK_UN); err != nil {
		// the semantics: reachable; under the premise: excluded
		panic(err)
	}
	f.Close()
}
