//go:build linux

package semantics

import (
	"os"
	"syscall"

	"golang.org/x/sys/unix"
)

// NoMapLockErr: a client premise, an environment assumption (2026-11-17,
// pending the user's review; mmap's ENOMEM excluded too, 2026-11-17, with
// map_mmap_no_room.go; madvise and open with no free fd, 2026-11-17, session
// S3d, with map_madvise.go), beside NoIoErr (premise_no_io_err.go).
//
// Decision: not part of the semantics. A theorem may assume, of its steps, that
// flock, mmap and munmap on a chosen set of files (IoSet, by inode at the
// step) return no error of the environment whenever the semantics lets them:
// flock succeeds where it can (no conflicting lock; LOCK_UN always), and a
// non-blocking one that cannot fails with EWOULDBLOCK only; mmap never fails
// (it returns a mapping, or, with no room left for it in (0, maxAddr], does
// not return: map_mmap_no_room.go); munmap of a whole mapping succeeds (and
// unmaps); madvise with a paging hint of a mapping of the file succeeds
// (map_madvise.go). And an open of a covered path (IoSet, by path) from a
// state with no free fd fails with EINTR, never EMFILE or another errno:
// every model of open retries EINTR (TrustedCode/os.lean: OpenFile.impl,
// model.stat, model.openLoop), so the Go call does not return, as an mmap
// with no room or an allocation with no free range. The
// semantics alone lets each of them fail with any errno (locks_flock.go; Impl.lean's
// "Mmap" and "Munmap", where a failing munmap may or may not have unmapped);
// NoIoErr deliberately does not name them.
//
// Lean: Premises.lean: MapLockCovers, MapLockOk (for mmap: errno 0 or the
// step to itself, MmapStall; for open with no free fd: EINTR, or errno 0,
// which the semantics has not there), NoMapLockErr (a premise on steps, a filter of
// fsSemWithS); NoMapLockErr.lean: noMapLockErr_keeps (it keeps a step from
// every state the semantics steps from: for a failing mmap, the success where
// the heap has room, heapRendered_map, the stall where it has none),
// noIoErr_noMapLockErr_keeps (with NoIoErr, StepPrem.and: they name disjoint
// steps but open with no free fd, where the semantics has no success, so
// NoIoErr says nothing, and its EINTR is kept: isFsStep_open_eintr);
// NoMapLockErrSpecs.lean: mmap_noFail, wp_osMmapNE; Madvise.lean:
// wp_osMadviseNE; NoErrSpecsOpenFile.lean: open_failure_eintr,
// wp_osOpenCreateSNE, wp_osOpenFileSNE (Spec/os/OpenFileSNoErr.lean:
// os.OpenFile.specCreateSNoErr, no error).
//
// Excluded under the premise, on a covered file: flock(LOCK_EX|LOCK_NB) failing
// with ENOLCK, EINTR or any errno but EWOULDBLOCK, or with EWOULDBLOCK when no
// other description holds a conflicting lock; flock(LOCK_UN) failing; mmap
// (PROT_READ, MAP_SHARED) failing with ENOMEM, EAGAIN, ENFILE, ENODEV,
// EOVERFLOW, EPERM or any errno; munmap failing; madvise(MADV_RANDOM) of a
// mapping failing (EAGAIN, ENOMEM, ...); on a covered path with no free fd,
// open failing with EMFILE (or any errno but EINTR).
//
// Still allowed (the semantics has no success there): a blocking flock on a
// conflict (it fails, or waits); an mmap that does not return when no room is
// left in the address space (the mappings and the Go heap share (0, maxAddr];
// a premise on steps sees the extension's state but not the heap, and the
// stall, a step of the semantics that sees the heap, is the step it keeps from
// a state with no room: StepKeeps). Under the premise bbolt's Open makes no
// mmap error; out of address space it does not return, as a Go allocation.
//
// Why: etcd's backend panics when bolt.Open fails (backend.go: "cannot open
// database") and applySnapshot when the old backend's Close fails; bbolt's
// Open calls open, flock, mmap and madvise, its Close munmap and
// flock(LOCK_UN). With these calls allowed to fail the panics are reachable,
// and the server's theorems need an assumption excluding them; this one
// assumes only what the environment does.
//
// Out of descriptors: the model's fds are any nonnegative int64 not in use,
// and open fails with no free fd only once all 2^63 are taken; NoIoErr
// already asks a covered open to succeed wherever the model has a free fd, so
// it already assumes Linux's EMFILE at RLIMIT_NOFILE (open(2), man-pages 6.9:
// "EMFILE The per-process limit on the number of open file descriptors has
// been reached") does not happen on a covered path. What this clause adds is
// the model's own exhaustion, which takes 2^63 opens without a close, more
// steps than any execution a theorem covers (receiptBound); there the model's
// open has no success, and the premise keeps EINTR (a step it always has),
// which the Go models retry: the call does not return, fd exhaustion treated as
// memory exhaustion (outside the model).
// Evidence: assumed (no claim that Linux on configuration C behaves so: kernel
// memory exhaustion, the map count vm.max_map_count, RLIMIT_AS, RLIMIT_NOFILE,
// a sealed memfd or a file system without mmap violate it).
func NoMapLockErrPremise(dir string) {
	f, _ := os.OpenFile(dir+"/db", os.O_RDWR|os.O_CREATE, 0o600)
	f.Truncate(1 << 16)
	if err := syscall.Flock(int(f.Fd()), syscall.LOCK_EX|syscall.LOCK_NB); err != nil && err != syscall.EWOULDBLOCK {
		// the semantics: reachable; under the premise (f's inode covered): excluded
		panic(err)
	}
	b, err := unix.Mmap(int(f.Fd()), 0, 1<<16, unix.PROT_READ, unix.MAP_SHARED)
	if err != nil {
		// the semantics: reachable (any errno, ENOMEM included); under the
		// premise: excluded (with no room, the call does not return instead)
		panic(err)
	}
	if err == nil {
		if err := unix.Madvise(b, syscall.MADV_RANDOM); err != nil {
			// the semantics: reachable (map_madvise.go); under the premise: excluded
			panic(err)
		}
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
	var fs []*os.File
	for i := 0; i < 1<<20; i++ {
		g, err := os.OpenFile(dir+"/db", os.O_RDWR|os.O_CREATE, 0o600)
		if err != nil {
			// Linux: EMFILE at RLIMIT_NOFILE (excluded on a covered path by NoIoErr
			// while the model has a free fd); the model's own exhaustion (all 2^63
			// fds): under the premise the call does not return (EINTR, retried)
			panic(err)
		}
		fs = append(fs, g)
	}
	for _, g := range fs {
		g.Close()
	}
}
