//go:build linux

package semantics

import (
	"os"
	"syscall"

	"golang.org/x/sys/unix"
)

// madvise with a paging hint is a step of the extension: no visible change,
// any errno (2026-11-17, session S3d, pending the user's review).
//
// Decision: unix.Madvise(b, advice) with advice MADV_NORMAL (0), MADV_RANDOM
// (1), MADV_SEQUENTIAL (2) or MADV_WILLNEED (3) is the extension's Madvise
// operation on (&b[0], len(b), advice): it changes nothing the model tracks (a
// hint changes no byte a load of a mapped cell or a pread sees) and returns
// any errno, 0 included. An empty b (where Go passes a pointer to a zero byte
// of its own) returns an arbitrary errno with no step, as before; any other
// advice is stuck (the model panics: some change memory). Until this decision
// the trusted model (TrustedCode/golang_org/x/sys/unix.lean, Madvise.impl)
// returned an arbitrary errno without a step of the extension; the outcomes are
// the same, but as a step its errno can be constrained by a premise on steps
// (NoMapLockErr: no error for a mapping of a covered file,
// premise_no_map_lock_err.go).
//
// Lean: Impl.lean: the "Madvise" case of IsFsStep (st' = st, e' = #e for any
// e); World.lean: DataOp (the tree left alone); unix.lean: Madvise.impl;
// GooseLang/Ext/Fs/Madvise.lean: wp_osMadvise, wp_osMadviseNE.
//
// Allowed: any errno from any madvise with a paging hint (EAGAIN, EINVAL,
// ENOMEM, EIO, EBADF, ...), nothing changed. Excluded: a change of any byte or
// mapping (Linux's paging hints change neither: mm/madvise.c, madvise_behavior
// sets VM_RAND_READ/VM_SEQ_READ flags of the vma, and MADV_WILLNEED starts
// readahead of the file's pages, which changes no page-cache value).
//
// Why: bbolt's mmap (bolt_unix.go) calls unix.Madvise(b, MADV_RANDOM) after
// unix.Mmap and returns an error when it fails (but ENOSYS), leaking the
// mapping; Open then fails, and a later Close cannot give the file back. With
// madvise a step, NoMapLockErr can exclude its failure on the database file.
//
// Evidence: documented. madvise(2) (man-pages 6.9): "EAGAIN A kernel resource
// was temporarily unavailable. EBADF The map exists, but the area maps
// something that isn't a file. EINVAL addr is not page-aligned or length is
// negative. ... EIO (for MADV_WILLNEED) Paging in this area would exceed the
// process's maximum resident set size. ENOMEM (for MADV_WILLNEED) Not enough
// memory: paging in failed. ENOMEM Addresses in the specified range are not
// currently mapped"; Linux 7.0 mm/madvise.c, madvise_update_vma: -ENOMEM when
// splitting the vma fails.
func MadviseHint(dir string) {
	f, _ := os.OpenFile(dir+"/db", os.O_RDWR|os.O_CREATE, 0o600)
	f.Truncate(1 << 16)
	b, err := unix.Mmap(int(f.Fd()), 0, 1<<16, unix.PROT_READ, unix.MAP_SHARED)
	if err != nil {
		return
	}
	if err := unix.Madvise(b, syscall.MADV_RANDOM); err != nil {
		// the semantics: reachable (any errno), the mapping and the bytes unchanged;
		// under NoMapLockErr (f's inode covered): excluded
		_ = err
	}
	_ = b[0] // the file's first byte, as before the call
	unix.Munmap(b)
	f.Close()
}
