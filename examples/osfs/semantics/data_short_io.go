//go:build linux

package semantics

import (
	"os"
	"syscall"
)

// Short reads and writes, what a failed one did, and page cuts (model
// decision; audit F4, F6; the page-cut rule, notes/bbolt-port-plan.md).
//
// Decision: every system call may fail with any nonzero errno. A pread that
// succeeds returns a non-empty prefix of what it asked for (or nothing at
// EOF); a failed one returns any prefix with its errno (the os model's ReadAt
// copies it, uncounted). A pwrite that succeeds writes all of its data or a
// non-empty prefix (a short write with errno 0); a failed one may have
// written a prefix, none included. Whatever the errno, the prefix a pwrite
// landed is empty, all of the data, or ends on a 4096-byte page boundary of
// the file ("page cuts").
//
// Lean: Impl.lean: the PRead step (ReadSees, a prefix), PWriteFinish
// (`(k = data.length ∨ 0 < k) ∧ e = 0 ∨ e ≠ 0`, `k ≤ data.length`,
// `k = 0 ∨ k = data.length ∨ (off + k) % osPageSize = 0`); the header's
// "Environmental failure" and "Page cuts"; Tests.lean `pwrite_page_cut`.
//
// Allowed: n < len(buf) with err == nil; a short write with err == nil ending
// on a page boundary; a failed write whose landed prefix is a page cut; a
// failed read that returned a prefix.
// Excluded: a successful read past what the file holds; a pwrite returning
// (or a failed one having landed) a prefix that ends inside a page, unless it
// is the whole write.
//
// Why: documented (read(2), write(2): "the number of bytes ... may be less
// than count"). Page cuts: measured on configuration C
// (notes/axiom-review/bbolt-port-plan-review/: under ENOSPC on a nearly full
// filesystem, swept over free-block counts, and EFBIG at s_maxbytes, 19 of 19
// short counts ended on a page boundary, 20 of 20 errno returns landed
// nothing, and 19 Go-level (0, err) results had a page-cut prefix landed);
// from the source, ext4's write loop stops only before a folio, and folios
// are page-aligned. What cuts inside a page is excluded: a limited
// RLIMIT_FSIZE (C: unlimited; measured mid-page), a source page that cannot
// be faulted in (assumed: every page of the source can be faulted in; a
// memory-cgroup OOM gives EFAULT after progress, measured mid-page with an
// unreadable source page; every client's source is a heap buffer), and an
// allocation failure in the write path after a short copy (assumed: no
// allocation failure in the write path; a short copy during a page migration
// then ENOMEM in write_begin stops mid-page; from the kernel source, not
// measured).
// This is a rule of the call's result: a process killed during the copy can
// leave a mid-page prefix in the page cache, which a crash's per-byte rule
// covers. Go's File.ReadAt and File.WriteAt loop over short counts, which is
// why the trusted models of `os` loop too; bbolt relies on the page cut for a
// one-page meta write (all or nothing in the process).
func ShortIO(dir string) {
	f, _ := os.Create(dir + "/f")
	fd := int(f.Fd())
	n, err := syscall.Pwrite(fd, fill(8192, 'x'), 0)
	// allowed: n == 8192, err == nil; n == 4096, err == nil;
	//          n == 0 or -1, err != nil, with 0, 4096 or 8192 bytes landed
	// excluded: n == 5000, err == nil; err != nil with 5000 bytes landed
	_, _ = n, err
	buf := make([]byte, 8192)
	m, err := syscall.Pread(fd, buf, 0)
	// allowed: 0 < m <= 8192 (a prefix), err == nil; err != nil with any
	//          prefix of the file copied into buf
	_, _ = m, err
}
