//go:build linux

package semantics

import (
	"os"
	"syscall"
)

// Short reads and writes, and what a failed one did (model decision; audit F4,
// F6).
//
// Decision: every system call may fail with any nonzero errno. A pread that
// succeeds returns a non-empty prefix of what it asked for (or nothing at
// EOF); a failed one returns any prefix with its errno (the os model's ReadAt
// copies it, uncounted). A pwrite that succeeds writes all of its
// data or a non-empty prefix (a short write with errno 0); a failed one may
// have written any prefix, none included.
//
// Lean: Impl.lean: the PRead step (ReadSees, a prefix), PWriteFinish
// (`(k = data.length ∨ 0 < k) ∧ e = 0 ∨ e ≠ 0`, `k ≤ data.length`); the
// header's "Environmental failure"; notes/axiom-review/fs-v2.md, F4 and F6.
//
// Allowed: n < len(buf) with err == nil; a short write with err == nil; a
// failed write whose prefix landed; a failed read that returned a prefix.
// Excluded: a successful read past what the file holds.
//
// Why: documented (read(2), write(2): "the number of bytes ... may be less
// than count"; ENOSPC partway through a write returns the count written).
// Go's File.ReadAt and File.WriteAt loop over short counts, which is why the
// trusted models of `os` loop too.
func ShortIO(dir string) {
	f, _ := os.Create(dir + "/f")
	fd := int(f.Fd())
	n, err := syscall.Pwrite(fd, fill(8192, 'x'), 0)
	// allowed: n == 8192, err == nil; 0 < n < 8192, err == nil;
	//          n == 0 or -1, err != nil, with any prefix of the data landed
	_, _ = n, err
	buf := make([]byte, 8192)
	m, err := syscall.Pread(fd, buf, 0)
	// allowed: 0 < m <= 8192 (a prefix), err == nil; err != nil with any
	//          prefix of the file copied into buf
	_, _ = m, err
}
