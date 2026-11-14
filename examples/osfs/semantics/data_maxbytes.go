//go:build linux

package semantics

import (
	"os"
	"syscall"
)

// No byte at or past ext4's s_maxbytes (model decision, 2026-11-14; pending
// the user's review).
//
// Decision: configuration C's largest file size is s_maxbytes = 2^44 - 4096
// = 0xffffffff000 (ext4 with 4 KiB blocks and extent-mapped files). A pwrite
// never lands a byte at or past it: one that starts there lands nothing (on
// Linux, EFBIG), one that crosses it lands at most up to it (on Linux, a short
// count ending at s_maxbytes, page-aligned, errno 0; Go's WriteAt then retries
// at s_maxbytes and returns EFBIG). An ftruncate to a size past it, and a
// fallocate (mode 0) ending past it, fail with no change. A crash never leaves
// a file larger, and no file at the first start is larger. So every file's
// size, and every size it had since its last sync, is at most s_maxbytes.
//
// Lean: Impl.lean: `maxBytes`; PWriteFinish (`k = 0 ∨ off + k ≤ maxBytes`),
// FtruncateFinish and FallocFinish (the resize lands only if
// `c.target ≤ maxBytes`), CrashFile (`sz ≤ maxBytes`), FsInit (`sz ≤
// maxBytes`); the invariant OsWf.sizes (`f.sizeHi ≤ maxBytes`, Ghost.lean);
// what clients see: Write.lean `PwCut` (its second clause: a write's landed
// prefix ends at or below maxBytes) and World.lean `wp_osMeta_size` (any
// `osMeta`'s size, before any step).
//
// Allowed: below, n == 1 with errno 0, then EFBIG with nothing landed;
// ftruncate to maxBytes; EFBIG from the ftruncate and the fallocate past it,
// the size unchanged; any errno with nothing changed, as for every call.
// Excluded: a byte landed at or past maxBytes; a size past it, after a call,
// a failed call, or a crash.
//
// Why: measured on configuration C (models_test.go TestMaxBytes, run by
// run-models-on-c.sh, 2026-11-14, kernel 7.0.0-38: pwrite(100 bytes at
// maxBytes-1) = 1, size maxBytes; pwrite at maxBytes = EFBIG, nothing landed;
// WriteAt(8192 bytes at maxBytes-4196) = (0, EFBIG) with the size maxBytes;
// ftruncate(maxBytes) ok, ftruncate(maxBytes+1) = EFBIG with the size
// unchanged; fallocate(0, maxBytes-4096, 8192) and the same with
// FALLOC_FL_KEEP_SIZE = EFBIG with the size unchanged; fallocate(0,
// maxBytes-4096, 4096) ok; and the earlier sweep of
// notes/axiom-review/bbolt-port-plan-review/, "EFBIG"). From the source:
// ext4_max_size (fs/ext4/super.c) gives (2^32 - 1) << 12 for extent files with
// 4 KiB blocks; generic_write_check_limits (fs/read_write.c) fails a write
// at or past s_maxbytes with EFBIG and truncates one crossing it;
// inode_newsize_ok (fs/attr.c) fails a truncate past it; vfs_fallocate
// (fs/open.c) fails offset + len past it, whatever the mode. A crash cannot
// leave a larger size: the on-disk size is one the inode had. Which client
// needs it: the WAL (notes/wal-fsext-plan.md, W6 log, fourteenth session): its
// tail grows with every SaveSnapshot, which never cuts, so only this bound
// keeps the tail's offsets, stream and segment sizes bounded.
func MaxBytes(dir string) {
	const maxBytes = int64(0xffffffff000)
	f, _ := os.Create(dir + "/f") // a sparse file
	fd := int(f.Fd())
	n, err := syscall.Pwrite(fd, fill(100, 'a'), maxBytes-1)
	// allowed: n == 1, err == nil (cut at maxBytes); nothing landed, any errno
	// excluded: n > 1; any byte landed at maxBytes or past it
	_, err = syscall.Pwrite(fd, fill(100, 'b'), maxBytes)
	// allowed: EFBIG (any errno), nothing landed
	// excluded: success; a byte landed
	err = syscall.Ftruncate(fd, maxBytes+1)
	// allowed: EFBIG (any errno), the size unchanged
	// excluded: success; the size maxBytes+1
	err = syscall.Fallocate(fd, 0, maxBytes-4096, 8192)
	// allowed: EFBIG (any errno), the size unchanged
	// excluded: success; any growth
	_, _ = n, err
	// crash here
	// allowed: a size at most maxBytes; excluded: a larger one
}
