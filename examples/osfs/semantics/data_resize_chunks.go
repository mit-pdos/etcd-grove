//go:build linux

package semantics

import (
	"os"
	"syscall"
)

// A failed or interrupted fallocate or truncate may leave any size between
// (model decision, audit F5).
//
// Decision: a change of a file's size lands, at a failure or a crash, as any
// size between the file's size and the target, not only all or nothing.
//
// Lean: Impl.lean: CrashFile (a size between the sizes since the last sync and
// an in-flight change's target), the FallocFinish step's failure branch (any
// `sz'` between); OsChange.ofResize (the grown bytes' candidate, zero), OsFile.land;
// notes/axiom-review/fs-v2.md, F5.
//
// Allowed: after a failure (or a crash during the call) below, any size in
// [4096, 1<<20], zero-filled past 4096.
// Excluded: a size outside that range; non-zero bytes past 4096.
//
// Why: documented in the source: ext4's fallocate (ext4_alloc_file_blocks,
// fs/ext4/extents.c, v6.12) allocates chunk by chunk, each in its own journal
// handle, and updates the size after each chunk, so ENOSPC partway leaves an
// intermediate size, and so does a crash between handles. etcd's WAL
// preallocates every segment (fileutil.Preallocate with extendFile=true:
// fallocate mode 0).
func ResizeChunks(dir string) {
	f, _ := os.Create(dir + "/f")
	f.Truncate(4096)
	f.Sync()
	if err := syscall.Fallocate(int(f.Fd()), 0, 0, 1<<20); err != nil {
		// allowed: size anywhere in [4096, 1<<20], zeros past 4096
		return
	}
	// crash here, during the call: the same range
}
