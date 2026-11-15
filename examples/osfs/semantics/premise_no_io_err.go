//go:build linux

package semantics

import (
	"os"
)

// NoIoErr: a client premise, an environment assumption (approved by the user,
// 2026-11-15).
//
// Decision: not part of the semantics. A theorem may assume, of its steps, that
// the calls on a chosen set of files and paths have no I/O error: whenever the
// semantics lets the call succeed from the state it is made in, it succeeds.
// The set (IoSet) names files by inode at the step (for the calls on an fd or a
// change's token) and paths by the call's own argument (for the calls on a
// path). The semantics alone lets every one of these calls fail with any errno
// (data_failed_fsync.go, data_short_io.go, ...); the premise removes those
// failures for the covered files only.
//
// Lean: Premises.lean: IoSet, IoCovers, ErrnoZero, NoIoErr (the premise on
// steps, a filter of fsSemWithS); NoIoErr.lean: noIoErr_keeps (it keeps a step
// from every state the semantics steps from, so the restriction is not
// vacuous); NoIoErrSpecs.lean: the error-free specs of the operations over it.
//
// Excluded under the premise, on a covered file: fsync/fdatasync failing (EIO,
// ENOSPC, EDQUOT); a pwrite ending with an errno (EIO, ENOSPC, EDQUOT, EINTR)
// where at least one byte could land (offset below maxBytes); ftruncate or
// fallocate failing on a size up to maxBytes; fstat, pread or close failing;
// fsync or close of a covered directory failing; open, rename, mkdir, unlink
// or rmdir of a covered path failing where the call can succeed (the path
// resolves as the call needs; a free fd for open).
//
// Still allowed under the premise (the semantics has no success there): EFBIG
// at or past maxBytes (data_maxbytes.go), EMFILE with no free fd, the failures
// of a path call that cannot succeed in the state it is made in (ENOENT,
// EEXIST, ENOTEMPTY, EISDIR, ...), and anything on a call the premise does not
// name: flock and the OFD lock (the lock calls), mmap/munmap, fallocate with
// KEEP_SIZE, lstat, the directory reads, the calls on a directory above a root.
// Short writes and short reads with errno 0 stay too: they are no error, and
// Go's loops retry them.
//
// Why: etcd's server calls lg.Panic when certain WAL operations fail (Create,
// the apply thread's SaveSnapshot and ReleaseLockTo, applySnapshot's
// ReleaseLockTo, onStop's Close, Reopen). With every system call allowed to
// fail, those panics are reachable, and the server's no-panic theorem needs an
// assumption excluding them. "No panic at these sites" would assume the
// conclusion; this premise assumes only what the environment does: the device
// returns no I/O error and the filesystem has room for these files.
// Evidence: assumed (no claim that Linux on configuration C behaves so; a full
// disk or a failing device violates it, and then etcd does panic).
func NoIoErrPremise(dir string) {
	f, _ := os.Create(dir + "/0.wal")
	f.Truncate(64 * 1024 * 1024)
	f.WriteAt(fill(512, 'R'), 0)
	if err := f.Sync(); err != nil {
		// the semantics: reachable (fsync may fail: EIO, ENOSPC)
		// under the premise (dir's files covered): excluded, Sync returns nil
		panic(err)
	}
	f.Close()
}
