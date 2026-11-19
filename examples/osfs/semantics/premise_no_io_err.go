//go:build linux

package semantics

import (
	"os"
	"syscall"

	"golang.org/x/sys/unix"
)

// NoIoErr: a client premise, an environment assumption (approved by the user,
// 2026-11-15; the lock requests and the directory reads added with the user's
// approval of 2026-11-19, option (a) of notes/wal-units/noioerr.md).
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
// resolves as the call needs; a free fd for open). Since 2026-11-19 also: a
// lock request on a covered file (flock LOCK_SH/LOCK_EX, with or without
// LOCK_NB, or fcntl F_OFD_SETLK/F_OFD_SETLKW with F_RDLCK/F_WRLCK) failing
// although no other fd of the process holds a conflicting lock (ENOLCK,
// EINTR, ...), an unlock (LOCK_UN, F_UNLCK) failing; a step of Readdirnames
// (getdents64) on a covered directory failing with an errno other than ENOENT
// (EIO, ...) while the directory has a name left to return or is at its end.
// Lean: IoCovers "Flock", "OfdLock" (an fd of a covered inode), "DirReadNext"
// (a directory fd of a covered inode); ErrnoZero "DirReadNext" (errno 0, or
// ENOENT: a removed directory, meta_enoent.go, is no I/O error).
//
// Still allowed under the premise (the semantics has no success there): EFBIG
// at or past maxBytes (data_maxbytes.go), EMFILE with no free fd, the failures
// of a path call that cannot succeed in the state it is made in (ENOENT,
// EEXIST, ENOTEMPTY, EISDIR, ...), a lock request that conflicts with a lock
// another fd of the process holds (EAGAIN, or for a blocking request any
// errno: locks_blocking.go), ENOENT from a read of a removed directory, and
// anything on a call the premise does not name: mmap/munmap, fallocate with
// KEEP_SIZE, lstat (LstatDir: its outcome does not tell a failed lstat of a
// directory from a non-directory, so it has no success to name), the model's
// queries PathKind and FdKind (one answer from each state: nothing to
// exclude), the calls on a directory above a root. Short writes and short
// reads with errno 0 stay too: they are no error, and Go's loops retry them.
//
// Why: etcd's server calls lg.Panic when certain WAL operations fail (Create,
// the apply thread's SaveSnapshot and ReleaseLockTo, applySnapshot's
// ReleaseLockTo, onStop's Close, Reopen). With every system call allowed to
// fail, those panics are reachable, and the server's no-panic theorem needs an
// assumption excluding them. "No panic at these sites" would assume the
// conclusion; this premise assumes only what the environment does: the device
// returns no I/O error and the filesystem has room for these files.
// Evidence: assumed (no claim that Linux on configuration C behaves so; a full
// disk or a failing device violates it, and then etcd does panic). For the lock
// requests and the reads, the further assumptions: the kernel has memory for a
// lock record (fs/locks.c: posix_lock_inode and flock_lock_inode allocate it,
// ENOLCK when that fails) and for a read's buffer, no other process locks the
// covered files (the lock rule already takes the roots' files to be the
// process's own, locks_ofd.go), and no fatal signal is pending (iterate_dir's
// killable lock, EINTR). An uncontended request does not sleep, so no signal
// can interrupt it (fs/locks.c: the wait is only on a conflict). Measured on
// C, as support only (premise_no_io_err_test.go, run by run-models-on-c.sh):
// uncontended OFD (F_OFD_SETLKW) and flock (LOCK_EX) locks and their unlocks,
// and the Readdirnames of a small directory, succeed every time over many
// rounds.
//
// Why the locks and the reads (2026-11-19): wal.Create locks its first segment
// (fileutil.LockFile: F_OFD_SETLKW) and reads its fresh temporary directory
// (fileutil.CreateDirAll: ReadDir), WAL.cut locks its new tail; with those
// calls free to fail, Create's and cut's errors, on which etcd panics, were not
// excluded (notes/wal-units/noioerr.md, "Blocked").
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

// NoIoErrLocksReads: the lock request and the directory read under the
// premise (dir's files covered).
func NoIoErrLocksReads(dir string) {
	os.Mkdir(dir+"/wal.tmp", 0o700)
	d, _ := os.Open(dir + "/wal.tmp")
	if _, err := d.Readdirnames(-1); err != nil {
		// the semantics: reachable (getdents64 may fail: EIO, ENOMEM, ...)
		// under the premise: excluded (the directory is not removed: no ENOENT)
		panic(err)
	}
	d.Close()
	f, _ := os.OpenFile(dir+"/wal.tmp/0.wal", os.O_WRONLY|os.O_CREATE, 0o600)
	lk := syscall.Flock_t{Type: syscall.F_WRLCK, Whence: 0, Start: 0, Len: 0}
	if err := syscall.FcntlFlock(f.Fd(), unix.F_OFD_SETLKW, &lk); err != nil {
		// the semantics: reachable (any errno, e.g. ENOLCK)
		// under the premise: excluded (no other fd of the file holds a lock)
		panic(err)
	}
	g, _ := os.OpenFile(dir+"/wal.tmp/0.wal", os.O_WRONLY, 0o600)
	lk2 := lk
	if err := syscall.FcntlFlock(g.Fd(), unix.F_OFD_SETLK, &lk2); err == nil {
		// excluded by the lock rule (f holds a conflicting lock), premise or not
		panic("second lock")
	} // still allowed under the premise: EAGAIN (a conflict, no success)
	g.Close()
	f.Close()
}
