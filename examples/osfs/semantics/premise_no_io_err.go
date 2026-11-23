//go:build linux

package semantics

import (
	"errors"
	"os"
	"syscall"

	"golang.org/x/sys/unix"
)

// NoIoErr: a client premise, an environment assumption (approved by the user,
// 2026-11-15; the lock requests and the directory reads added with the user's
// approval of 2026-11-19, option (a) of notes/wal-units/noioerr.md; narrowed to
// the blocking lock requests and to the paths that fit, the user's decisions of
// 2026-11-19 after the attack on F1's fix, noioerr.md session 7).
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
// or rmdir of a covered path that fits (shorter than 4096 bytes, no component
// longer than 255: PathFits) failing where the call can succeed (the path
// resolves as the call needs; the model always has a free fd for open, so
// EMFILE and ENFILE are excluded too, which the environment's fd limits make
// true: env_config.go, TestNoIoErrEmfile). Since 2026-11-19 also: a
// blocking OFD lock request on a covered file (fcntl F_OFD_SETLKW with
// F_RDLCK/F_WRLCK) failing although no
// other description holds a conflicting lock (another fd's, or one a live
// mapping keeps after its fd's close, locks_mmap_close.go; ENOLCK, EINTR,
// ...), a blocking OFD unlock (F_OFD_SETLKW with F_UNLCK) failing (flock's
// requests: premise_no_map_lock_err.go, NoMapLockErr, which covers them in the
// same form: one premise per call but for an open with no free fd, which both may name; the user's decision of 2026-11-20); a step
// of Readdirnames (getdents64) on a covered directory failing with an errno
// other than ENOENT (EIO, ...) while the directory has a name left to return
// or is at its end. Lean: IoCovers "OfdLock" (cmd
// F_OFD_SETLKW) (an fd of a covered inode), "DirReadNext" (a directory fd of a
// covered inode), "Open"/"Rename"/"Mkdir"/"Unlink"/"Rmdir" (PathFits);
// ErrnoZero "DirReadNext" (errno 0, or ENOENT: a removed directory,
// meta_enoent.go, is no I/O error).
//
// Still allowed under the premise (the semantics has no success there): EFBIG
// at or past maxBytes (data_maxbytes.go), the failures of a path call that cannot succeed in the state it is made in (ENOENT,
// EEXIST, ENOTEMPTY, EISDIR, ...), a lock request that conflicts with a lock
// another description holds (another fd's, or a mapping's: EAGAIN, or for a blocking request any
// errno: locks_blocking.go), ENOENT from a read of a removed directory, and
// anything on a call the premise does not name: flock (NoMapLockErr's), a
// non-blocking OFD lock request (F_OFD_SETLK), which may fail with EAGAIN while another
// process holds a reference to a description the program closed
// (locks_spurious_eagain.go: a /proc/<pid>/fdinfo reader; a blocking request
// waits for it instead), a path call on a path that does not fit (ENAMETOOLONG
// once the walk reaches the long component: TestNoIoErrNameTooLong),
// mmap/munmap, fallocate with
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
// ENOLCK when that fails) and for a read's buffer, no other process locks or
// unlocks the covered files, through any description (its own open, or a copy
// of the program's: pidfd_getfd, SCM_RIGHTS; the lock rule already takes the
// roots' files to be the process's own, locks_ofd.go), no fd is closed while a
// lock call on it is in flight (env_no_close_during_lock.go), and no fatal
// signal is pending (iterate_dir's
// killable lock, EINTR). An uncontended request does not sleep, so no signal
// can interrupt it (fs/locks.c: the wait is only on a conflict; a blocking
// request that meets a description another process keeps alive past close
// waits, uninterrupted, for its last reference: a moment for a /proc reader,
// as long as the other process keeps it for a pidfd_getfd copy). And configuration C's
// permissions (Impl.lean's "Environment", 2026-11-19, the user's approvals
// after the attack A2 on PathErrno and the attack on its fix): the process may
// search every ancestor of a root, search and write every covered directory,
// and read and write every covered file (no EACCES, on the walk or on an open
// for writing); no directory's sticky bit denies a removal or a rename; no
// covered file or directory has the immutable or append-only attribute (EPERM
// from may_delete, fs/namei.c, even for root); the sysctls
// fs.protected_symlinks and fs.protected_regular deny nothing (may_follow_link
// for a trailing symlink, may_create_in_sticky for an O_CREAT open, both in
// sticky world-writable directories, the latter even for root); an idmapped
// mount, if the filesystem is reached through one, maps the process's fsuid
// and fsgid (may_create: EOVERFLOW otherwise; measured by the attack on this
// host's idmapped /shared as nobody, not on C, which has no idmapped mount);
// and no Linux security module, seccomp filter or fanotify permission event
// denies or fails a call on them (security_path_*/security_inode_* hooks;
// SECCOMP_RET_ERRNO, kernel/seccomp.c; FAN_DENY, fs/notify/fanotify: from the
// kernel source, not measured). Measured as contrasts: TestNoIoErrPermissions
// (a child running as nobody gets EACCES from unlink in a directory it may not
// search or write; with the immutable or append-only attribute, where it can
// be set: CAP_LINUX_IMMUTABLE, unlink and rename get EPERM),
// TestNoIoErrPermAncestor (EACCES for unlink, rmdir and an O_CREAT open as
// nobody under a 0700 ancestor, ENOENT once it is 0755),
// TestNoIoErrPermFileWrite (EACCES for an O_RDWR open of a 0444 file as
// nobody), TestNoIoErrProtectedSymlinks (EACCES for nobody's open of a symlink
// owned by another user in a sticky world-writable directory, where the
// sysctl is set), TestNoIoErrProtectedRegular (EACCES for root's O_CREAT open
// of another user's file in a sticky world-writable directory, where the
// sysctl is set; skipped where it is 0). Measured on
// C, as support only (premise_no_io_err_test.go, run by run-models-on-c.sh):
// uncontended OFD (F_OFD_SETLKW) locks and their unlocks, and the Readdirnames
// of a small directory, succeed every time over many rounds; so do flock's
// (LOCK_EX), which since 2026-11-20 support NoMapLockErr's MapLockOk "Flock",
// not NoIoErr.
//
// The errnos of a failing unlink/rmdir (2026-11-19, the user's approval of item 3 of
// notes/wal-units/noioerr.md, narrowed to the cases wal.Create needs): an unlink
// or rmdir of a covered path that cannot succeed fails with the errno Linux
// gives, not any errno: ENOENT for a path with no entry whose parent is a
// directory (unlink(2), rmdir(2): the last component's lookup finds nothing),
// EISDIR for an unlink of a directory (may_delete, fs/namei.c), ENOTEMPTY for
// an rmdir of a directory with an entry (ext4_rmdir, fs/ext4/namei.c; POSIX
// also allows EEXIST, ext4 never gives it). Lean: PathErrno (Premises.lean),
// asked by NoIoErr only where the semantics has no outcome with errno 0;
// NoIoErr.lean: noIoErr_good keeps a step; NoIoErrSpecs.lean: noIoErr_pathErrno.
// Still allowed: every other failing case (an rmdir of a file, ENOTDIR; a
// missing parent; ...). Why: os.RemoveAll returns nil for an absent path only
// when rmdir answers ENOENT (or ENOTDIR after unlink's ENOENT), and walks a
// directory only after unlink's EISDIR (or EPERM/EACCES); wal.Create's
// renameWAL starts with RemoveAll(w.dir) of a directory that does not exist at
// a first start, and RemoveAll of a crash's leftover dir.tmp meets EISDIR and
// ENOTEMPTY: with any errno allowed, Create's error (on which etcd panics) was
// not excluded. Evidence: measured on C as support (premise_no_io_err_test.go,
// TestNoIoErrPathErrno); the further assumptions are the premise's (the
// permissions above: a permission check comes before the lookup's ENOENT,
// EACCES/EPERM; no memory pressure, no I/O error on the directory's blocks).
// A path that does not fit (a name longer than 255 bytes, or a path of 4096
// bytes or more) fails with ENAMETOOLONG (TestNoIoErrNameTooLong: a path of
// 4096 bytes always; a long name when the walk reaches it, ext4_lookup's check,
// after ENOENT or ENOTDIR from an earlier missing or non-directory component):
// such a path is not covered (PathFits; 2026-11-19,
// the user's decision on the attack's finding A1), so neither PathErrno nor
// the success clause speaks of it; the semantics, which bounds no length,
// gives it a short path's outcomes, failures with any errno included.
//
// The errno of a failing open of an absent name (2026-11-23, the user's
// approval for claim #34, wal.Exist): an open without O_CREAT of a covered path
// with no entry whose parent is a directory, from a state with a free fd,
// fails with ENOENT (open(2): the last component's lookup finds nothing), not
// any errno. Lean: PathErrno's "Open" case (Premises.lean); NoIoErr.lean:
// noIoErr_good keeps the step (the semantics' failure arm allows ENOENT exactly
// where the path does not resolve, Impl.lean's "Open"); NoMapLockErr.lean:
// noIoErr_noMapLockErr_keeps (with no free fd NoMapLockErr's EINTR, so the
// clause asks for a free fd; Linux takes the fd first, EMFILE). Still allowed:
// an open with O_CREAT that cannot succeed, an absent name under a missing
// parent (ENOENT on Linux too, but not asked), under a file (ENOTDIR), any
// errno with no free fd. Why: wal.Exist(dir) runs fileutil.ReadDir(dir), an
// os.Open of dir, and answers false only when errors.Is(err, os.ErrNotExist),
// true on any other error; with any errno allowed, Exist of an absent WAL
// directory could answer true and bootstrap would take a fresh member for a
// restart. Evidence: measured on C as support (premise_no_io_err_test.go,
// TestNoIoErrOpenAbsent, with its contrasts: ENOTDIR under a file, an O_CREAT
// open's success, EMFILE at RLIMIT_NOFILE); the further assumptions are the
// premise's (the permissions above: a search denied on the walk is EACCES).
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
		// under the premise: excluded (a blocking request; no other
		// description of the file holds a lock)
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
	h, _ := os.OpenFile(dir+"/wal.tmp/0.wal", os.O_WRONLY, 0o600)
	if err := syscall.FcntlFlock(h.Fd(), unix.F_OFD_SETLK, &lk); err != nil {
		// still allowed under the premise, though no description the
		// program has holds a lock: a non-blocking request is not covered
		// (EAGAIN while another process reads /proc/self/fdinfo of f's
		// closed fd: locks_spurious_eagain.go)
	}
	h.Close()
}

// NoIoErrPathErrno: the errnos of unlink and rmdir that cannot succeed, under
// the premise (dir's paths covered).
func NoIoErrPathErrno(dir string) {
	if err := os.RemoveAll(dir + "/wal"); err != nil {
		// the semantics: reachable (rmdir of the absent path may fail with any
		// errno, and RemoveAll returns nil only on ENOENT)
		// under the premise: excluded (PathErrno: ENOENT)
		panic(err)
	}
	os.MkdirAll(dir+"/wal.tmp", 0o700)
	os.WriteFile(dir+"/wal.tmp/0.wal", nil, 0o600)
	if err := os.RemoveAll(dir + "/wal.tmp"); err != nil {
		// the semantics: reachable (unlink of the directory, rmdir of it while
		// non-empty: any errno)
		// under the premise: excluded (PathErrno: EISDIR, then ENOTEMPTY; the
		// entries go, the directory then goes)
		panic(err)
	}
	if err := syscall.Rmdir(dir + "/wal.tmp"); err != syscall.ENOENT {
		// under the premise: excluded (the path is gone)
		panic(err)
	}
}

// NoIoErrOpenAbsent: wal.Exist of an absent WAL directory, under the premise
// (dir's paths covered).
func NoIoErrOpenAbsent(dir string) {
	d, err := os.Open(dir + "/member/wal")
	if err == nil {
		// excluded by the semantics (the path does not resolve)
		panic("opened")
	}
	if !errors.Is(err, os.ErrNotExist) {
		// the semantics: reachable (open of the absent path may fail with any
		// nonzero errno: wal.Exist would answer true)
		// under the premise, with dir/member a directory: excluded
		// (PathErrno: ENOENT)
		panic(err)
	}
	_ = d
}
