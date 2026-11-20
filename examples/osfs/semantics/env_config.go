//go:build linux

package semantics

import (
	"os"
)

// The target configuration C (environment assumption): the only machine the
// semantics claims to describe.
//
// Decision: Linux 7.0 on x86-64 with 4 KiB pages and no swap; one local ext4
// filesystem made by mkfs.ext4 with its defaults (4 KiB blocks, extents, a
// journal; no bigalloc, fast_commit, casefold, inline_data), mounted with
// ext4's default options (data=ordered, delalloc, dioread_nolock, barriers;
// any commit= interval); the process's RLIMIT_FSIZE unlimited; Go 1.27.3.
// notes/axiom-review/fs-config/check.sh checks a machine against C, and every
// experiment makes its filesystem with fs-config/mkfs-mount.sh.
//
// Lean: Impl.lean's header, "Configuration C"; pageIn (4096-byte pages, which
// on C are the blocks).
//
// Why this one: it is a reasonable etcd deployment (etcd's hardware guide
// recommends local SSD storage; ext4 made and mounted with its defaults is the
// root filesystem of Ubuntu's and Debian's installers and of most cloud
// images; etcd needs no special mount option), and every claim of the
// semantics is tested or argued for it alone. What C fixes, the semantics
// relies on:
//   - 4 KiB blocks = pages: a page past the size has no block of its own
//     shared with the end (durable zeros, data_durable_zeros.go);
//   - dioread_nolock: a new block may come back zeros under its size
//     (measured); data=ordered: never stale bytes;
//   - RLIMIT_FSIZE unlimited: a write is not cut short by the limit (Go's
//     WriteAt would retry into EFBIG; measured outside C with ulimit -f 6,
//     fs-v2-r4.md N2);
//   - no swap (an etcd deployment's usual setting; nothing in the model
//     depends on it now that tears are byte-level).
//   - no Linux security module denies a file lock on the roots' files
//     (security_file_lock, called by flock(2) and fcntl's lock commands
//     before any lock; 2026-11-19): a lock request that the lock rule lets
//     succeed is refused only by an error NoIoErr names (premise_no_io_err.go).
//   - no fd is closed while a lock call on it is in flight (2026-11-19, the
//     user's decision on the attack's finding F1'): env_no_close_during_lock.go.
//   - fds within the limits (2026-11-19, the user's decision on the attack's
//     finding F2'): at every open(2) the process holds fewer fds than its
//     RLIMIT_NOFILE soft limit (which Go's syscall init raises) and the
//     system's open files are below fs.file-max, so open gives no EMFILE or
//     ENFILE. The model always has a free fd (FdFree is unbounded), so
//     NoIoErr lets no covered open fail on it (premise_no_io_err.go; the
//     contrast measured: TestNoIoErrEmfile, EMFILE with the soft limit at 64;
//     ENFILE from the kernel source, alloc_empty_file, not measured). etcd's
//     own files are few (the WAL's locked segments, bbolt's db), but its
//     sockets, one per client connection, count toward the same limit: the
//     clause is the deployment's (a limit above what its clients need).
//   - permissions (2026-11-19, the user's approvals via etcd-grove-03, after
//     the attack A2 on PathErrno and the attack on its fix): the process may
//     search every ancestor of every root, search and write every directory
//     of the roots' trees, and read and write every file in them (no EACCES
//     from inode_permission on the walk, nor on an open for writing); no
//     directory's sticky bit denies a removal or rename in it; no entry has
//     the immutable or append-only attribute; the sysctls
//     fs.protected_symlinks and fs.protected_regular deny nothing (a
//     symlink named as a call's last component in a sticky world-writable
//     directory, such as a root's ancestor that Open's outside case opens;
//     an O_CREAT open of a file in one); if the filesystem is reached through an
//     idmapped mount, the mount maps the process's fsuid and fsgid (else
//     may_create gives EOVERFLOW); and no Linux security module, seccomp
//     filter or fanotify permission event denies or fails a call on them
//     (may_delete, may_create, inode_permission and the LSM hooks return no
//     EPERM/EACCES; no SECCOMP_RET_ERRNO; no FAN_DENY): the errnos PathErrno
//     names come from the lookup, not from a check that precedes it, and a
//     call NoIoErr lets succeed is refused by none of these
//     (premise_no_io_err.go; contrasts measured: TestNoIoErrPermissions,
//     TestNoIoErrPermAncestor, TestNoIoErrPermFileWrite,
//     TestNoIoErrProtectedSymlinks, TestNoIoErrProtectedRegular; the
//     idmapped mount, seccomp and fanotify: from the kernel source
//     (fs/namei.c may_create's fsuidgid_has_mapping; kernel/seccomp.c;
//     fs/notify/fanotify), not measured).
//
// Outside C (xfs, data=journal, 1-2 KiB blocks, other kernels): not
// described until tested on their own.
func Config(dir string) {
	f, _ := os.Create(dir + "/f")
	// on C: f is on ext4 with 4 KiB blocks, mounted with default options
	f.Close()
}
