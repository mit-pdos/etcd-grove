//go:build linux

package semantics

import (
	"errors"
	"os"
)

// ENOENT only where Linux returns it: a failing open of a path, and a failing
// read of a directory's names (trusted semantics; decided provisionally on
// 2026-11-14, pending the user's review, notes/wal-fsext-plan.md §10 and the
// W7-W12 log).
//
// Decision: a failing open(2) of a path of the roots' trees (a file or a
// directory, any flags) may return ENOENT (2) only when the path does not
// resolve in the tree at the call's step (OsState.lookup p = none: a component
// missing; also, more than Linux, which says ENOTDIR, a component that is a
// file); a failing getdents64 of a
// directory fd (one DirReadNext step) may return ENOENT only when the
// directory has been removed (not reachable from a root: ¬ Reach). Every other
// failure is any nonzero errno but ENOENT. Unchanged: unlink(2), rmdir(2),
// rename(2), mkdir(2) may still fail with ENOENT and no effect whatever the
// tree (os.RemoveAll's model relies on it: model_os_removeall.go,
// LinuxFs/TrustedCode/os.lean, model.removeAllFrom), and Open's outside case
// (an ancestor of a root, model_os_open_above.go) any nonzero errno.
//
// Lean: GooseLang/Ext/Fs/Impl.lean: ENOENT, IsFsStep's "Open" (its failure
// disjunct: e = ENOENT → st0.lookup p = none) and "DirReadNext" (its errno
// disjunct: e = ENOENT → ¬ Reach st.fs.roots st.tree df.ino).
//
// Allowed: Open of a missing path fails with ENOENT or any other errno; Open
// of a present file or directory succeeds or fails with any errno but ENOENT;
// Readdirnames of a removed directory's fd fails with ENOENT (or any errno),
// or returns no names; of a live directory, any errno but ENOENT.
// Excluded: ENOENT from Open of a path that resolves at the call's step, or
// from a read of a directory still in the tree.
//
// Why the step: the model resolves a path at its call's step (meta_dir_rename_
// stuck.go); Linux walks it a component at a time between the call's start and
// its return. Linux's ENOENT comes from a component's lookup finding no entry
// (a negative dentry: fs/namei.c, walk_component/step_into, "if
// (unlikely(d_is_negative(dentry))) return -ENOENT"; lookup_open and
// lookup_one_qstr_excl return -ENOENT in a dead directory, IS_DEADDIR). Since
// no directory is renamed while the call is in flight (the stuck clause), at
// that lookup's instant, or just after the rmdir that killed the directory the
// walk had reached, the path did not resolve; the call does nothing else
// between its start and its return, so the model's step may be placed at that
// instant. For a directory read, fs/readdir.c's iterate_dir: "res = -ENOENT;
// if (!IS_DEADDIR(inode)) { ... res = file->f_op->iterate_shared(file, ctx);"
// and a removed directory stays dead (its inode is never reused while the fd
// holds it), so a directory dead at the check is removed at the step.
// ext4's own lookup and readdir errors (ext4_lookup, ext4_readdir,
// ext4_dx_readdir) are EIO, EFSCORRUPTED, ENOMEM, not ENOENT (kernel source,
// read for Linux 7.0's ext4; not exhaustively measured).
//
// Measured on C (models_test.go, TestEnoent, run by run-models-on-c.sh): open
// of a missing name, and of a name under a missing or removed directory, fails
// with ENOENT; open of a present directory and of a file in it, and
// Readdirnames of the directory (made large enough for an htree index, so
// ext4_dx_readdir runs), each repeated while other goroutines create, rename
// and remove other entries of the same directory and of its parent, never
// failed; Readdirnames of an fd on a directory removed after its open fails
// with ENOENT.
//
// Who needs it: wal.Exist's false answer (errors.Is(err, os.ErrNotExist) of
// fileutil.ReadDir's error) must mean the WAL directory is absent, which the
// server's bootstrap uses to call wal.Create (fileutil.ReadDir.specChildIs,
// LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/ExistCallees.lean).
func EnoentOnlyAbsent(dir string) {
	os.Mkdir(dir+"/wal", 0o700)
	_, err := os.ReadDir(dir + "/wal")
	// allowed: err == nil, or any error with !errors.Is(err, os.ErrNotExist)
	// excluded: errors.Is(err, os.ErrNotExist): the directory is there
	_ = errors.Is(err, os.ErrNotExist)

	_, err = os.ReadDir(dir + "/missing")
	// allowed: errors.Is(err, os.ErrNotExist), or any other error
	_ = err

	d, _ := os.Open(dir + "/wal")
	os.Remove(dir + "/wal")
	_, err = d.Readdirnames(-1)
	// allowed: ENOENT (Linux's answer), any other errno, or no names
	_ = err
	d.Close()
}
