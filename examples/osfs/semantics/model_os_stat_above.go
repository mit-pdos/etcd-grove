//go:build linux

package semantics

import (
	"os"
)

// os.Stat and os.Lstat of a strict ancestor of a root ("/", or a directory
// above a root): no extension step; a directory (or a symlink), or any errno
// (trusted semantics and model; pending the user's review, 2026-11-13,
// notes/wal-fsext-models-review.md, "Above-root Stat/Open").
//
// Decision: the extension's query PathKind(p) (no system call, no state
// change) is 1 for a path strictly below a root, 0 for a root, 2 for a strict
// ancestor of one (OsState.AboveRoot: "/" included). Stat and Lstat ask it
// first; at 2 they answer with no extension step: a fresh fileStat of
// arbitrary size whose mode is ModeDir or ModeSymlink with arbitrary
// permission bits, and a nil error; or a nil FileInfo and &PathError{op, p,
// Errno(e)}, e any nonzero errno. Elsewhere they are as before
// (model_os_stat.go: open, fstat, close).
//
// Lean: GooseLang/Ext/Fs/Impl.lean: PathKind, OsState.AboveRoot, the header's
// Environment ("the roots and their ancestors are existing directories
// throughout"; an ancestor may be a symlink to one); LinuxFs/TrustedCode/os.lean:
// model.stat, model.statAbove, Stat.impl, Lstat.impl.
//
// Allowed: Stat(ancestor) and Lstat(ancestor) return a directory's (or a
// symlink's) FileInfo or a "stat"/"lstat" PathError; nothing changes.
// Excluded: any change to the trees; an answer of a regular file.
//
// Why: fileutil.TouchDirAll's Exist loop (the WAL's Create) climbs from the
// directory to make while Stat fails, and Stat of the root may fail (any
// errno, the extension's environmental failure), so it reaches the root's
// parent and above; before this the model was stuck there (the extension's
// Open is stuck off the roots' trees) and TouchDirAll had no proof.
// Measured on C (models_test.go, TestStatOpenAboveRoot): Stat and Lstat of
// "/" and of a root's parent succeed with a directory and change nothing (the
// directory's inode, link count and modification time as before); Lstat of
// a symlink to a directory sees a symlink, Stat a directory. Documented:
// stat(2) ("stat() and fstatat() retrieve information about the file pointed
// to by pathname"; "lstat() is identical to stat(), except that if pathname is
// a symbolic link, then it returns information about the link itself"; EACCES,
// ENOMEM, ... as errors); go1.27.3 src/os/stat_unix.go (statNolog/lstatNolog:
// ignoringEINTR, &PathError{Op: "stat"/"lstat", ...}).
func StatAboveRoot(root string) {
	os.Stat("/")               // a directory, or any errno; no change
	os.Lstat("/")              // the same (or a symlink, which Linux never says of "/")
	os.Stat(root + "/..")      // stuck: not canonical (the model's paths are)
	os.Stat("/elsewhere/file") // stuck: outside the roots' trees and not above one
}
