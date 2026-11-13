//go:build linux

package semantics

import (
	"os"
)

// os.Open of a strict ancestor of a root ("/", or a directory above a root),
// read-only: an fd of a directory outside the roots' trees, whose Sync is
// success with no effect or any errno and whose Close frees it; or any errno
// (trusted semantics; pending the user's review, 2026-11-13,
// notes/wal-fsext-models-review.md, "Above-root Stat/Open").
//
// Decision: the extension's Open, of a path p with OsState.AboveRoot p (and
// not a path of the roots' trees) and flags O_RDONLY (with or without
// O_CLOEXEC), ends its call and either opens a fresh fd (FdFree: no fd of a
// file or a directory has it) recorded in ProcState.ofds, or fails with any
// nonzero errno; nothing else changes. On such an fd, FdKind is 2, OutSync
// (File.Sync's fsync) returns any errno, 0 included, and changes nothing,
// OutClose (File.Close's close) frees it whatever the errno; every other step
// on it is stuck (pread, fstat, readdir, ...). Open of such a path with other
// flags (O_WRONLY, O_RDWR, O_CREAT, O_TRUNC) is stuck. A crash forgets the fd
// with the rest of the process.
//
// Lean: GooseLang/Ext/Fs/Impl.lean: IsFsStep's "Open" (its outside case,
// OpenOutside), "FdKind", "OutSync", "OutClose", ProcState.ofds, FdFree,
// OsState.addOfd, OsState.delOfd; LinuxFs/TrustedCode/os.lean:
// OpenFile.impl (unchanged: it calls Open), File.Sync.impl and
// File.Close.impl (FdKind 2: OutSync, OutClose).
//
// Allowed: Open(ancestor) returns a *File or a PathError; its Sync returns nil
// or any PathError; its Close nil or any PathError; the trees unchanged, no
// claim on what the fsync made durable. Excluded: any change to the trees;
// reads, Readdirnames or Stat through the fd (stuck); an fd number another
// open fd has.
//
// Why: fileutil.syncDir (fileutil.TouchDirAll's last loop, the WAL's Create)
// opens and fsyncs the parent of every directory TouchDirAll's Exist loop
// found missing, and that loop may climb above the root (model_os_stat_above.go);
// before this the model was stuck there. No claim about durability is made: on
// C an fsync of a directory commits its filesystem's whole journal
// (ext4_force_commit), which on the roots' filesystem commits their trees'
// operations too, but an ancestor may be on another filesystem; claiming
// nothing is weaker than either. Measured on C (models_test.go,
// TestStatOpenAboveRoot): open("/", O_RDONLY|O_CLOEXEC) and open of a root's
// parent succeed, fsync of either returns 0, close returns 0, and the
// directory is unchanged; open of "/" with O_WRONLY or O_RDWR fails with
// EISDIR. Documented: open(2) (EISDIR: "pathname refers to a directory and the
// access requested involved writing"); fsync(2); close(2) ("the file
// descriptor is released" whatever the error, Linux); go1.27.3
// src/os/file_unix.go (openFileNolog, ignoringEINTR).
func OpenAboveRoot(root string) {
	f, err := os.Open("/") // an fd outside the trees, or a PathError
	if err != nil {
		return
	}
	f.Sync()                             // nil or any error; no claim on durability
	f.Close()                            // the fd freed
	os.OpenFile("/", os.O_RDWR, 0)       // stuck (Linux: EISDIR)
	g, _ := os.Open(root + "/../" + "x") // stuck: not canonical
	_ = g
}
