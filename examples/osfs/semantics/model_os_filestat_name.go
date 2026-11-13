//go:build linux

package semantics

import (
	"os"
)

// fileStat.Name: the base name of the path given to Stat/Lstat, or of the
// *File's name for File.Stat (trusted layout and models; pending the user's
// review, 2026-11-13, notes/wal-fsext-models-review.md, "fileStat.Name").
//
// Decision: the model's fileStat (LinuxFs/TrustedCode/os.lean,
// fileStat.underlying) holds name, size and mode; Name is translated (Go's
// `return fs.name`); File.Stat.impl, model.stat and model.statAbove store
// model.base of the path (of f.name for File.Stat): the path after the
// separator before its last component, the path itself if that is empty
// ("/" for "/"), and "." for "". That is Go's filepathlite.Base on the
// canonical absolute paths the model takes (every other path is stuck
// before), which fillFileStatFromSys stores (go1.27.3 src/os/stat_linux.go:
// fs.name = filepathlite.Base(name); src/os/stat_unix.go: File.Stat passes
// f.name, Stat and Lstat the path).
//
// Lean: LinuxFs/TrustedCode/os.lean: fileStat, fileStat.underlying,
// fileStat.FieldAssumptions (get_name, set_name), model.base, File.Stat.impl,
// model.stat, model.statAbove; LinuxFs/Code/os.toml ("fileStat.Name").
//
// Allowed: Stat("/r/wal").Name() == "wal", Stat("/").Name() == "/",
// f.Stat().Name() == "0000-0000.wal" for f opened at "/r/wal/0000-0000.wal".
// Excluded: any other name.
//
// Why: the WAL's decoder builds its "frame too large" error from
// f.Stat().Name() (wal/decoder.go), so Name must have a body.
// Measured (models_test.go, TestFileStatName): the three equalities above.
func FileStatName(root string) {
	fi, _ := os.Stat(root + "/wal")
	_ = fi.Name() // "wal"
	f, _ := os.Open(root + "/wal/0000-0000.wal")
	fi, _ = f.Stat()
	_ = fi.Name() // "0000-0000.wal"
}
