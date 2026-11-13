//go:build linux

package semantics

import (
	"os"
)

// (*os.File).Close on a nil receiver returns os.ErrInvalid (trusted model; a
// draft pending review, 2026-11-13).
//
// Decision: Close of a nil *File makes no system call and returns ErrInvalid
// (until 2026-11-13 the model was stuck there, as on every nil *File).
//
// Lean: LinuxFs/TrustedCode/os.lean: File.Close.impl (the nil check).
//
// Allowed: err == os.ErrInvalid below.
//
// Why: documented (go1.27.3 src/os/file_posix.go: "if f == nil { return
// ErrInvalid }") and measured (TestCloseNil). etcd's wal.Open closes, on an
// error, a WAL whose dirFile is still nil (wal.go: w.Close() calls
// w.dirFile.Close()).
func CloseNil() {
	var f *os.File
	err := f.Close()
	_ = err == os.ErrInvalid // true
}
