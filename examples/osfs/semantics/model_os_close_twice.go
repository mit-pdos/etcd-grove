//go:build linux

package semantics

import (
	"errors"
	"os"
)

// (*os.File).Close on a closed *File returns &PathError{"close", name,
// ErrClosed} (trusted model; a draft pending review, 2026-11-14).
//
// Decision: Close of a *File already closed (the model's fd field -1, which
// only Close sets) makes no system call, changes nothing, and returns
// &PathError{Op: "close", Path: f.Name(), Err: os.ErrClosed} (until 2026-11-14
// the model was stuck there: it asked the extension FdKind(-1)).
//
// Lean: LinuxFs/TrustedCode/os.lean: File.Close.impl (the fd -1 check).
//
// Allowed: the outcome below; nothing else (no close(2), so no other fd that
// reused the number is closed).
//
// Why: documented (go1.27.3 src/os/file_unix.go, file.close: pfd.Close's
// increfAndClose fails once the poll.FD is closing and returns
// poll.ErrFileClosing, which close maps to ErrClosed in a PathError with the
// file's name; no system call) and measured on C (TestCloseTwice). etcd's
// wal.Create reaches it: renameWALUnlock's w.Close() closes the tail's locked
// file, a failed second rename returns an error, and Create's deferred
// f.Close() closes it again.
func CloseTwice(f *os.File) {
	_ = f.Close() // nil, or close(2)'s error
	err := f.Close()
	var pe *os.PathError
	_ = errors.As(err, &pe) && pe.Op == "close" && pe.Path == f.Name() &&
		pe.Err == os.ErrClosed // true
}
