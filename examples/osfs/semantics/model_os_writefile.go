//go:build linux

package semantics

import (
	"os"
)

// os.WriteFile is Go's body; an empty File.Write returns nil or any errno
// (translation, and a trusted-model change; a draft pending review,
// 2026-11-13).
//
// Decision: WriteFile is translated (OpenFile with O_WRONLY|O_CREATE|O_TRUNC,
// Write, Close: the models). A Write of an empty slice, which Go issues as a
// zero-byte write(2), returns (0, nil) or (0, &PathError{"write", name,
// Errno(e)}) for any errno, with no extension step and the offset unchanged
// (until 2026-11-13 a panic: the answer depends on the fd's mode, which the
// model does not know).
//
// Lean: LinuxFs/TrustedCode/os.lean: File.Write.impl (the empty case);
// LinuxFs/Code/os.lean: WriteFile.impl (translated).
//
// Allowed: below, the file .touch made (empty) and WriteFile nil; any errno
// from the open, the empty write or the close.
// Excluded: .touch with data.
//
// Why: documented (POSIX write(): "If nbyte is zero and the file is a regular
// file, the write() function may detect and return errors as described below.
// In the absence of errors, or if error detection is not performed, the
// write() function shall return zero and have no other results") and measured
// (TestEmptyWrite: (0, nil) on a writable fd, EBADF on a read-only one, size
// unchanged). etcd's fileutil.IsDirWriteable writes an empty file with
// WriteFile (from TouchDirAll, the WAL's directory check).
func WriteEmptyFile(dir string) {
	os.WriteFile(dir+"/.touch", []byte(""), 0o600)
	os.Remove(dir + "/.touch")
}
