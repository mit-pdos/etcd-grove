//go:build linux

package semantics

import (
	"os"
)

// os.Stat and os.Lstat of a path, as an open, an fstat and a close (trusted
// model; a draft pending review, 2026-11-13).
//
// Decision: the extension has no stat of a path, so Stat(name) is an
// open(name, O_RDONLY|O_CLOEXEC) (the extension's Open, after a CallBegin),
// whose fd says the kind (FdKind) and, for a file, the size (Fstat), closed at
// once, EINTR retried; any failure is &PathError{"stat", name, Errno(e)} for
// any errno. The FileInfo's mode is the type (0, or ModeDir for a directory)
// with arbitrary permission, setuid, setgid and sticky bits; a directory's
// size is arbitrary. Lstat is the same (no symlinks in the roots' trees).
// File.Stat's mode, which the model did not hold before, is a regular file's
// with arbitrary permission bits. Name, ModTime and Sys stay unmodelled.
//
// Lean: LinuxFs/TrustedCode/os.lean: model.stat, Stat.impl, Lstat.impl,
// model.arbitraryMode, fileStat.underlying (size, mode); the translated
// fileStat.Mode, fileStat.IsDir, fs.FileMode.IsDir and Perm.
//
// Allowed: below, Exist true and IsDir true for the directory, false for the
// file; any errno for either (Exist false, IsDir unknown); any Perm.
// Excluded: IsDir false for a directory whose Stat succeeded.
//
// Why: an open without O_CREAT/O_TRUNC changes nothing but the fd table, and
// the fd is closed before Stat returns (fd numbers are the extension's
// arbitrary choice, so no other thread can tell); where stat succeeds, the
// open can succeed on the same entry (permissions are not modelled), and
// where it fails, the open can fail with the same errno; extra answers (an
// EMFILE stat) only weaken a proof. Documented (go1.27.3 src/os/stat_unix.go,
// statNolog; stat_linux.go, fillFileStatFromSys: the mode is st_mode&0777,
// ModeDir for S_IFDIR, and the setuid/setgid/sticky bits) and measured
// (TestStatMode: Mode().IsDir() of a directory and of a file, the permission
// bits Mkdir and OpenFile set under the umask). etcd's fileutil calls Stat in
// Exist (TouchDirAll, the WAL's Exist) and CheckDirPermission (Mode().Perm()).
func StatModes(dir string) {
	os.Mkdir(dir+"/d", 0o700)
	f, _ := os.Create(dir + "/f")
	f.Close()
	di, _ := os.Stat(dir + "/d") // di.IsDir(): true; di.Mode().Perm(): any
	fi, _ := os.Stat(dir + "/f") // fi.IsDir(): false; fi.Size(): 0
	_, _ = di, fi
}
