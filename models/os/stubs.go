// The primitive stubs of os's model: each is one operation (or one call's two steps) of the Linux
// file extension fsExt (GooseLang/Ext/Fs/Impl.lean), listed in Code/os.toml's trusted, with its
// GooseLang model in TrustedCode/os.lean. The Go bodies here serve gc builds and differential tests
// only (the real system call, or the common case where the extension answers a question of its own
// model). An errno is a uintptr (0 for success), as the extension returns it. The path operations
// take their CallBegin (the extension's start of a call on a path) in the same stub, so the
// extension's token never reaches a Go variable.

package os

import "syscall"

// modelGcErrno is the errno of a system call's error (0 for nil), for the stubs' Go bodies.
func modelGcErrno(err error) uintptr {
	if err == nil {
		return 0
	}
	if e, ok := err.(syscall.Errno); ok {
		return uintptr(e)
	}
	return 5 // EIO
}

// fsOpen is CallBegin of name, then open(name, flag, perm): (fd, errno). GooseLang: the extension's
// Open of (token, name, flag); perm is not modelled (the extension has no file modes).
func fsOpen(name string, flag int, perm uint32) (int, uintptr) {
	fd, err := syscall.Open(name, flag, perm)
	return fd, modelGcErrno(err)
}

// fsPRead is pread(fd, n bytes, off): (data, errno). GooseLang: the extension's PRead.
func fsPRead(fd int, off int64, n int) (string, uintptr) {
	b := make([]byte, n)
	m, err := syscall.Pread(fd, b, off)
	if m < 0 {
		m = 0
	}
	return string(b[:m]), modelGcErrno(err)
}

// fsPWrite is pwrite(fd, data, off): (written, errno). GooseLang: the extension's PWriteStart, then
// PWriteFinish of its token.
func fsPWrite(fd int, off int64, data string) (int, uintptr) {
	m, err := syscall.Pwrite(fd, []byte(data), off)
	if m < 0 {
		m = 0
	}
	return m, modelGcErrno(err)
}

// fsFdKind is what fd is: 0 a file's, 1 a directory's, 2 a directory's outside the roots' trees.
// GooseLang: the extension's FdKind, a query of its state. Go: an fstat (never 2).
func fsFdKind(fd int) uintptr {
	var st syscall.Stat_t
	if syscall.Fstat(fd, &st) == nil && st.Mode&syscall.S_IFMT == syscall.S_IFDIR {
		return 1
	}
	return 0
}

// fsClose is close(fd) of a file's fd: the errno. GooseLang: the extension's Close.
func fsClose(fd int) uintptr { return modelGcErrno(syscall.Close(fd)) }

// fsDirClose is close(fd) of a directory's fd. GooseLang: the extension's DirClose.
func fsDirClose(fd int) uintptr { return modelGcErrno(syscall.Close(fd)) }

// fsOutClose is close(fd) of a directory's fd outside the roots' trees. GooseLang: OutClose.
func fsOutClose(fd int) uintptr { return modelGcErrno(syscall.Close(fd)) }

// fsFstat is fstat(fd)'s size: (size, errno). GooseLang: the extension's Fstat.
func fsFstat(fd int) (int64, uintptr) {
	var st syscall.Stat_t
	err := syscall.Fstat(fd, &st)
	return st.Size, modelGcErrno(err)
}

// fsFtruncate is ftruncate(fd, size): the errno. GooseLang: FtruncateStart, then FtruncateFinish.
func fsFtruncate(fd int, size int64) uintptr { return modelGcErrno(syscall.Ftruncate(fd, size)) }

// fsFsync is fsync(fd) of a file's fd. GooseLang: the extension's Fsync.
func fsFsync(fd int) uintptr { return modelGcErrno(syscall.Fsync(fd)) }

// fsDirSync is fsync(fd) of a directory's fd. GooseLang: the extension's DirSync.
func fsDirSync(fd int) uintptr { return modelGcErrno(syscall.Fsync(fd)) }

// fsOutSync is fsync(fd) of a directory's fd outside the roots' trees. GooseLang: OutSync.
func fsOutSync(fd int) uintptr { return modelGcErrno(syscall.Fsync(fd)) }

// fsLstatDir is CallBegin of name, then os.Rename's question of its destination: (isDir, errno),
// isDir 1 only for a directory, with the errno Rename returns. GooseLang: the extension's LstatDir.
func fsLstatDir(name string) (uintptr, uintptr) {
	var st syscall.Stat_t
	if syscall.Lstat(name, &st) == nil && st.Mode&syscall.S_IFMT == syscall.S_IFDIR {
		return 1, uintptr(syscall.EEXIST)
	}
	return 0, 0
}

// fsRename is CallBegin of oldpath, then rename(oldpath, newpath): the errno. GooseLang: Rename.
func fsRename(oldpath, newpath string) uintptr {
	return modelGcErrno(syscall.Rename(oldpath, newpath))
}

// fsUnlink is CallBegin of name, then unlink(name): the errno. GooseLang: the extension's Unlink.
func fsUnlink(name string) uintptr { return modelGcErrno(syscall.Unlink(name)) }

// fsRmdir is CallBegin of name, then rmdir(name): the errno. GooseLang: the extension's Rmdir.
func fsRmdir(name string) uintptr { return modelGcErrno(syscall.Rmdir(name)) }

// fsDirReadNext is the next name of the directory fd: (name, done, errno), done 1 at the end.
// GooseLang: the extension's DirReadNext. Go: the names of one getdents pass, kept per fd.
func fsDirReadNext(fd int) (string, uintptr, uintptr) {
	names, ok := modelDirNames[fd]
	if !ok {
		buf := make([]byte, 8192)
		for {
			n, err := syscall.ReadDirent(fd, buf)
			if err != nil {
				return "", 0, modelGcErrno(err)
			}
			if n <= 0 {
				break
			}
			_, _, names = syscall.ParseDirent(buf[:n], -1, names)
		}
		names = append(names, "")
	}
	nm := names[0]
	if len(names) == 1 {
		delete(modelDirNames, fd)
		return "", 1, 0
	}
	modelDirNames[fd] = names[1:]
	return nm, 0, 0
}

// modelDirNames is fsDirReadNext's state in gc builds (a [[skip]] variable of Code/os.toml).
var modelDirNames = map[int][]string{}

// fsPathKind is what name is: 1 a path strictly below a root, 0 a root, 2 a strict ancestor of a
// root. GooseLang: the extension's PathKind, a query of its environment. Go: 1.
func fsPathKind(name string) uintptr { return 1 }

// fsWithCall runs body inside a CallBegin of path, ended (after body returns) by a LstatDir of path
// with that token (a step without effect): every rename of a directory in path's root's tree by
// another thread is stuck meanwhile. GooseLang: CallBegin, body, LstatDir. Go: body().
func fsWithCall(path string, body func() error) error { return body() }
