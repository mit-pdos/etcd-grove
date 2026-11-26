// The primitive stubs of syscall's model: each is one operation (or one call's two steps) of the
// Linux file extension fsExt (GooseLang/Ext/Fs/Impl.lean), listed in Code/syscall.toml's trusted,
// with its GooseLang model in TrustedCode/syscall.lean. The Go bodies serve gc builds and
// differential tests only (the real system call). An errno is a uintptr, 0 for success.

package syscall

import "unsafe"

// modelGcErrno is the errno of a system call's error, for the stubs' Go bodies.
func modelGcErrno(err error) uintptr {
	if err == nil {
		return 0
	}
	if e, ok := err.(Errno); ok {
		return uintptr(e)
	}
	return 5 // EIO
}

// fsFsync is fsync(fd) of a file's fd. GooseLang: the extension's Fsync.
func fsFsync(fd int) uintptr { return modelGcErrno(Fsync(fd)) }

// fsFlock is flock(fd, how). GooseLang: the extension's Flock.
func fsFlock(fd int, how int) uintptr {
	_, _, e := Syscall(SYS_FLOCK, uintptr(fd), uintptr(how), 0)
	return uintptr(e)
}

// fsFalloc is fallocate(fd, 0, off, len). GooseLang: FallocStart, then FallocFinish of its token.
func fsFalloc(fd int, off int64, len int64) uintptr {
	_, _, e := Syscall6(SYS_FALLOCATE, uintptr(fd), 0, uintptr(off), uintptr(len), 0, 0)
	return uintptr(e)
}

// fsFallocKeep is fallocate(fd, FALLOC_FL_KEEP_SIZE, off, len). GooseLang: FallocKeep.
func fsFallocKeep(fd int, off int64, len int64) uintptr {
	_, _, e := Syscall6(SYS_FALLOCATE, uintptr(fd), 1, uintptr(off), uintptr(len), 0, 0)
	return uintptr(e)
}

// fsOfdLock is fcntl(fd, cmd, &Flock_t{Type: typ}) for cmd F_OFD_SETLK or F_OFD_SETLKW, a
// whole-file lock. GooseLang: the extension's OfdLock of (fd, (cmd, typ)).
func fsOfdLock(fd uintptr, cmd int, typ int) uintptr {
	lk := Flock_t{Type: int16(typ)}
	_, _, e := Syscall(SYS_FCNTL, fd, uintptr(cmd), uintptr(unsafe.Pointer(&lk)))
	return uintptr(e)
}

// fsMkdir is CallBegin of path, then mkdir(path). GooseLang: the extension's Mkdir.
func fsMkdir(path string, mode uint32) uintptr { return modelGcErrno(Mkdirat(_AT_FDCWD, path, mode)) }

// fsUnlink is CallBegin of path, then unlink(path). GooseLang: the extension's Unlink.
func fsUnlink(path string) uintptr { return modelGcErrno(unlinkat(_AT_FDCWD, path, 0)) }

// fsRmdir is CallBegin of path, then rmdir(path). GooseLang: the extension's Rmdir.
func fsRmdir(path string) uintptr { return modelGcErrno(unlinkat(_AT_FDCWD, path, _AT_REMOVEDIR)) }

// fsPathKind is what path is: 1 strictly below a root, 0 a root, 2 a strict ancestor of a root.
// GooseLang: the extension's PathKind, a query of its environment. Go: 1.
func fsPathKind(path string) uintptr { return 1 }
