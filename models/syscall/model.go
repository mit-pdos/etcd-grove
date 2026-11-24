// The Go model of syscall (Go 1.27.3, linux/amd64) over the Linux file extension fsExt: the
// declarations Code/syscall.toml's [model] table replaces. The functions are zsyscall_linux_amd64.go's
// system-call stubs (one Syscall/Syscall6 and errnoErr, no EINTR retry at this level) and
// syscall_linux.go's *at wrappers; until 2026-11-24 their models were hand-written GooseLang
// (TrustedCode/syscall.lean), and each function here is that model, written in Go, step for step.

package syscall

import "internal/gomodel"

// MODEL: errnoErr (syscall_unix.go): nil for 0, else e as an error. Go returns the preallocated
// errEAGAIN, errEINVAL or errENOENT for those three errnos (to avoid an allocation); each holds the
// boxed Errno of the same value, so the two are equal interface values and no Go code can tell them
// apart (reflection and unsafe are not modelled). The preallocated variables are [[skip]] names, so
// Go's body does not translate.
func errnoErr(e Errno) error {
	if e == 0 {
		return nil
	}
	return e
}

// modelString is an arbitrary string (it can return every string, and may also not terminate).
func modelString() string {
	var s string
	for gomodel.ChooseUint64() != 0 {
		s += string([]byte{byte(gomodel.ChooseUint64())})
	}
	return s
}

// MODEL: (Errno).Error (syscall_unix.go): some string. Go's body reads the read-only table errors
// (zerrors_linux_amd64.go) inside its bounds and calls strconv.Itoa: it returns a string, never
// panics, and touches no memory a caller owns. The model returns an arbitrary string, so every result
// of Go's is one of the model's. (Go's body translates; it reads a package variable, which needs
// syscall's package fact, and Errno.Error's spec (fmtErrorOk) has none.)
func (e Errno) Error() string {
	return modelString()
}

// MODEL: syscall's init function (rlimit.go) raises the process's soft limit on open files through
// the raw prlimit system call (RawSyscall6, assembly) and records the original limit in
// origRlimitNofile, which only Setrlimit and exec read. It cannot panic. The model does nothing: the
// changed limit and origRlimitNofile are observable only through exec, a Getrlimit system call
// (neither modelled) or running out of file descriptors, and the file extension's Open may fail with
// any errno, EMFILE included, whatever the limit. (Running out can also end the process, when the
// netpoller's epoll_create1 fails: a prefix of a model run, which a partial-correctness triple does
// not contradict.) The user's decision, Perennial fix-semantics Case 33, 2026-11-04.
//
//gomodel:replace init.0 "var lim Rlimit"
func init() {
}

// MODEL: Fdatasync (zsyscall_linux_amd64.go): fdatasync(2), which the extension does not tell
// apart from fsync(2) (Linux's fdatasync also flushes the size, all the metadata the extension has):
// its Fsync (stuck on an fd that is not open, else success or any nonzero errno).
func Fdatasync(fd int) (err error) {
	return errnoErr(Errno(fsFsync(fd)))
}

// MODEL: Flock (zsyscall_linux_amd64.go): flock(2), one Syscall, EINTR not retried: the
// extension's Flock, the lock rule on the description's flock lock (a lock succeeds only when no
// other open file description of the file holds a conflicting one, two opens in one process
// conflicting; a blocking one waits; any request may fail with any errno and no change, EWOULDBLOCK
// included). Stuck on an fd that is not a file's, on another how, and on re-locking a description.
// examples/osfs/semantics/locks_flock.go, locks_blocking.go, locks_spurious_eagain.go.
func Flock(fd int, how int) (err error) {
	return errnoErr(Errno(fsFlock(fd, how)))
}

// MODEL: Fallocate (zsyscall_linux_amd64.go): one fallocate(2), EINTR not retried. Mode 0 is the
// extension's FallocStart, a resize to max(size, off + len) in flight, and FallocFinish (on failure
// any size between); FALLOC_FL_KEEP_SIZE (1) is FallocKeep, no visible change, any errno. Both are
// stuck on a negative off or a len not above 0 (Linux: EINVAL, misuse) and on an fd that is not a
// writable file's. Other modes (punching, zeroing, collapsing, inserting) are not modelled.
// examples/osfs/semantics/model_syscall_fallocate.go.
func Fallocate(fd int, mode uint32, off int64, len int64) (err error) {
	if mode == 0 {
		return errnoErr(Errno(fsFalloc(fd, off, len)))
	}
	if mode == 1 {
		return errnoErr(Errno(fsFallocKeep(fd, off, len)))
	}
	gomodel.Stuck()
	return nil
}

// MODEL: FcntlFlock (flock_linux.go): one fcntl(2) with the lock description lk
// (fcntl64Syscall is SYS_FCNTL on amd64), nil for errno 0, else the Errno.
//
// F_OFD_SETLK (37) and F_OFD_SETLKW (38): Linux copies the description in (do_fcntl), so the model
// loads Type, Whence, Start, Len, Pid (a concurrent write is a race a proof must exclude; the padding,
// which no outcome depends on, is not loaded). A whole-file request (Whence SEEK_SET, Start and Len
// 0) with Pid 0 and Type F_RDLCK (0), F_WRLCK (1) or F_UNLCK (2) is the extension's OfdLock of (fd,
// (cmd, Type)): the lock rule on the description's OFD lock (as Flock's), any request failing with
// any errno and no change. Anything else is not modelled: a byte range (Linux accepts it), Pid not 0
// or another Type (Linux: EINVAL). Nothing is written back (F_SETLK copies nothing out).
// examples/osfs/semantics/locks_ofd.go, locks_blocking.go.
//
// F_SETLK (6) and F_SETLKW (7), the per-process POSIX locks, are not modelled: they never conflict
// within one process and closing any fd of the file releases them (locks_posix_not_modelled.go).
//
// F_OFD_GETLK (36), the query fileutil's initializer makes on fd 0 (lock_linux.go's init), on any fd,
// one the process opened or not: no extension step (a query changes no state the model has), and
// nil or any nonzero errno. Linux copies the whole struct in, and on success copies the whole struct
// back: the lock description and the padding as read. So the model loads all seven fields at entry
// and, on success, stores all seven: arbitrary values in Type, Whence, Start, Len and Pid, the
// padding as loaded (measured, TestOFDGetlkPadding); a concurrent access is then a race, which a
// proof must exclude. On failure lk is unchanged. A nil lk is stuck (Linux: EFAULT). Any other
// command is not modelled. examples/osfs/semantics/model_syscall_fcntlflock.go.
func FcntlFlock(fd uintptr, cmd int, lk *Flock_t) error {
	if cmd == 37 || cmd == 38 {
		ty := lk.Type
		wh := lk.Whence
		st := lk.Start
		ln := lk.Len
		pid := lk.Pid
		if wh == 0 && st == 0 && ln == 0 && pid == 0 {
			if ty == 1 {
				return errnoErr(Errno(fsOfdLock(fd, cmd, 1)))
			}
			if ty == 0 {
				return errnoErr(Errno(fsOfdLock(fd, cmd, 0)))
			}
			if ty == 2 {
				return errnoErr(Errno(fsOfdLock(fd, cmd, 2)))
			}
			gomodel.Stuck()
		}
		gomodel.Stuck()
	}
	if cmd == 36 {
		_ = lk.Type
		_ = lk.Whence
		p0 := lk.Pad_cgo_0
		_ = lk.Start
		_ = lk.Len
		_ = lk.Pid
		p1 := lk.Pad_cgo_1
		e := Errno(gomodel.ChooseUint64())
		if e == 0 {
			lk.Type = int16(gomodel.ChooseUint64())
			lk.Whence = int16(gomodel.ChooseUint64())
			lk.Pad_cgo_0 = p0
			lk.Start = int64(gomodel.ChooseUint64())
			lk.Len = int64(gomodel.ChooseUint64())
			lk.Pid = int32(gomodel.ChooseUint64())
			lk.Pad_cgo_1 = p1
			return nil
		}
		return errnoErr(e)
	}
	gomodel.Stuck()
	return nil
}

// MODEL: Mkdir (syscall_linux.go: Mkdirat(AT_FDCWD, path, mode), one mkdirat(2), EINTR not
// retried here: os's ignoringEINTR retries): the extension's Mkdir of path, after its own CallBegin
// (fsMkdir). At a root or a strict ancestor of one (fsPathKind 0 or 2), where the extension gives a
// path no meaning, with no extension step: any nonzero errno (EEXIST on Linux). The environment keeps
// the roots and their ancestors existing directories (a symlink to one, for an ancestor) that no step
// of the program can remove or rename, so mkdir(2) of one fails (EEXIST, or any other errno), changing
// nothing. (Until 2026-11-24 this was os.MkdirAll's mkdirAllAbove; os.MkdirAll is now Go's, over
// this.) The mode matters only to a created directory's, which the extension does not model.
// examples/osfs/semantics/model_os_mkdirall.go, model_os_mkdirall_above.go.
func Mkdir(path string, mode uint32) (err error) {
	if fsPathKind(path) != 1 {
		e := Errno(gomodel.ChooseUint64())
		if e == 0 {
			e = EEXIST
		}
		return e
	}
	return errnoErr(Errno(fsMkdir(path, mode)))
}

// MODEL: Unlink (syscall_linux.go: unlinkat(AT_FDCWD, path, 0), one unlinkat(2), EINTR not
// retried here): the extension's Unlink of path, after its own CallBegin (fsUnlink).
func Unlink(path string) error {
	return errnoErr(Errno(fsUnlink(path)))
}

// MODEL: Rmdir (syscall_linux.go: unlinkat(AT_FDCWD, path, AT_REMOVEDIR), one unlinkat(2), EINTR
// not retried here): the extension's Rmdir of path, after its own CallBegin (fsRmdir).
func Rmdir(path string) error {
	return errnoErr(Errno(fsRmdir(path)))
}
