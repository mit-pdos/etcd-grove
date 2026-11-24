// The Go model of os (Go 1.27.3, linux/amd64) over the Linux file extension fsExt
// (GooseLang/Ext/Fs/Impl.lean): the declarations Code/os.toml's [model] table replaces, their
// helpers, and the primitive stubs (stubs.go), one extension operation each. Until 2026-11-24 the
// same models were hand-written GooseLang (TrustedCode/os.lean); each function here is that model,
// written in Go, step for step.
//
// Shared facts (every MODEL: comment relies on them):
//   - A *File that OpenFile returns holds a *file whose pfd.Sysfd is the fd and name the name;
//     nonblock, appendMode and dirinfo stay zero (the extension's Open refuses O_APPEND and
//     O_NONBLOCK, and no model reads a directory through dirinfo), so Go's methods that read them
//     take the branch the model takes. off is the kernel's file offset of the fd's open file
//     description (f_pos), which Go does not keep: Seek, Write, Read and copy_file_range use it.
//   - Go retries EINTR (ignoringEINTR, poll's loops); so do the models (errno 4).
//   - An error is Go's: &PathError{Op, Path: f.name, Err: Errno(e)} (f.wrapErr of an errno), &LinkError,
//     io.EOF unwrapped.
//   - The models are less defined than Go (gomodel.Stuck, or a stuck extension step) where Go's
//     answer depends on what is not modelled: a closed file (fd -1, which only Close sets; Go answers
//     ErrClosed), a nil or zero File (Go: ErrInvalid), an operation racing Close (Go's reference count
//     makes it safe; in the model it is a race on the file cell), an unknown offset (after a failed
//     Write), offsets reaching 2^62.
//   - A fileStat the models make has name, size and mode; modTime and sys stay zero, so ModTime, Sys
//     and sameFile (and SameFile) stay untranslated (no proof can call them).

package os

import (
	"errors"
	"internal/filepathlite"
	"internal/gomodel"
	"io"
	"syscall"
	"sync/atomic"
	"internal/poll"
)

// MODEL: file is Go's layout (file_unix.go) with one field added, off, the kernel's file offset of
// the fd's open file description (f_pos), which Go does not keep and the extension, whose reads and
// writes name their offsets, does not either. An unexported field of an unexported type: no code
// outside os can observe it (reflection and unsafe are not modelled), and inside os only the models
// read or write it.
type file struct {
	pfd         poll.FD
	name        string
	dirinfo     atomic.Pointer[dirInfo] // nil unless directory being read
	nonblock    bool                    // whether we set nonblocking mode
	stdoutOrErr bool                    // whether this is stdout or stderr
	appendMode  bool                    // whether file is opened for appending
	inRoot      bool                    // whether file is opened in a Root
	off         int64                   // MODEL: the kernel's file offset (f_pos)
}

const (
	// modelMaxRW is poll's maxRW (fd_unix.go): at most 1 GiB per read(2)/pread(2)/pwrite(2).
	modelMaxRW = 1 << 30
	// modelOffMax is the bound below which the models keep file offsets (2^62), so that an int64
	// sum of two of them cannot wrap: past it they do not go (gomodel.Stuck).
	modelOffMax = 0x4000000000000000
	// modelSeekMax is the largest offset lseek accepts on the target configuration's ext4 (extent
	// files, 4 KiB blocks): s_maxbytes = (2^32 - 1) * 4096 (ext4_max_size); measured on
	// configuration C (notes/axiom-review/fs-v2-r8/, TestSeekPastMaxBytes).
	modelSeekMax = 0xffffffff000
	// modelOpenFlags is O_RDONLY|O_CLOEXEC, what Go's open adds (and openDirAt's flags but for
	// O_DIRECTORY|O_NOFOLLOW, which the extension does not take).
	modelOpenFlags = 0x80000
	// modelOtherBits are the bits of a FileMode that fillFileStatFromSys (stat_linux.go) sets from
	// st_mode other than the type: the permissions (0777), ModeSetuid, ModeSetgid and ModeSticky.
	modelOtherBits = 0xD001FF
)

// modelErrno is syscall's errnoErr of an errno: nil for 0, else Errno(e) as an error.
func modelErrno(e uintptr) error {
	if e == 0 {
		return nil
	}
	return syscall.Errno(e)
}

// modelPathError is &PathError{Op: op, Path: path, Err: err} as an error.
func modelPathError(op, path string, err error) error {
	return &PathError{Op: op, Path: path, Err: err}
}

// modelPathErrorPtr is &PathError{Op: op, Path: path, Err: err}, the pointer (RemoveAll's model
// changes its Path after making it, as Go does).
func modelPathErrorPtr(op, path string, err error) *PathError {
	return &PathError{Op: op, Path: path, Err: err}
}

// modelWrapErrno is f.wrapErr(op, Errno(e)) for an errno e != 0 of the file inner.
func modelWrapErrno(op string, inner *file, e uintptr) error {
	return modelPathError(op, inner.name, modelErrno(e))
}

// modelMode is a mode fillFileStatFromSys can make for a file of type ty (0 for a regular file,
// ModeDir for a directory, ModeSymlink for a symlink): the type, and arbitrary other bits (the
// extension does not model permissions, so any of them may be set).
func modelMode(ty FileMode) FileMode {
	return ty | FileMode(gomodel.ChooseUint64())&modelOtherBits
}

// MODEL: OpenFile (file.go, file_unix.go's openFileNolog and newFile). Go's body is
// `testlog.Open(name)` (a no-op outside go test's logging), then open(2) of name with
// flag|O_CLOEXEC (O_LARGEFILE is 0 on amd64), EINTR retried, an error being
// &PathError{"open", name, Errno(e)}, then newFile, whose other work (an fstat deciding whether the
// fd is pollable, the poller's registration, the finalizer) no Go code observes; appendMode is
// flag&O_APPEND, false since the extension refuses O_APPEND. fsOpen is the extension's Open after its
// own CallBegin, each attempt. perm matters only to a created file's mode, which the extension does
// not model. A name with a NUL byte (Go: EINVAL without a system call) is not a path of the roots'
// trees: the extension is stuck on it.
func OpenFile(name string, flag int, perm FileMode) (*File, error) {
	for {
		fd, e := fsOpen(name, flag|modelOpenFlags, syscallMode(perm))
		if e == 0 {
			inner := &file{name: name}
			inner.pfd.Sysfd = fd
			inner.pfd.IsStream = true
			inner.pfd.ZeroReadIsEOF = true
			return &File{inner}, nil
		}
		if e != 4 { // EINTR
			return nil, modelPathError("open", name, modelErrno(e))
		}
	}
}

// MODEL: (*File).Close (file_posix.go, file_unix.go's file.close): a nil *File returns ErrInvalid
// without a system call (Go's own first line); a closed one (fd -1) returns
// &PathError{"close", name, ErrClosed} without one (Go: pfd.Close's increfAndClose fails with
// ErrFileClosing, which close maps to ErrClosed; examples/osfs/semantics/model_os_close_twice.go).
// Otherwise close(2), not retried on EINTR (Linux frees the fd whatever the errno), and pfd.Sysfd
// set to -1 (Go's pfd.destroy). The extension's Close frees the fd whatever its errno; DirClose for
// a directory's fd, OutClose for a directory's outside the roots' trees (fsFdKind, a query of the
// model's state, not a system call, decides).
func (f *File) Close() error {
	if f == nil {
		return ErrInvalid
	}
	inner := f.file
	fd := inner.pfd.Sysfd
	if fd == -1 {
		return modelPathError("close", inner.name, ErrClosed)
	}
	kind := fsFdKind(fd)
	inner.pfd.Sysfd = -1
	var e uintptr
	if kind == 0 {
		e = fsClose(fd)
	} else if kind == 1 {
		e = fsDirClose(fd)
	} else {
		e = fsOutClose(fd)
	}
	if e == 0 {
		return nil
	}
	return modelWrapErrno("close", inner, e)
}

// MODEL: (*File).ReadAt (file.go, poll.FD.Pread). A negative offset returns Go's error without a
// system call. Otherwise Go's loop: pread(2) of at most modelMaxRW bytes, EINTR retried; an error
// ends it with f.wrapErr("read", e); a read of 0 bytes ends it with io.EOF; a short read is
// followed by another. fsPRead's data is copied into b (a failed pread may have written a prefix of
// b, which is copied and not counted, as in Go).
func (f *File) ReadAt(b []byte, off int64) (n int, err error) {
	inner := f.file
	if off < 0 {
		return 0, modelPathError("readat", inner.name, errors.New("negative offset"))
	}
	fd := inner.pfd.Sysfd
	for {
		l := len(b)
		if l == 0 {
			return n, nil
		}
		k := l
		if k > modelMaxRW {
			k = modelMaxRW
		}
		data, e := fsPRead(fd, off, k)
		m := copy(b, data)
		if e == 4 { // EINTR
			continue
		}
		if e != 0 {
			return n, modelWrapErrno("read", inner, e)
		}
		if m == 0 {
			return n, io.EOF
		}
		b = b[m:l]
		off += int64(m)
		n += m
	}
}

// MODEL: (*File).WriteAt (file.go, poll.FD.Pwrite). A negative offset returns Go's error without a
// system call. Pwrite returns all of p written, or an error, so WriteAt's loop runs once: (len(b),
// nil) or (0, f.wrapErr("write", e)). Pwrite's loop writes p[nn:max] (at most modelMaxRW bytes) at
// off+nn, EINTR retried, until all is written or an error. Each pwrite(2) is fsPWrite (the
// extension's PWriteStart and PWriteFinish), never of empty data; with errno 0 it always writes
// something, so Pwrite's io.ErrUnexpectedEOF branch is unreachable.
func (f *File) WriteAt(b []byte, off int64) (n int, err error) {
	inner := f.file
	if off < 0 {
		return 0, modelPathError("writeat", inner.name, errors.New("negative offset"))
	}
	fd := inner.pfd.Sysfd
	l := len(b)
	if l == 0 {
		return 0, nil
	}
	nn := 0
	for {
		max := l
		if l-nn > modelMaxRW {
			max = nn + modelMaxRW
		}
		w, e := fsPWrite(fd, off+int64(nn), string(b[nn:max]))
		if e == 4 { // EINTR
			continue
		}
		nn += w
		if nn == l && e == 0 {
			return l, nil
		}
		if e != 0 {
			return 0, modelWrapErrno("write", inner, e)
		}
	}
}

// MODEL: (*File).Seek (file.go, file_unix.go's seek, poll.FD.Seek): one lseek(2). Linux computes
// the new offset from 0 (SEEK_SET), the offset (SEEK_CUR) or the size (SEEK_END, the extension's
// Fstat: the model has more errnos than lseek's, only more outcomes), and fails with EINVAL on
// another whence or a negative result, changing nothing; past modelSeekMax ext4 answers EINVAL.
// Not modelled (gomodel.Stuck): a closed file, SEEK_CUR from an unknown offset, a result at or past
// modelOffMax. A directory's fd (Go: EISDIR after Readdirnames) does not arise: Fstat is stuck on it.
func (f *File) Seek(offset int64, whence int) (ret int64, err error) {
	inner := f.file
	fd := inner.pfd.Sysfd
	if fd < 0 {
		gomodel.Stuck()
	}
	cur := inner.off
	var base int64
	var e uintptr
	if whence == 0 {
	} else if whence == 1 {
		if cur < 0 {
			gomodel.Stuck()
		}
		base = cur
	} else if whence == 2 {
		base, e = fsFstat(fd)
	} else {
		e = 22 // EINVAL
	}
	if e != 0 {
		return 0, modelWrapErrno("seek", inner, e)
	}
	n := base + offset
	if n < 0 {
		return 0, modelWrapErrno("seek", inner, 22)
	}
	if modelOffMax <= n || modelOffMax <= base || modelOffMax <= offset {
		gomodel.Stuck()
	}
	if modelSeekMax < n {
		return 0, modelWrapErrno("seek", inner, 22)
	}
	inner.off = n
	return n, nil
}

// MODEL: (*File).Write (file.go, file_posix.go's write, poll.FD.Write): write(2) calls at the file
// offset until all of b is written, EINTR retried, the offset advancing by what was written. A
// write(2) is a pwrite(2) at the offset that then moves it: the model calls WriteAt at off, then
// moves off past b. On an error Go returns the bytes written before it, which WriteAt does not
// keep: the model returns any count, and the offset is unknown (-1). An empty b, for which Go issues
// a zero-byte write(2) whose answer depends on the fd's mode (EBADF on a read-only fd), returns
// (0, nil) or (0, f.wrapErr("write", e)) for any errno, changing nothing (POSIX; measured,
// TestEmptyWrite; examples/osfs/semantics/model_os_writefile.go). Not modelled: a closed file, an
// unknown offset, a write reaching modelOffMax.
func (f *File) Write(b []byte) (n int, err error) {
	inner := f.file
	fd := inner.pfd.Sysfd
	off := inner.off
	l := len(b)
	if fd < 0 {
		gomodel.Stuck()
	}
	if l == 0 {
		e := uintptr(gomodel.ChooseUint64())
		if e == 0 {
			return 0, nil
		}
		return 0, modelWrapErrno("write", inner, e)
	}
	if off < 0 {
		gomodel.Stuck()
	}
	if modelOffMax <= off+int64(l) {
		gomodel.Stuck()
	}
	n, err = f.WriteAt(b, off)
	if err == nil {
		inner.off = off + int64(l)
		return n, err
	}
	inner.off = -1
	return int(gomodel.ChooseUint64()), err
}

// MODEL: (*File).Read (file.go, file_posix.go's read, poll.FD.Read): for a non-empty b, one
// read(2) at the file offset of at most modelMaxRW bytes, EINTR retried; the offset advances by
// what was read; 0 bytes is io.EOF; an error is f.wrapErr("read", e) with n = 0, the offset
// unchanged. A read(2) is a pread(2) at the offset that then moves it (fsPRead at off, its bytes
// copied into b). An empty b returns 0, nil at once (poll.FD.Read). Not modelled: a closed file, an
// unknown offset, a read reaching modelOffMax.
func (f *File) Read(b []byte) (n int, err error) {
	inner := f.file
	fd := inner.pfd.Sysfd
	off := inner.off
	l := len(b)
	if fd < 0 {
		gomodel.Stuck()
	}
	if l == 0 {
		return 0, nil
	}
	if off < 0 {
		gomodel.Stuck()
	}
	if modelOffMax <= off+int64(l) {
		gomodel.Stuck()
	}
	for {
		k := l
		if k > modelMaxRW {
			k = modelMaxRW
		}
		data, e := fsPRead(fd, off, k)
		if e == 4 { // EINTR
			continue
		}
		if e != 0 {
			return 0, modelWrapErrno("read", inner, e)
		}
		m := copy(b, data)
		inner.off = off + int64(m)
		if m == 0 {
			return 0, io.EOF
		}
		return m, nil
	}
}

// MODEL: (*File).Stat (stat_unix.go): fstat(2), EINTR retried, into a fresh fileStat
// (fillFileStatFromSys(&fs, f.name)), an error being f.wrapErr("stat", e) with a nil FileInfo. The
// extension's Fstat gives only the size, and is stuck on a directory's fd, so the mode is a regular
// file's (modelMode(0)); the name is filepathlite.Base(f.name), as fillFileStatFromSys sets it.
func (f *File) Stat() (FileInfo, error) {
	inner := f.file
	fd := inner.pfd.Sysfd
	for {
		size, e := fsFstat(fd)
		if e == 4 { // EINTR
			continue
		}
		if e != 0 {
			return nil, modelWrapErrno("stat", inner, e)
		}
		fs := &fileStat{}
		fs.name = filepathlite.Base(inner.name)
		fs.size = size
		fs.mode = modelMode(0)
		return fs, nil
	}
}

// MODEL: (*File).Truncate (file_posix.go, poll.FD.Ftruncate): ftruncate(2), EINTR retried, an
// error being f.wrapErr("truncate", e). A negative size is EINVAL, which Linux answers before
// looking at the fd, without a system call (the extension's ftruncate is stuck on it). fsFtruncate
// is the extension's FtruncateStart and FtruncateFinish. Not modelled: a closed file.
func (f *File) Truncate(size int64) error {
	inner := f.file
	fd := inner.pfd.Sysfd
	if fd < 0 {
		gomodel.Stuck()
	}
	if size < 0 {
		return modelWrapErrno("truncate", inner, 22)
	}
	for {
		e := fsFtruncate(fd, size)
		if e == 4 { // EINTR
			continue
		}
		if e != 0 {
			return modelWrapErrno("truncate", inner, e)
		}
		return nil
	}
}

// MODEL: (*File).Sync (file_posix.go, poll.FD.Fsync): fsync(2), EINTR retried, an error being
// f.wrapErr("sync", e): the extension's Fsync, DirSync for a directory's fd, OutSync for a
// directory's outside the roots' trees (fsFdKind). A failed Fsync changes nothing (the extension
// assumes no failed writeback) and never returns EINTR.
func (f *File) Sync() error {
	inner := f.file
	fd := inner.pfd.Sysfd
	kind := fsFdKind(fd)
	for {
		var e uintptr
		if kind == 0 {
			e = fsFsync(fd)
		} else if kind == 1 {
			e = fsDirSync(fd)
		} else {
			e = fsOutSync(fd)
		}
		if e == 4 { // EINTR
			continue
		}
		if e != 0 {
			return modelWrapErrno("sync", inner, e)
		}
		return nil
	}
}

// MODEL: Rename (file.go, file_unix.go's rename). Go first Lstat's newname; for a directory it
// returns a LinkError: EEXIST, or the error of the Lstat of oldname (two distinct names of the
// namespace are never the same file: no hard links, a case-sensitive filesystem, so SameFile is
// false). fsLstatDir answers that question (isDir 1 only for a directory, with the errno to return;
// 0 otherwise, and for a directory whose lstat failed, as in Go). Then rename(2), EINTR retried
// (the extension's Rename, after its own CallBegin, each attempt). Go's body is not translated: its
// SameFile reads fileStat.sys, which the models leave zero.
func Rename(oldpath, newpath string) error {
	isDir, le := fsLstatDir(newpath)
	if isDir == 1 {
		return &LinkError{"rename", oldpath, newpath, modelErrno(le)}
	}
	for {
		e := fsRename(oldpath, newpath)
		if e == 4 { // EINTR
			continue
		}
		if e != 0 {
			return &LinkError{"rename", oldpath, newpath, modelErrno(e)}
		}
		return nil
	}
}

// MODEL: (*File).Readdirnames (dir.go, dir_unix.go's readdir) for n <= 0: every name of the
// directory but . and .., read by getdents(2) calls until one returns nothing (EINTR retried); an
// error returns the names so far and &PathError{"readdirent", name, Errno(e)}; the result is never a
// nil slice. The extension's DirReadNext gives a name at a time, with POSIX's readdir across
// concurrent changes; it is stuck on a fd that is not a directory's (Go: ENOTDIR) and on a second
// read of one fd (Go returns no names). n > 0 is not modelled. Before each append the loop assumes
// (an infinite loop otherwise, Perennial's assume) that fewer than 2^44 names were read: Go's append
// panics ("growslice: len out of range") once a []string's capacity passes maxAlloc/16 = 2^44
// (linux/amd64), so the assumption excludes only executions Go ends in that runtime panic, which
// Perennial's append treats as an assumption already
// (examples/osfs/semantics/model_os_readdirnames_len.go).
func (f *File) Readdirnames(n int) (names []string, err error) {
	inner := f.file
	fd := inner.pfd.Sysfd
	if n > 0 {
		gomodel.Stuck()
	}
	names = []string{}
	for {
		nm, done, e := fsDirReadNext(fd)
		if e == 4 { // EINTR
			continue
		}
		if e != 0 {
			return names, modelWrapErrno("readdirent", inner, e)
		}
		if done == 1 {
			return names, nil
		}
		if len(names) >= 1<<44 {
			for {
			}
		}
		names = append(names, nm)
	}
}

// modelStatAbove is Stat's and Lstat's body at a strict ancestor of a root (fsPathKind 2), with no
// extension step: a fresh fileStat of arbitrary size whose mode is ModeDir or ModeSymlink with
// arbitrary other bits, and a nil error; or a nil FileInfo and &PathError{op, name, Errno(e)}, e any
// nonzero errno. The environment keeps each such path an existing directory, or a symlink to one,
// that nothing changes; stat(2) follows the symlink, lstat(2) does not, either may fail (EACCES,
// ENOMEM, ...), and neither changes anything; the model also lets Stat see a symlink (only more
// answers). examples/osfs/semantics/model_os_stat_above.go.
func modelStatAbove(op, name string) (FileInfo, error) {
	if gomodel.Choose() {
		fs := &fileStat{}
		fs.name = filepathlite.Base(name)
		fs.size = int64(gomodel.ChooseUint64())
		ty := ModeSymlink
		if gomodel.Choose() {
			ty = ModeDir
		}
		fs.mode = modelMode(ty)
		return fs, nil
	}
	e := uintptr(gomodel.ChooseUint64())
	if e == 0 {
		e = 2 // ENOENT
	}
	return nil, modelPathError(op, name, modelErrno(e))
}

// modelStat is Stat's and Lstat's body (stat_unix.go's statNolog/lstatNolog): one stat(2) (or
// lstat(2)) of the path, EINTR retried, into a fresh fileStat; an error is &PathError{op, name,
// Errno(e)} with a nil FileInfo. The extension has no stat of a path, so the model asks what a stat
// would by the steps it has: open(name, O_RDONLY|O_CLOEXEC) (fsOpen), whose fd says whether the path
// is a file or a directory (fsFdKind), the size of a file (fsFstat), and the fd closed at once (its
// errno ignored). This contains every answer of Linux's stat: an open without O_CREAT/O_TRUNC
// changes no state but the fd table (the fd freed before the model returns; fd numbers are chosen
// arbitrarily by the extension, so no other thread can tell); where stat succeeds the path exists
// (in the roots' trees every entry is a regular file or a directory, with no symlinks, so stat and
// lstat agree), and Open, FdKind and Fstat can succeed with its kind and size (permissions are not
// modelled), and where it fails Open can fail with the same errno. At an ancestor of a root
// (fsPathKind 2), modelStatAbove. examples/osfs/semantics/model_os_stat.go, model_os_stat_above.go.
func modelStat(op, name string) (FileInfo, error) {
	if fsPathKind(name) == 2 {
		return modelStatAbove(op, name)
	}
	for {
		fd, e := fsOpen(name, modelOpenFlags, 0)
		if e == 4 { // EINTR
			continue
		}
		if e != 0 {
			return nil, modelPathError(op, name, modelErrno(e))
		}
		kind := fsFdKind(fd)
		var size int64
		var ze uintptr
		if kind == 0 {
			size, ze = fsFstat(fd)
		} else {
			size = int64(gomodel.ChooseUint64())
		}
		if kind == 0 {
			fsClose(fd)
		} else {
			fsDirClose(fd)
		}
		if ze == 4 { // EINTR
			continue
		}
		if ze != 0 {
			return nil, modelPathError(op, name, modelErrno(ze))
		}
		fs := &fileStat{}
		fs.name = filepathlite.Base(name)
		fs.size = size
		if kind == 0 {
			fs.mode = modelMode(0)
		} else {
			fs.mode = modelMode(ModeDir)
		}
		return fs, nil
	}
}

// MODEL: Stat (stat.go): testlog.Stat(name), a no-op outside go test's logging (its logger is
// nil), then statNolog: modelStat with Op "stat".
func Stat(name string) (FileInfo, error) {
	return modelStat("stat", name)
}

// MODEL: Lstat (stat.go): testlog.Stat(name), then lstatNolog: modelStat with Op "lstat". In the
// roots' trees there are no symlinks and no root is one (the extension's environment), so lstat
// answers as stat does on every path below an ancestor of a root.
func Lstat(name string) (FileInfo, error) {
	return modelStat("lstat", name)
}

// modelUnlinkLoop is unlink(2) of p, each attempt after its own CallBegin, EINTR retried: the errno.
func modelUnlinkLoop(p string) uintptr {
	for {
		e := fsUnlink(p)
		if e != 4 {
			return e
		}
	}
}

// modelRmdirLoop is rmdir(2) of p, each attempt after its own CallBegin, EINTR retried: the errno.
func modelRmdirLoop(p string) uintptr {
	for {
		e := fsRmdir(p)
		if e != 4 {
			return e
		}
	}
}

// modelOpenLoop is open(p, O_RDONLY|O_CLOEXEC), each attempt after its own CallBegin, EINTR
// retried: (fd, errno).
func modelOpenLoop(p string) (int, uintptr) {
	for {
		fd, e := fsOpen(p, modelOpenFlags, 0)
		if e != 4 {
			return fd, e
		}
	}
}

// modelCloseFd closes the fd of a file or of a directory (fsFdKind), ignoring the errno.
func modelCloseFd(fd int) {
	if fsFdKind(fd) == 0 {
		fsClose(fd)
	} else {
		fsDirClose(fd)
	}
}

// modelPrefixPath is `pe.Path = pre + "/" + pe.Path` for a non-nil pe (removeall_at.go).
func modelPrefixPath(pe *PathError, pre string) {
	if pe == nil {
		return
	}
	pe.Path = pre + "/" + pe.Path
}

// modelRemoveAllFrom is removeAllFrom(parentFd, base) (removeall_at.go), with the entry named by its
// path parent + "/" + base instead of base under the fd of parent (RemoveAll says why that is
// faithful): a *PathError (nil for success) whose Path is relative to parent, as Go's. Go:
//
//	err := removefileat(parentFd, base)            // unlinkat(parentFd, base, 0), EINTR retried
//	if err == nil || IsNotExist(err) { return nil }
//	if err != EISDIR && err != EPERM && err != EACCES { return &PathError{"unlinkat", base, err} }
//	uErr := err
//	for {
//		file, err := openDirAt(parentFd, base)   // openat(O_DIRECTORY|O_NOFOLLOW|O_CLOEXEC)
//		if err != nil {
//			if IsNotExist(err) { return nil }
//			if err == ENOTDIR { return &PathError{"unlinkat", base, uErr} }
//			recurseErr = &PathError{"openfdat", base, err}; break   // (no symlinks in the trees)
//		}
//		for { names, readErr := file.Readdirnames(1024); ... removeAllFrom(file.Fd(), name) for each,
//		      prefixing base to a *PathError's Path, recurseErr = the first; until a chunk not all failed }
//		file.Close()
//		if respSize < reqSize { break }
//	}
//	unlinkError := removedirat(parentFd, base)      // unlinkat(parentFd, base, AT_REMOVEDIR)
//	if unlinkError == nil || IsNotExist(unlinkError) { return nil }
//	if recurseErr != nil { return recurseErr }
//	return &PathError{"unlinkat", base, unlinkError}
//
// The unlinkats are the extension's Unlink and Rmdir of the path, and openDirAt its Open of the path
// (O_RDONLY|O_CLOEXEC: the extension does not take O_DIRECTORY; an fd of a file is closed and
// answered as ENOTDIR, which Linux returns without opening). The reads of a pass are all of the
// directory (DirReadNext until the end, EINTR retried; an error is &PathError{"readdirnames", base,
// &PathError{"readdirent", base, Errno(e)}}, as Go's), all of whose names are then removed. Go's pass
// reads a chunk of up to 1024 names, removes them, closes and reopens the directory, so under a
// concurrent creation a later pass reads new entries mixed with old ones not yet removed (measured;
// notes/wal-fsext-models-review.md, finding 3). The model still has each such run, for a reason that
// is load-bearing: the extension's Unlink and Rmdir may fail with any errno and no effect, ENOENT
// included, and ENOENT is success here (IsNotExist, no error recorded). So the model's first pass may
// read every name and remove only Go's first chunk, and each later pass reads what Go's next one
// reads and does the same. A tightening of the extension's failure branches (ENOENT only when there
// is no entry) would make this model unsound. Whether another pass follows is a choice: Go makes one
// more exactly when a chunk was full, which depends on the directory's size and on entries added
// meanwhile. Errnos: ENOENT 2, ENOTDIR 20, EISDIR 21, EPERM 1, EACCES 13.
func modelRemoveAllFrom(parent, base string) *PathError {
	p := parent + "/" + base
	e := modelUnlinkLoop(p)
	if e == 0 || e == 2 {
		return nil
	}
	if e != 21 && e != 1 && e != 13 {
		return modelPathErrorPtr("unlinkat", base, modelErrno(e))
	}
	var rerr *PathError
	for {
		fd, oe := modelOpenLoop(p)
		if oe != 0 {
			if oe == 2 {
				return nil
			}
			if oe == 20 {
				return modelPathErrorPtr("unlinkat", base, modelErrno(e))
			}
			rerr = modelPathErrorPtr("openfdat", base, modelErrno(oe))
			break
		}
		if fsFdKind(fd) == 0 {
			fsClose(fd)
			return modelPathErrorPtr("unlinkat", base, modelErrno(e))
		}
		names := []string{}
		var re uintptr
		for {
			nm, done, x := fsDirReadNext(fd)
			if x == 4 { // EINTR
				continue
			}
			if x != 0 {
				re = x
				break
			}
			if done == 1 {
				break
			}
			names = append(names, nm)
		}
		if re != 0 {
			fsDirClose(fd)
			if re == 2 {
				return nil
			}
			return modelPathErrorPtr("readdirnames", base,
				modelPathError("readdirent", base, modelErrno(re)))
		}
		n := len(names)
		for k := 0; k < n; k++ {
			pe := modelRemoveAllFrom(p, names[k])
			modelPrefixPath(pe, base)
			if rerr == nil {
				rerr = pe
			}
		}
		fsDirClose(fd)
		if !gomodel.Choose() { // another pass, or not (Go: false, one pass)
			break
		}
	}
	e4 := modelRmdirLoop(p)
	if e4 == 0 || e4 == 2 {
		return nil
	}
	if rerr != nil {
		return rerr
	}
	return modelPathErrorPtr("unlinkat", base, modelErrno(e4))
}

// MODEL: RemoveAll (path.go, removeall_at.go). Go's body:
//
//	if path == "" { return nil }
//	if endsWithDot(path) { return &PathError{"RemoveAll", path, EINVAL} }
//	err := Remove(path)
//	if err == nil || IsNotExist(err) { return nil }
//	parentDir, base := splitPath(path)
//	parent, err := OpenFile(parentDir, O_RDONLY, 0)
//	if IsNotExist(err) { return nil }
//	if err != nil { return err }
//	defer parent.Close()
//	if err := removeAllFrom(parent.Fd(), base); err != nil {
//		if pathErr, ok := err.(*PathError); ok { pathErr.Path = parentDir + "/" + pathErr.Path }
//		return err
//	}
//	return nil
//
// Below Remove it is over the *at system calls (unlinkat, openat relative to a directory's fd),
// which the extension does not have (its steps name paths). The model is that body over paths:
// Remove inlined (for its errno), the parent opened as OpenFile does (and closed), and removeAllFrom
// with each entry named by its path (modelRemoveAllFrom). A path and a name under an open
// directory's fd name the same entry as long as no directory above it is moved: the model holds a
// CallBegin of path from its start to its return (fsWithCall), so that every rename of a directory
// in path's root's tree by another thread is stuck while it runs (the extension's Rename), and the
// proved programs, which are never stuck, have no such rename. What is left is a directory above it
// removed and another made in its place by another thread (Go's *at calls then act on the removed
// one, which no path names, and fail or change nothing a path can see; the model's calls on the new
// one may fail with any errno and no effect, the outcome Linux's leave visible). path must be
// strictly below a root and canonical: the model is stuck on any other (as every path step).
// examples/osfs/semantics/model_os_removeall.go.
func RemoveAll(path string) error {
	if path == "" {
		return nil
	}
	if endsWithDot(path) {
		return modelPathError("RemoveAll", path, modelErrno(22))
	}
	return fsWithCall(path, func() error {
		e := modelUnlinkLoop(path)
		if e == 0 {
			return nil
		}
		e1 := modelRmdirLoop(path)
		if e1 == 0 {
			return nil
		}
		if e1 != 20 { // ENOTDIR: Remove keeps unlink's errno
			e = e1
		}
		if e == 2 {
			return nil
		}
		parentDir, base := splitPath(path)
		fd, oe := modelOpenLoop(parentDir)
		if oe == 2 {
			return nil
		}
		if oe != 0 {
			return modelPathError("open", parentDir, modelErrno(oe))
		}
		pe := modelRemoveAllFrom(parentDir, base)
		modelCloseFd(fd)
		if pe == nil {
			return nil
		}
		modelPrefixPath(pe, parentDir)
		return pe
	})
}

// modelCopyFileRangeRound is one copy_file_range(src, NULL, dst, NULL, max, 0) (poll.copyFileRange's
// unix.CopyFileRange, file offsets used and updated) between the files dst and src: (n, errno). On
// configuration C (ext4, no remap_file_range) Linux copies through the page cache: it reads the
// source from its offset and writes what it read at the destination's offset (the path of
// pwrite(2)), returns the count written (short on an error after progress, or the error with
// nothing written), and advances both offsets by it. The model is that read and that write (fsPRead,
// fsPWrite), then both offsets move by the count written. One round being one PRead makes the read
// atomic where Linux reads page by page; PRead's short counts make every finer split a sequence of
// rounds, which Go's loop issues anyway, so the model has every outcome of Linux's. Every errno Linux
// can give with nothing copied (EINVAL, EXDEV, EBADF, EINTR, ...) is one of PRead's (any). Not
// modelled: a closed file, an unknown offset, offsets reaching modelOffMax.
// examples/osfs/semantics/model_os_copy_file_range.go.
func modelCopyFileRangeRound(dst, src *file, max int64) (int64, uintptr) {
	dfd := dst.pfd.Sysfd
	sfd := src.pfd.Sysfd
	doff := dst.off
	soff := src.off
	if dfd < 0 || sfd < 0 {
		gomodel.Stuck()
	}
	if doff < 0 || soff < 0 {
		gomodel.Stuck()
	}
	if modelOffMax <= doff+max || modelOffMax <= soff+max {
		gomodel.Stuck()
	}
	data, e := fsPRead(sfd, soff, int(max))
	if e != 0 {
		return 0, e
	}
	if len(data) == 0 { // the source's end
		return 0, 0
	}
	w, we := fsPWrite(dfd, doff, data)
	if w == 0 {
		return 0, we
	}
	src.off = soff + int64(w)
	dst.off = doff + int64(w)
	return int64(w), 0
}

// modelHandleCopyFileRangeErr is internal/poll's handleCopyFileRangeErr (copy_file_range_linux.go),
// copied verbatim: os cannot call poll's unexported function.
func modelHandleCopyFileRangeErr(err error, copied, written int64) (bool, error) {
	switch err {
	case syscall.ENOSYS:
		return false, nil
	case syscall.EXDEV, syscall.EINVAL, syscall.EIO, syscall.EOPNOTSUPP, syscall.EPERM:
		return false, nil
	case nil:
		if copied == 0 {
			if written == 0 {
				return false, nil
			}
		}
	}
	return true, err
}

// modelPollCopyFileRange is poll.CopyFileRange(&dst.pfd, &src.pfd, remain) (copy_file_range_unix.go)
// over the two files:
//
//	if !supportCopyFileRange() { return 0, false, nil }
//	for remain > 0 {
//		max := min(remain, maxCopyFileRangeRound)
//		n, e := copyFileRange(dst, src, int(max))   // ignoringEINTR2(unix.CopyFileRange(...))
//		if n > 0 { remain -= n; written += n }
//		handled, err = handleCopyFileRangeErr(e, n, written)
//		if n == 0 || !handled || err != nil { return }
//	}
//	return written, true, nil
//
// supportCopyFileRange() (KernelVersionGE(5, 3)) is true on configuration C (Linux 7.0).
// copyFileRange's writeLock/readLock (fdMutex, failing only on a closed file) are not modelled (as
// Read/Write do not lock either); one round is modelCopyFileRangeRound, EINTR retried.
func modelPollCopyFileRange(dst, src *file, remain int64) (written int64, handled bool, err error) {
	for {
		if remain <= 0 {
			return written, true, nil
		}
		max := remain
		if !(remain < 0x7ffff000) { // maxCopyFileRangeRound
			max = 0x7ffff000
		}
		var n int64
		var c uintptr
		for {
			n, c = modelCopyFileRangeRound(dst, src, max)
			if c != 4 { // EINTR
				break
			}
		}
		if 0 < n {
			remain -= n
			written += n
		}
		handled, err = modelHandleCopyFileRangeErr(modelErrno(c), n, written)
		if n == 0 || !handled || err != nil {
			return written, handled, err
		}
	}
}

// MODEL: (*File).copyFileRange (zero_copy_linux.go): Go's body, with
// pollCopyFileRange(&f.pfd, &src.pfd, remain) as modelPollCopyFileRange of the two files (it needs
// their kernel offsets, which poll.FD does not hold). Go reads the function from the package
// variable pollCopyFileRange, which only os's tests reassign.
func (f *File) copyFileRange(r io.Reader) (written int64, handled bool, err error) {
	var (
		remain int64
		lr     *io.LimitedReader
	)
	if lr, r, remain = tryLimitedReader(r); remain <= 0 {
		return 0, true, nil
	}

	var src *File
	switch v := r.(type) {
	case *File:
		src = v
	case fileWithoutWriteTo:
		src = v.File
	default:
		return 0, false, nil
	}

	if src.checkValid("ReadFrom") != nil {
		return 0, false, nil
	}

	written, handled, err = modelPollCopyFileRange(f.file, src.file, remain)
	if lr != nil {
		lr.N -= written
	}
	return written, handled, wrapSyscallError("copy_file_range", err)
}
