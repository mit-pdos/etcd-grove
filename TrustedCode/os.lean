/-
Trusted Go model of `os` (namespace of the generated package; project bboltfs of `etc/goose.py`,
`Code/os.toml`), in terms of the Linux file extension of `GooseLang.Ext.OsFs.Impl` (`osFsExt`,
`ExternalOp osFsExt.name "PRead"`, ...), for any program whose extensions include it.
linux/amd64, Go 1.27.3 (`etc/goose.py`'s `GO_TOOLCHAIN`). Perennial's own translation of `os`
(`Perennial.Code.os`) trusts nothing and must not be in the same import closure.

**Files.** Go's `File` is `struct{ *file }` (`types.go`), with `file` (`file_unix.go`) holding a
`poll.FD` (the fd `Sysfd`, a reference count and the poller), the name and flags. goose translates
`File` as it is (a struct whose one field `file` points to a `file`); `file` is trusted, with the
layout `struct{ fd int; name string }` (`file.underlying`): `fd` is `pfd.Sysfd`, and `name` the
name. Copies of a `File` value share the inner cell, as in Go. The other fields of Go's `file`
are not observable to code outside `os` (they are unexported), and the methods modelled here do
not depend on them for a file `OpenFile` returns: `nonblock` and `appendMode` are false
(`O_APPEND` and `O_NONBLOCK` are among the flags the extension's `Open` refuses), `dirinfo` is
nil. `Name` is translated, the real `return f.name`, over this layout; so is `fileStat.Size`.

**Faithfulness.** Each model is the Go method with the `poll.FD` calls replaced by the extension's
operations, and with Go's retries of `EINTR` (`ignoringEINTR`, `ignoringEINTR2`, `Pwrite`'s loop)
kept. Errors are as Go makes them: `&PathError{Op, Path: f.name, Err: Errno(e)}` (`wrapErr`), and
`io.EOF` unwrapped. The model is less defined than Go (stuck) where Go's answer depends on what is
not modelled: a nil `*File` or a zero `File` (Go returns `ErrInvalid` or `EINVAL`), and a closed
file (`Close` sets `fd` to -1, as Go's `pfd.destroy` sets `Sysfd`; Go then returns `ErrClosed`,
while the extension is stuck on fd -1), including a method racing `Close` (Go's reference count
makes that safe; in the model it is a race on the inner cell, or an operation on a closed fd).
Unrelated to the extension: an open file's finalizer (`notes/osfs-ext-plan.md`, D5).
-/
module

public import Perennial.Golang.Defn
public import Perennial.Code.errors
public import Perennial.Code.io
public import Code.io.fs
public import Code.syscall
public import GooseLang.Ext.OsFs.Impl

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace os

/-- The model's `file` (`file.underlying`): the fd and the name. -/
structure file where
  mk ::
  fd' : w64
  name' : GoString

instance file.zero_val : ZeroVal file := ⟨file.mk zeroValDef zeroValDef⟩

/-- The model's `fileStat` (`fileStat.underlying`): the size. -/
structure fileStat where
  mk ::
  size' : w64

instance fileStat.zero_val : ZeroVal fileStat := ⟨fileStat.mk zeroValDef⟩

section code
variable [GooseExts] [GoGlobalContext]

/-- `file` (`file_unix.go`): `pfd.Sysfd` as `fd`, and `name` (the module docstring says why the
other fields are not needed). -/
@[reducible] def file.underlying : go.GoType :=
  go.GoType.StructType [go.field_decl.FieldDecl go!"fd" go.int,
    go.field_decl.FieldDecl go!"name" go.string]

/-- `fileStat` (`types_unix.go`): only `size`. A `fileStat` is made only by `Stat.impl`, and its
methods but `Size` (`Name`, `Mode`, `ModTime`, `IsDir`, `Sys`) are not translated (stuck). -/
@[reducible] def fileStat.underlying : go.GoType :=
  go.GoType.StructType [go.field_decl.FieldDecl go!"size" go.int64]

/-! The types as goose names them (their `.ty` is in `Code.os`, which imports this file), and
helpers of the models (not Go functions). -/

@[reducible] def model.File : go.GoType := go.GoType.Named go!"os.File" []
@[reducible] def model.file : go.GoType := go.GoType.Named go!"os.file" []
@[reducible] def model.fileStat : go.GoType := go.GoType.Named go!"os.fileStat" []

/-- `f.file`, for a `*File` `f`. -/
noncomputable def model.inner : val :=
  λ: "f", ![go.PointerType model.file] (StructFieldRef model.File go!"file" "f")

/-- `&PathError{Op: op, Path: path, Err: err}` as an `error`. -/
noncomputable def model.pathError : val :=
  λ: "op" "path" "err",
    let: "pe" := GoAlloc io.fs.PathError.ty (GoZeroVal io.fs.PathError.ty #()) in
    StructFieldRef io.fs.PathError.ty go!"Op" "pe" <-[go.string] "op" ;;
    StructFieldRef io.fs.PathError.ty go!"Path" "pe" <-[go.string] "path" ;;
    StructFieldRef io.fs.PathError.ty go!"Err" "pe" <-[go.error] "err" ;;
    Convert (go.PointerType io.fs.PathError.ty) go.error "pe"

/-- `f.wrapErr(op, Errno(e))` for an errno `e ≠ 0` of the file at `inner`. -/
noncomputable def model.wrapErrno : val :=
  λ: "op" "inner" "e",
    model.pathError "op" (![go.string] (StructFieldRef model.file go!"name" "inner"))
      (syscall.model.errno "e")

/-- `OpenFile(name string, flag int, perm FileMode) (*File, error)` (`file.go`, `file_unix.go`):

```go
	ignoringEINTR(func() error {
		r, s, e = open(name, flag|syscall.O_CLOEXEC, syscallMode(perm))
		return e
	})
	if e != nil {
		return nil, &PathError{Op: "open", Path: name, Err: e}
	}
	f := newFile(r, name, kindOpenFile, unix.HasNonblockFlag(flag))
	...
	f.appendMode = flag&O_APPEND != 0
```

`open` is `openat(AT_FDCWD, name, flag|O_CLOEXEC|O_LARGEFILE, perm)`, `O_LARGEFILE` being 0 on
amd64: the extension's `Open` (`(name, flags) ↦ (fd, errno)`, stuck on a path outside its domain
or on a flag it does not support, among them `O_APPEND`, `O_EXCL`, `O_SYNC` and `O_NONBLOCK`).
`newFile` makes the `File{&file{...}}` with the fd and the name; its other work (an `fstat` to
decide that a regular file is not pollable, the finalizer) is invisible to Go code. `perm` matters
only to the mode of a created file, which the extension does not model. A name with a NUL byte,
where Go returns `EINVAL` without a system call, is not a path of the domain (the environment
assumptions of `GooseLang/Ext/OsFs/Impl.lean`). -/
noncomputable def OpenFile.impl : val :=
  λ: "name" "flag" "perm",
    (rec: "open" <> :=
      let: "r" := ExternalOp osFsExt.name "Open" ("name", "flag" |⟨go.int⟩ #(W64 0x80000)) in
      if: Snd "r" =⟨go.uintptr⟩ #(W64 0) then
        let: "inner" := GoAlloc model.file (GoZeroVal model.file #()) in
        StructFieldRef model.file go!"fd" "inner" <-[go.int] Fst "r" ;;
        StructFieldRef model.file go!"name" "inner" <-[go.string] "name" ;;
        let: "f" := GoAlloc model.File (GoZeroVal model.File #()) in
        StructFieldRef model.File go!"file" "f" <-[go.PointerType model.file] "inner" ;;
        ("f", #GoInterface.nil)
      else if: Snd "r" =⟨go.uintptr⟩ #(W64 4) then "open" #() -- EINTR
      else (#null, model.pathError #"open" "name" (syscall.model.errno (Snd "r")))) #()

/-- `(*File).Fd() uintptr` (`file_unix.go`): `uintptr(f.pfd.Sysfd)` (`nonblock` is false), the
fd, or `^uintptr(0)` after `Close`, which sets it to -1. -/
noncomputable def File.Fd.impl : val :=
  λ: "f" <>,
    Convert go.int go.uintptr (![go.int] (StructFieldRef model.file go!"fd" (model.inner "f")))

/-- `(*File).Close() error` (`file_posix.go`, `file_unix.go`'s `file.close`): `pfd.Close`, which
closes the fd (`close(2)`, not retried on `EINTR`: Linux frees the fd whatever the errno) and sets
`Sysfd` to -1; an error is `&PathError{"close", name, Errno(e)}`. The extension's `Close` frees the
fd whatever the errno it returns. -/
noncomputable def File.Close.impl : val :=
  λ: "f" <>,
    let: "inner" := model.inner "f" in
    let: "fd" := ![go.int] (StructFieldRef model.file go!"fd" "inner") in
    StructFieldRef model.file go!"fd" "inner" <-[go.int] #(-1 : w64) ;;
    let: "e" := ExternalOp osFsExt.name "Close" "fd" in
    if: "e" =⟨go.uintptr⟩ #(W64 0) then #GoInterface.nil
    else model.wrapErrno #"close" "inner" "e"

/-- `(*File).ReadAt(b []byte, off int64) (n int, err error)` (`file.go`, with `poll.FD.Pread`):

```go
	if off < 0 {
		return 0, &PathError{Op: "readat", Path: f.name, Err: errors.New("negative offset")}
	}
	for len(b) > 0 {
		m, e := f.pread(b, off)   // Pread: at most maxRW (1 << 30) bytes; EINTR retried;
		if e != nil {             // m = 0 on an error; m = 0 and no error is io.EOF
			err = f.wrapErr("read", e)   // io.EOF stays io.EOF
			break
		}
		n += m
		b = b[m:]
		off += int64(m)
	}
	return
```

A negative offset returns Go's error without a system call. Each `pread(2)` is the extension's
`PRead` (`(fd, off, n) ↦ (data, errno)`), whose data (a string) is copied into `b` with Go's
`copy` (as goose translates `copy(b, s)`: `copy(b, []byte(s))`); a failed `pread` may have
written a prefix of `b`, which the model copies too and does not count, as Go does not. A short
read is followed by another; a read of 0 bytes ends it with `io.EOF`. -/
noncomputable def File.ReadAt.impl : val :=
  λ: "f" "b" "off",
    let: "inner" := model.inner "f" in
    if: "off" <⟨go.int64⟩ #(W64 0) then
      (#(W64 0), model.pathError #"readat"
        (![go.string] (StructFieldRef model.file go!"name" "inner"))
        ((FuncResolve errors.New []) #() #"negative offset"))
    else
      let: "fd" := ![go.int] (StructFieldRef model.file go!"fd" "inner") in
      (rec: "loop" "b" "off" "n" :=
        let: "len" := (FuncResolve go.len [go.GoType.SliceType go.byte]) #() "b" in
        if: "len" =⟨go.int⟩ #(W64 0) then ("n", #GoInterface.nil)
        else
          let: "r" := ExternalOp osFsExt.name "PRead" ("fd", ("off",
            if: "len" >⟨go.int⟩ #(W64 0x40000000) then #(W64 0x40000000) else "len")) in
          let: "m" := (FuncResolve go.copy [go.GoType.SliceType go.byte]) #() "b"
            (Convert go.string (go.GoType.SliceType go.byte) (Fst "r")) in
          if: Snd "r" =⟨go.uintptr⟩ #(W64 4) then "loop" "b" "off" "n" -- EINTR
          else if: Snd "r" ≠⟨go.uintptr⟩ #(W64 0) then
            ("n", model.wrapErrno #"read" "inner" (Snd "r"))
          else if: "m" =⟨go.int⟩ #(W64 0) then
            ("n", ![go.error] (GlobalVarAddr io.EOF #()))
          else
            "loop" (Slice (go.GoType.SliceType go.byte) ("b", "m", "len"))
              ("off" +⟨go.int64⟩ Convert go.int go.int64 "m") ("n" +⟨go.int⟩ "m"))
        "b" "off" #(W64 0)

/-- `(*File).WriteAt(b []byte, off int64) (n int, err error)` (`file.go`, with
`poll.FD.Pwrite`):

```go
	if off < 0 {
		return 0, &PathError{Op: "writeat", Path: f.name, Err: errors.New("negative offset")}
	}
	for len(b) > 0 {
		m, e := f.pwrite(b, off)
		if e != nil {
			err = f.wrapErr("write", e)
			break
		}
		n += m; b = b[m:]; off += int64(m)
	}
	return

func (fd *FD) Pwrite(p []byte, off int64) (int, error) {
	var nn int
	for {
		max := len(p)
		if fd.IsStream && max-nn > maxRW {   // IsStream is true for an os.File
			max = nn + maxRW
		}
		n, err := syscall.Pwrite(fd.Sysfd, p[nn:max], off+int64(nn))
		if err == syscall.EINTR {
			continue
		}
		if n > 0 {
			nn += n
		}
		if nn == len(p) {
			return nn, err
		}
		if err != nil {
			return nn, err
		}
		if n == 0 {
			return nn, io.ErrUnexpectedEOF
		}
	}
}
```

`Pwrite` returns all of `p` written, or an error, so `WriteAt`'s loop runs once: `(len(b), nil)`
or `(0, PathError{"write", ...})` (`n` is not incremented on an error). A negative offset returns
Go's error without a system call. Each `pwrite(2)` is the extension's two steps, `PWriteStart`
(`(fd, off, data) ↦ token`) and `PWriteFinish` (`token ↦ (written, errno)`), with the data passed
as `string(p[nn:max])`, as goose models `string(b)`. `PWriteFinish` writes all of the data with
errno 0, or a prefix with a nonzero errno, which the loop treats as Go treats the system call's
`(n, err)`; with errno 0 it always writes something, so the `io.ErrUnexpectedEOF` branch is
unreachable and not modelled. -/
noncomputable def File.WriteAt.impl : val :=
  λ: "f" "b" "off",
    let: "inner" := model.inner "f" in
    if: "off" <⟨go.int64⟩ #(W64 0) then
      (#(W64 0), model.pathError #"writeat"
        (![go.string] (StructFieldRef model.file go!"name" "inner"))
        ((FuncResolve errors.New []) #() #"negative offset"))
    else
      let: "fd" := ![go.int] (StructFieldRef model.file go!"fd" "inner") in
      let: "len" := (FuncResolve go.len [go.GoType.SliceType go.byte]) #() "b" in
      if: "len" =⟨go.int⟩ #(W64 0) then (#(W64 0), #GoInterface.nil)
      else
        (rec: "pwrite" "nn" :=
          let: "max" := if: ("len" -⟨go.int⟩ "nn") >⟨go.int⟩ #(W64 0x40000000)
            then "nn" +⟨go.int⟩ #(W64 0x40000000) else "len" in
          let: "t" := ExternalOp osFsExt.name "PWriteStart" ("fd",
            ("off" +⟨go.int64⟩ Convert go.int go.int64 "nn",
             Convert (go.GoType.SliceType go.byte) go.string
               (Slice (go.GoType.SliceType go.byte) ("b", "nn", "max")))) in
          let: "r" := ExternalOp osFsExt.name "PWriteFinish" "t" in
          if: Snd "r" =⟨go.uintptr⟩ #(W64 4) then "pwrite" "nn" -- EINTR
          else
            let: "nn" := "nn" +⟨go.int⟩ Fst "r" in
            if: ("nn" =⟨go.int⟩ "len") && (Snd "r" =⟨go.uintptr⟩ #(W64 0)) then
              ("len", #GoInterface.nil)
            else if: Snd "r" ≠⟨go.uintptr⟩ #(W64 0) then
              (#(W64 0), model.wrapErrno #"write" "inner" (Snd "r"))
            else "pwrite" "nn") #(W64 0)

/-- `(*File).Stat() (FileInfo, error)` (`stat_unix.go`): `pfd.Fstat` (`fstat(2)`, `EINTR`
retried) into a fresh `fileStat`, an error being `&PathError{"stat", name, Errno(e)}`. The
extension's `Fstat` gives only the size (`fd ↦ (size, errno)`), which is all the model's
`fileStat` holds; it is returned as a `FileInfo` (`&fs`), whose `Size()` reads it. -/
noncomputable def File.Stat.impl : val :=
  λ: "f" <>,
    let: "inner" := model.inner "f" in
    let: "fd" := ![go.int] (StructFieldRef model.file go!"fd" "inner") in
    (rec: "fstat" <> :=
      let: "r" := ExternalOp osFsExt.name "Fstat" "fd" in
      if: Snd "r" =⟨go.uintptr⟩ #(W64 4) then "fstat" #() -- EINTR
      else if: Snd "r" ≠⟨go.uintptr⟩ #(W64 0) then
        (GoZeroVal io.fs.FileInfo.ty #(), model.wrapErrno #"stat" "inner" (Snd "r"))
      else
        let: "fs" := GoAlloc model.fileStat (GoZeroVal model.fileStat #()) in
        StructFieldRef model.fileStat go!"size" "fs" <-[go.int64] Fst "r" ;;
        (Convert (go.PointerType model.fileStat) io.fs.FileInfo.ty "fs", #GoInterface.nil)) #()

/-- `(*File).Truncate(size int64) error` (`file_posix.go`, `poll.FD.Ftruncate`): `ftruncate(2)`,
`EINTR` retried, an error being `&PathError{"truncate", name, Errno(e)}`. The extension's
`ftruncate` is two steps, `FtruncateStart` (`(fd, size) ↦ token`) and `FtruncateFinish`
(`token ↦ errno`), stuck on a negative size; Linux answers a negative size with `EINVAL` before
looking at the fd, so the model returns that without a system call. On a closed file (fd -1) Go
returns `ErrClosed` before the system call, so the model is stuck there first. -/
noncomputable def File.Truncate.impl : val :=
  λ: "f" "size",
    let: "inner" := model.inner "f" in
    let: "fd" := ![go.int] (StructFieldRef model.file go!"fd" "inner") in
    if: "fd" <⟨go.int⟩ #(W64 0) then Panic "os: Truncate of a closed file not modelled"
    else if: "size" <⟨go.int64⟩ #(W64 0) then model.wrapErrno #"truncate" "inner" #(W64 22)
    else
      (rec: "ftruncate" <> :=
        let: "e" := ExternalOp osFsExt.name "FtruncateFinish"
          (ExternalOp osFsExt.name "FtruncateStart" ("fd", "size")) in
        if: "e" =⟨go.uintptr⟩ #(W64 4) then "ftruncate" #() -- EINTR
        else if: "e" ≠⟨go.uintptr⟩ #(W64 0) then model.wrapErrno #"truncate" "inner" "e"
        else #GoInterface.nil) #()

/-- `(*File).Sync() error` (`file_posix.go`, `poll.FD.Fsync`): `fsync(2)`, `EINTR` retried (each
failed attempt loses the writeback of the dirty bytes, D2, as on Linux), an error being
`&PathError{"sync", name, Errno(e)}`: the extension's `Fsync` (`fd ↦ errno`). -/
noncomputable def File.Sync.impl : val :=
  λ: "f" <>,
    let: "inner" := model.inner "f" in
    let: "fd" := ![go.int] (StructFieldRef model.file go!"fd" "inner") in
    (rec: "fsync" <> :=
      let: "e" := ExternalOp osFsExt.name "Fsync" "fd" in
      if: "e" =⟨go.uintptr⟩ #(W64 4) then "fsync" #() -- EINTR
      else if: "e" ≠⟨go.uintptr⟩ #(W64 0) then model.wrapErrno #"sync" "inner" "e"
      else #GoInterface.nil) #()

end code
end os

end Perennial
