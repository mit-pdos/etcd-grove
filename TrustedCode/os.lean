/-
Trusted Go model of `os` (namespace of the generated package; project bboltfs of `etc/goose.py`,
`Code/os.toml`), in terms of the Linux file extension of `GooseLang.Ext.OsFs.Impl` (`osFsExt`,
`ExternalOp osFsExt.name "PRead"`, ...), for any program whose extensions include it.
linux/amd64, Go 1.27.3 (`etc/goose.py`'s `GO_TOOLCHAIN`). Perennial's own translation of `os`
(`Perennial.Code.os`) trusts nothing and must not be in the same import closure.

**Files.** Go's `File` is `struct{ *file }` (`types.go`), with `file` (`file_unix.go`) holding a
`poll.FD` (the fd `Sysfd`, a reference count and the poller), the name and flags. goose translates
`File` as it is (a struct whose one field `file` points to a `file`); `file` is trusted, with the
layout `struct{ fd int; name string; off int64 }` (`file.underlying`): `fd` is `pfd.Sysfd`, `name`
the name, and `off` the file offset of the fd's open file description (the kernel's `f_pos`,
which Go does not keep: `Seek`, `Write` and `Read` use it, below). Copies of a `File` value share
the inner cell, as in Go. The other fields of Go's `file`
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

/-- The model's `file` (`file.underlying`): the fd, the name and the file offset. -/
structure file where
  mk ::
  fd' : w64
  name' : GoString
  off' : w64

instance file.zero_val : ZeroVal file := ⟨file.mk zeroValDef zeroValDef zeroValDef⟩

/-- The model's `fileStat` (`fileStat.underlying`): the size. -/
structure fileStat where
  mk ::
  size' : w64

instance fileStat.zero_val : ZeroVal fileStat := ⟨fileStat.mk zeroValDef⟩

section code
variable [GooseExts] [GoGlobalContext]

/-- `file` (`file_unix.go`): `pfd.Sysfd` as `fd`, `name`, and the kernel's file offset `off` (the
module docstring says why the other fields are not needed). An open file's `off` starts at 0, as
`open(2)` sets `f_pos` (`O_APPEND` is refused). -/
@[reducible] def file.underlying : go.GoType :=
  go.GoType.StructType [go.field_decl.FieldDecl go!"fd" go.int,
    go.field_decl.FieldDecl go!"name" go.string, go.field_decl.FieldDecl go!"off" go.int64]

/-- `fileStat` (`types_unix.go`): only `size`. A `fileStat` is made only by `Stat.impl`, and its
methods but `Size` (`Name`, `Mode`, `ModTime`, `IsDir`, `Sys`) are not translated (stuck). -/
@[reducible] def fileStat.underlying : go.GoType :=
  go.GoType.StructType [go.field_decl.FieldDecl go!"size" go.int64]

/-- The struct-field facts goose emits for every translated struct (as `File.TypeAssumptions`'s
`get_file`/`set_file` in `Code.os`), stated by hand for `file`: goose cannot see the trusted
layout `file.underlying`, so it emits none. Getting a field of a `file` value gives the field;
setting it gives the value with that field replaced. Specs that need them take them as instance
hypotheses, as they take a package's generated `Assumptions`. Part of the trust base. -/
class file.FieldAssumptions [GoLocalContext] [GoSemanticsFunctions] : Prop where
  get_fd : ∀ (x : file), go.IsGoStepPureDetTagged Tag.under
    (StructFieldGet file.underlying go!"fd") #x (Val #(x.fd'))
  set_fd : ∀ (x : file) (y : w64), go.IsGoStepPureDetTagged Tag.under
    (StructFieldSet file.underlying go!"fd") (PairV #x #y) (Val #(({ x with fd' := y } : file)))
  get_name : ∀ (x : file), go.IsGoStepPureDetTagged Tag.under
    (StructFieldGet file.underlying go!"name") #x (Val #(x.name'))
  set_name : ∀ (x : file) (y : GoString), go.IsGoStepPureDetTagged Tag.under
    (StructFieldSet file.underlying go!"name") (PairV #x #y)
    (Val #(({ x with name' := y } : file)))
  get_off : ∀ (x : file), go.IsGoStepPureDetTagged Tag.under
    (StructFieldGet file.underlying go!"off") #x (Val #(x.off'))
  set_off : ∀ (x : file) (y : w64), go.IsGoStepPureDetTagged Tag.under
    (StructFieldSet file.underlying go!"off") (PairV #x #y) (Val #(({ x with off' := y } : file)))

/-- The struct-field facts goose emits for every translated struct, stated by hand for
`fileStat`, whose layout `fileStat.underlying` is trusted (as `file.FieldAssumptions`). Part of
the trust base. -/
class fileStat.FieldAssumptions [GoLocalContext] [GoSemanticsFunctions] : Prop where
  get_size : ∀ (x : fileStat), go.IsGoStepPureDetTagged Tag.under
    (StructFieldGet fileStat.underlying go!"size") #x (Val #(x.size'))
  set_size : ∀ (x : fileStat) (y : w64), go.IsGoStepPureDetTagged Tag.under
    (StructFieldSet fileStat.underlying go!"size") (PairV #x #y)
    (Val #(({ x with size' := y } : fileStat)))

attribute [instance] file.FieldAssumptions.get_fd file.FieldAssumptions.set_fd
  file.FieldAssumptions.get_name file.FieldAssumptions.set_name
  file.FieldAssumptions.get_off file.FieldAssumptions.set_off
  fileStat.FieldAssumptions.get_size fileStat.FieldAssumptions.set_size

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
or on a flag it does not support, among them `O_APPEND`, `O_EXCL`, `O_SYNC` and `O_NONBLOCK`) for a
path of the domain of its files, `NsOpen` for a path of the namespace (of a file or a directory,
`notes/walfs-ext-plan.md`): the model asks which (`Regime`, a query of the model's state, not a
system call; a path's regime never changes). An open of the namespace with `O_CREAT` may create, so
it starts with `NsBegin` (the extension's start of a call that changes the namespace).
`newFile` makes the `File{&file{...}}` with the fd and the name; its other work (an `fstat` to
decide that a regular file is not pollable, the finalizer) is invisible to Go code. `perm` matters
only to the mode of a created file, which the extension does not model. A name with a NUL byte,
where Go returns `EINVAL` without a system call, is not a path of the domain (the environment
assumptions of `GooseLang/Ext/OsFs/Impl.lean`). -/
noncomputable def OpenFile.impl : val :=
  λ: "name" "flag" "perm",
    (rec: "open" <> :=
      let: "r" := if: ExternalOp osFsExt.name "Regime" "name" =⟨go.uintptr⟩ #(W64 0) then
          ExternalOp osFsExt.name "Open" ("name", "flag" |⟨go.int⟩ #(W64 0x80000))
        else
          (if: ("flag" &⟨go.int⟩ #(W64 0x40)) ≠⟨go.int⟩ #(W64 0) then
            ExternalOp osFsExt.name "NsBegin" #() else #()) ;;
          ExternalOp osFsExt.name "NsOpen" ("name", "flag" |⟨go.int⟩ #(W64 0x80000)) in
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
fd whatever the errno it returns; `DirClose` for a directory's fd (the model asks which, `FdKind`, a
query of the model's state, not a system call). -/
noncomputable def File.Close.impl : val :=
  λ: "f" <>,
    let: "inner" := model.inner "f" in
    let: "fd" := ![go.int] (StructFieldRef model.file go!"fd" "inner") in
    let: "kind" := ExternalOp osFsExt.name "FdKind" "fd" in
    StructFieldRef model.file go!"fd" "inner" <-[go.int] #(-1 : w64) ;;
    let: "e" := if: "kind" =⟨go.uintptr⟩ #(W64 0) then ExternalOp osFsExt.name "Close" "fd"
      else ExternalOp osFsExt.name "DirClose" "fd" in
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

/-- The bound below which the model keeps file offsets (`2^62`): past it Linux's `lseek` fails
(`EINVAL` past the filesystem's maximum file size, which the extension does not model) and an
`int64` sum may wrap, so the model does not go there: a panic, never reached by a proved
program. -/
abbrev model.offMax : w64 := W64 0x4000000000000000

/-- `(*File).Seek(offset int64, whence int) (int64, error)` (`file.go`, `file_unix.go`'s
`seek`, `poll.FD.Seek`): one `lseek(2)`, whose result Go returns, an error being
`&PathError{"seek", name, Errno(e)}`. Linux's `lseek` on a regular file computes the new offset
from the start (`SEEK_SET`, 0), the offset (`SEEK_CUR`, 1) or the size (`SEEK_END`, 2), and fails
with `EINVAL` on another `whence` or a negative result, changing nothing. The model keeps the
offset in the `file`'s `off` (the module docstring) and reads the size by the extension's `Fstat`
(an `lseek` is not a call to `fstat`, and cannot fail with its errnos: the model has more outcomes
than Linux, which only weakens what a proof shows). A `SEEK_CUR` after a failed `Write` (whose
effect on the offset the model does not know, `off` being -1) and a result at or past
`model.offMax` are not modelled (a panic). The check of Go's `Seek` that a directory's fd (one
`Readdirnames` used) returns `EISDIR` does not arise: the extension's `Fstat` is stuck on a
directory's fd, and `Seek` of one is not modelled. -/
noncomputable def File.Seek.impl : val :=
  λ: "f" "offset" "whence",
    let: "inner" := model.inner "f" in
    let: "fd" := ![go.int] (StructFieldRef model.file go!"fd" "inner") in
    let: "cur" := ![go.int64] (StructFieldRef model.file go!"off" "inner") in
    let: "base" :=
      if: "whence" =⟨go.int⟩ #(W64 0) then (#(W64 0), #(W64 0))
      else if: "whence" =⟨go.int⟩ #(W64 1) then
        (if: "cur" <⟨go.int64⟩ #(W64 0) then Panic "os: Seek from an unknown offset not modelled"
         else ("cur", #(W64 0)))
      else if: "whence" =⟨go.int⟩ #(W64 2) then ExternalOp osFsExt.name "Fstat" "fd"
      else (#(W64 0), #(W64 22)) in -- EINVAL
    if: Snd "base" ≠⟨go.uintptr⟩ #(W64 0) then
      (#(W64 0), model.wrapErrno #"seek" "inner" (Snd "base"))
    else
      let: "n" := Fst "base" +⟨go.int64⟩ "offset" in
      if: "n" <⟨go.int64⟩ #(W64 0) then (#(W64 0), model.wrapErrno #"seek" "inner" #(W64 22))
      else if: (#model.offMax ≤⟨go.int64⟩ "n") || (#model.offMax ≤⟨go.int64⟩ Fst "base") ||
          (#model.offMax ≤⟨go.int64⟩ "offset") then
        Panic "os: Seek past 2^62 not modelled"
      else
        StructFieldRef model.file go!"off" "inner" <-[go.int64] "n" ;;
        ("n", #GoInterface.nil)

/-- `(*File).Write(b []byte) (n int, err error)` (`file.go`, `file_posix.go`'s `write`,
`poll.FD.Write`): `write(2)` calls at the file offset until all of `b` is written, `EINTR`
retried, an error being `&PathError{"write", name, Errno(e)}`; the offset advances by what was
written. A `write(2)` is a `pwrite(2)` at the offset that then moves it: the model calls `WriteAt`
(`File.WriteAt.impl`, the same loop of the extension's `PWriteStart`/`PWriteFinish` as Go's
`Pwrite`, whose result Go's `Write` gives too: `len(b)` and nil, or an error) at `off`, then `off`
moves past `b`. On an error the model's `WriteAt` does not say how much was written, so the offset
is unknown (`off` set to -1): a later `Write`, `Read` or `SEEK_CUR` is not modelled (a panic; a
`SEEK_SET` sets a known offset again). A write reaching `model.offMax` is not modelled. -/
noncomputable def File.Write.impl : val :=
  λ: "f" "b",
    let: "inner" := model.inner "f" in
    let: "off" := ![go.int64] (StructFieldRef model.file go!"off" "inner") in
    let: "len" := (FuncResolve go.len [go.GoType.SliceType go.byte]) #() "b" in
    if: "off" <⟨go.int64⟩ #(W64 0) then Panic "os: Write at an unknown offset not modelled"
    else if: #model.offMax ≤⟨go.int64⟩ ("off" +⟨go.int64⟩ Convert go.int go.int64 "len") then
      Panic "os: Write past 2^62 not modelled"
    else
      let: "r" := (MethodResolve (go.PointerType model.File) go!"WriteAt") "f" "b" "off" in
      (if: Snd "r" =⟨go.error⟩ #GoInterface.nil then
        StructFieldRef model.file go!"off" "inner" <-[go.int64]
          ("off" +⟨go.int64⟩ Convert go.int go.int64 "len")
      else StructFieldRef model.file go!"off" "inner" <-[go.int64] #(W64 (-1))) ;;
      "r"

/-- `(*File).Read(b []byte) (n int, err error)` (`file.go`, `file_posix.go`'s `read`,
`poll.FD.Read`): for a non-empty `b`, one `read(2)` at the file offset of at most `maxRW` (1 GiB)
bytes, `EINTR` retried; the offset advances by what was read; 0 bytes is `io.EOF`; an error is
`&PathError{"read", name, Errno(e)}` with `n = 0`, the offset unchanged. A `read(2)` is a
`pread(2)` at the offset that then moves it: the extension's `PRead` at `off` (as
`File.ReadAt.impl`'s), whose bytes are copied into `b`. An empty `b` returns `0, nil` at once
(`poll.FD.Read`). A read from an unknown offset (after a failed `Write`) or reaching
`model.offMax` is not modelled (a panic). -/
noncomputable def File.Read.impl : val :=
  λ: "f" "b",
    let: "inner" := model.inner "f" in
    let: "fd" := ![go.int] (StructFieldRef model.file go!"fd" "inner") in
    let: "off" := ![go.int64] (StructFieldRef model.file go!"off" "inner") in
    let: "len" := (FuncResolve go.len [go.GoType.SliceType go.byte]) #() "b" in
    if: "len" =⟨go.int⟩ #(W64 0) then (#(W64 0), #GoInterface.nil)
    else if: "off" <⟨go.int64⟩ #(W64 0) then Panic "os: Read at an unknown offset not modelled"
    else if: #model.offMax ≤⟨go.int64⟩ ("off" +⟨go.int64⟩ Convert go.int go.int64 "len") then
      Panic "os: Read past 2^62 not modelled"
    else
      (rec: "read" <> :=
        let: "r" := ExternalOp osFsExt.name "PRead" ("fd", ("off",
          if: "len" >⟨go.int⟩ #(W64 0x40000000) then #(W64 0x40000000) else "len")) in
        if: Snd "r" =⟨go.uintptr⟩ #(W64 4) then "read" #() -- EINTR
        else if: Snd "r" ≠⟨go.uintptr⟩ #(W64 0) then
          (#(W64 0), model.wrapErrno #"read" "inner" (Snd "r"))
        else
          let: "m" := (FuncResolve go.copy [go.GoType.SliceType go.byte]) #() "b"
            (Convert go.string (go.GoType.SliceType go.byte) (Fst "r")) in
          StructFieldRef model.file go!"off" "inner" <-[go.int64]
            ("off" +⟨go.int64⟩ Convert go.int go.int64 "m") ;;
          if: "m" =⟨go.int⟩ #(W64 0) then (#(W64 0), ![go.error] (GlobalVarAddr io.EOF #()))
          else ("m", #GoInterface.nil)) #()

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
`&PathError{"sync", name, Errno(e)}`: the extension's `Fsync` (`fd ↦ errno`), or `DirSync` for a
directory's fd (`FdKind`, as in `Close`). -/
noncomputable def File.Sync.impl : val :=
  λ: "f" <>,
    let: "inner" := model.inner "f" in
    let: "fd" := ![go.int] (StructFieldRef model.file go!"fd" "inner") in
    let: "kind" := ExternalOp osFsExt.name "FdKind" "fd" in
    (rec: "fsync" <> :=
      let: "e" := if: "kind" =⟨go.uintptr⟩ #(W64 0) then ExternalOp osFsExt.name "Fsync" "fd"
        else ExternalOp osFsExt.name "DirSync" "fd" in
      if: "e" =⟨go.uintptr⟩ #(W64 4) then "fsync" #() -- EINTR
      else if: "e" ≠⟨go.uintptr⟩ #(W64 0) then model.wrapErrno #"sync" "inner" "e"
      else #GoInterface.nil) #()


/-! The namespace (`notes/walfs-ext-plan.md`). -/

/-- `LinkError` (`file.go`), as goose names it. -/
@[reducible] def model.LinkError : go.GoType := go.GoType.Named go!"os.LinkError" []

/-- `&LinkError{op, old, new, err}` as an `error`. -/
noncomputable def model.linkError : val :=
  λ: "op" "old" "new" "err",
    let: "le" := GoAlloc model.LinkError (GoZeroVal model.LinkError #()) in
    StructFieldRef model.LinkError go!"Op" "le" <-[go.string] "op" ;;
    StructFieldRef model.LinkError go!"Old" "le" <-[go.string] "old" ;;
    StructFieldRef model.LinkError go!"New" "le" <-[go.string] "new" ;;
    StructFieldRef model.LinkError go!"Err" "le" <-[go.error] "err" ;;
    Convert (go.PointerType model.LinkError) go.error "le"

/-- `Rename(oldpath, newpath string) error` (`file.go`, `file_unix.go`'s `rename`):

```go
	fi, err := Lstat(newname)
	if err == nil && fi.IsDir() {
		if ofi, err := Lstat(oldname); err != nil {
			if pe, ok := err.(*PathError); ok {
				err = pe.Err
			}
			return &LinkError{"rename", oldname, newname, err}
		} else if newname == oldname || !SameFile(fi, ofi) {
			return &LinkError{"rename", oldname, newname, syscall.EEXIST}
		}
	}
	err = ignoringEINTR(func() error {
		return syscall.Rename(oldname, newname)
	})
	if err != nil {
		return &LinkError{"rename", oldname, newname, err}
	}
	return nil
```

The `lstat` of `newname` is the extension's `NsLstatDir` (`newname ↦ (isDir, e)`): `isDir` is 1
only for a directory, with a nonzero `e`; for a directory Go returns a `LinkError` whose error is
`EEXIST`, or the error of the `lstat` of `oldname` (two distinct names of the namespace are never
the same file: no hard links, and the filesystem is case-sensitive), so the model returns one with
`Errno(e)`. `isDir` is 0 for anything else, and for a directory whose `lstat` failed, as in Go.
Then `rename(2)` is the extension's `Rename`, after `NsBegin`, `EINTR` retried. -/
noncomputable def Rename.impl : val :=
  λ: "oldname" "newname",
    let: "l" := ExternalOp osFsExt.name "NsLstatDir" "newname" in
    if: Fst "l" =⟨go.uintptr⟩ #(W64 1) then
      model.linkError #"rename" "oldname" "newname" (syscall.model.errno (Snd "l"))
    else
      (rec: "rename" <> :=
        ExternalOp osFsExt.name "NsBegin" #() ;;
        let: "e" := ExternalOp osFsExt.name "Rename" ("oldname", "newname") in
        if: "e" =⟨go.uintptr⟩ #(W64 4) then "rename" #() -- EINTR
        else if: "e" ≠⟨go.uintptr⟩ #(W64 0) then
          model.linkError #"rename" "oldname" "newname" (syscall.model.errno "e")
        else #GoInterface.nil) #()

/-- `Remove(name string) error` (`file_unix.go`):

```go
	e := ignoringEINTR(func() error {
		return syscall.Unlink(name)
	})
	if e == nil {
		return nil
	}
	e1 := ignoringEINTR(func() error {
		return syscall.Rmdir(name)
	})
	if e1 == nil {
		return nil
	}
	if e1 != syscall.ENOTDIR {
		e = e1
	}
	return &PathError{Op: "remove", Path: name, Err: e}
```

`unlink(2)` and `rmdir(2)` are the extension's `Unlink` and `Rmdir`, each after `NsBegin`. -/
noncomputable def Remove.impl : val :=
  λ: "name",
    let: "e" := (rec: "unlink" <> :=
      ExternalOp osFsExt.name "NsBegin" #() ;;
      let: "e" := ExternalOp osFsExt.name "Unlink" "name" in
      if: "e" =⟨go.uintptr⟩ #(W64 4) then "unlink" #() else "e") #() in
    if: "e" =⟨go.uintptr⟩ #(W64 0) then #GoInterface.nil
    else
      let: "e1" := (rec: "rmdir" <> :=
        ExternalOp osFsExt.name "NsBegin" #() ;;
        let: "e1" := ExternalOp osFsExt.name "Rmdir" "name" in
        if: "e1" =⟨go.uintptr⟩ #(W64 4) then "rmdir" #() else "e1") #() in
      if: "e1" =⟨go.uintptr⟩ #(W64 0) then #GoInterface.nil
      else model.pathError #"remove" "name"
        (syscall.model.errno (if: "e1" ≠⟨go.uintptr⟩ #(W64 20) then "e1" else "e")) -- ENOTDIR

/-- `Mkdir(name string, perm FileMode) error` (`file.go`): `mkdir(2)` (`EINTR` retried), an error
being `&PathError{"mkdir", name, Errno(e)}` (the extension's `Mkdir`, after `NsBegin`); on Linux
nothing follows it
(`supportsCreateWithStickyBit`). `fixLongPath` is the identity off Windows; `perm` matters only to
the mode, which the extension does not model. -/
noncomputable def Mkdir.impl : val :=
  λ: "name" "perm",
    (rec: "mkdir" <> :=
      ExternalOp osFsExt.name "NsBegin" #() ;;
      let: "e" := ExternalOp osFsExt.name "Mkdir" "name" in
      if: "e" =⟨go.uintptr⟩ #(W64 4) then "mkdir" #() -- EINTR
      else if: "e" ≠⟨go.uintptr⟩ #(W64 0) then
        model.pathError #"mkdir" "name" (syscall.model.errno "e")
      else #GoInterface.nil) #()

/-- `(*File).Readdirnames(n int) (names []string, err error)` (`dir.go`, `dir_unix.go`'s
`readdir`) for `n ≤ 0`, the WAL's: every name of the directory but `.` and `..`, read by
`getdents(2)` calls until one returns nothing (`EINTR` retried); an error returns the names so
far and `&PathError{"readdirent", name, Errno(e)}`; the result is never a nil slice. The
extension's `DirReadNext` gives a name at a time (`fd ↦ (name, done, errno)`), with POSIX's
`readdir` across concurrent changes; it is stuck on a fd that is not a directory's (Go:
`ENOTDIR`) and on a second read of one fd (Go returns no names; the WAL never reads a directory fd
twice). `n > 0` is not modelled: a panic, never reached by a proved program. -/
noncomputable def File.Readdirnames.impl : val :=
  λ: "f" "n",
    let: "inner" := model.inner "f" in
    let: "fd" := ![go.int] (StructFieldRef model.file go!"fd" "inner") in
    if: "n" >⟨go.int⟩ #(W64 0) then Panic "os: Readdirnames with n > 0 not modelled"
    else
      (rec: "loop" "names" :=
        let: "r" := ExternalOp osFsExt.name "DirReadNext" "fd" in
        let: "e" := Snd (Snd "r") in
        if: "e" =⟨go.uintptr⟩ #(W64 4) then "loop" "names" -- EINTR
        else if: "e" ≠⟨go.uintptr⟩ #(W64 0) then
          ("names", model.wrapErrno #"readdirent" "inner" "e")
        else if: Fst (Snd "r") =⟨go.uintptr⟩ #(W64 1) then ("names", #GoInterface.nil)
        else
          let: "nm" := Fst "r" in
          "loop" ((FuncResolve go.append [go.GoType.SliceType go.string]) #() "names"
            (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.string))))
              (LiteralValue [KeyedElement none (ElementExpression go.string (Var "nm"))]))))
        (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.string))))
          (LiteralValue []))

end code
end os

end Perennial
