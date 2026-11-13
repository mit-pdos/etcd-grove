/-
Trusted Go model of `os` (namespace of the generated package; project bboltfs of `etc/goose.py`,
`Code/os.toml`), in terms of the Linux file extension of `GooseLang.Ext.Fs.Impl` (`Fs.fsExt`,
`ExternalOp Fs.fsExt.name "PRead"`, ...), for any program whose extensions include it.
linux/amd64, Go 1.27.3 (`etc/goose.py`'s `GO_TOOLCHAIN`). Perennial's own translation of `os`
(`Perennial.Code.os`, with its own models of the initializer's untranslated pieces) must not be in
the same import closure.

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
not modelled: a nil `*File` (but in `Close`, which returns Go's `ErrInvalid`) or a zero `File` (Go
returns `ErrInvalid` or `EINVAL`), and a closed
file (`Close` sets `fd` to -1, as Go's `pfd.destroy` sets `Sysfd`; Go then returns `ErrClosed`,
while the extension is stuck on fd -1, and the methods that answer without it, `Seek`, `Write`,
`Read` and `Truncate`, panic first: not modelled), including a method racing `Close` (Go's reference count
makes that safe; in the model it is a race on the inner cell, or an operation on a closed fd).
Unrelated to the extension: an open file's finalizer (`notes/osfs-ext-plan.md`, D5).
-/
module

public import Perennial.Golang.Defn
public import Perennial.Code.errors
public import Perennial.Code.io
public import LinuxFs.Code.io.fs
public import LinuxFs.Code.syscall
public import GooseLang.Ext.Fs.Impl

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

/-- The model's `fileStat` (`fileStat.underlying`): the size and the mode. -/
structure fileStat where
  mk ::
  size' : w64
  mode' : w32

instance fileStat.zero_val : ZeroVal fileStat := ⟨fileStat.mk zeroValDef zeroValDef⟩

section code
variable [GooseExts] [GoGlobalContext]

/-- `file` (`file_unix.go`): `pfd.Sysfd` as `fd`, `name`, and the kernel's file offset `off` (the
module docstring says why the other fields are not needed). An open file's `off` starts at 0, as
`open(2)` sets `f_pos` (`O_APPEND` is refused). -/
@[reducible] def file.underlying : go.GoType :=
  go.GoType.StructType [go.field_decl.FieldDecl go!"fd" go.int,
    go.field_decl.FieldDecl go!"name" go.string, go.field_decl.FieldDecl go!"off" go.int64]

/-- `fileStat` (`types_unix.go`): only `size` and `mode` (an `io/fs.FileMode`). A `fileStat` is
made only by `File.Stat.impl` and `model.stat` (`Stat`, `Lstat`); its methods `Size`, `Mode` and
`IsDir` are translated (`return fs.size`, `return fs.mode`, `return fs.Mode().IsDir()`), the
others (`Name`, `ModTime`, `Sys`) are not (stuck). -/
@[reducible] noncomputable def fileStat.underlying : go.GoType :=
  go.GoType.StructType [go.field_decl.FieldDecl go!"size" go.int64,
    go.field_decl.FieldDecl go!"mode" io.fs.FileMode.ty]

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
  get_mode : ∀ (x : fileStat), go.IsGoStepPureDetTagged Tag.under
    (StructFieldGet fileStat.underlying go!"mode") #x (Val #(x.mode'))
  set_mode : ∀ (x : fileStat) (y : w32), go.IsGoStepPureDetTagged Tag.under
    (StructFieldSet fileStat.underlying go!"mode") (PairV #x #y)
    (Val #(({ x with mode' := y } : fileStat)))

attribute [instance] file.FieldAssumptions.get_fd file.FieldAssumptions.set_fd
  file.FieldAssumptions.get_name file.FieldAssumptions.set_name
  file.FieldAssumptions.get_off file.FieldAssumptions.set_off
  fileStat.FieldAssumptions.get_size fileStat.FieldAssumptions.set_size
  fileStat.FieldAssumptions.get_mode fileStat.FieldAssumptions.set_mode

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

/-- `FileMode` as goose names it. -/
@[reducible] noncomputable def model.FileMode : go.GoType := io.fs.FileMode.ty

/-- The bits of a `FileMode` that `fillFileStatFromSys` (`stat_linux.go`) sets from `st_mode`
other than the type: the permissions (`0777`), `ModeSetuid` (`1 << 23`), `ModeSetgid` (`1 << 22`)
and `ModeSticky` (`1 << 20`). -/
abbrev model.modeOtherBits : w32 := W32 0xD001FF

/-- A mode `fillFileStatFromSys` can make for a file of type `ty` (0 for a regular file,
`ModeDir`, `1 << 31`, for a directory: the only types in the roots' trees, the extension's
environment): the type, and arbitrary other bits (the extension does not model permissions, so
any of them may be set). -/
noncomputable def model.arbitraryMode : val :=
  λ: "ty", "ty" |⟨model.FileMode⟩
    (Convert go.uint64 model.FileMode ArbitraryInt &⟨model.FileMode⟩ #model.modeOtherBits)

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
amd64: the extension's `Open` (`(tok, name, flags) ↦ (fd, errno)`, of a file or a directory,
stuck on a path outside the roots' trees or on a flag it does not support, among them `O_APPEND`,
`O_EXCL`, `O_SYNC` and `O_NONBLOCK`), each attempt after its own `CallBegin` (the extension's start
of a call on a path, whose token the step takes).
`newFile` makes the `File{&file{...}}` with the fd and the name; its other work (an `fstat` to
decide that a regular file is not pollable, the finalizer) is invisible to Go code. `perm` matters
only to the mode of a created file, which the extension does not model. A name with a NUL byte,
where Go returns `EINVAL` without a system call, is not a path of the roots' trees (the
extension is stuck on it). -/
noncomputable def OpenFile.impl : val :=
  λ: "name" "flag" "perm",
    (rec: "open" <> :=
      let: "c" := ExternalOp Fs.fsExt.name "CallBegin" #() in
      let: "r" := ExternalOp Fs.fsExt.name "Open" ("c", ("name", "flag" |⟨go.int⟩ #(W64 0x80000))) in
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
query of the model's state, not a system call). A nil `*File` returns `ErrInvalid` without a system
call (`file_posix.go`: `if f == nil { return ErrInvalid }`; 2026-11-13, the WAL's `Open` error path
closes a WAL whose `dirFile` is nil: `notes/wal-fsext-plan.md`, item 6; Go example
`examples/osfs/semantics/model_os_close_nil.go`). -/
noncomputable def File.Close.impl : val :=
  λ: "f" <>,
    if: "f" =⟨go.PointerType model.File⟩ #null then
      ![go.error] (GlobalVarAddr go!"os.ErrInvalid" #())
    else
    let: "inner" := model.inner "f" in
    let: "fd" := ![go.int] (StructFieldRef model.file go!"fd" "inner") in
    let: "kind" := ExternalOp Fs.fsExt.name "FdKind" "fd" in
    StructFieldRef model.file go!"fd" "inner" <-[go.int] #(-1 : w64) ;;
    let: "e" := if: "kind" =⟨go.uintptr⟩ #(W64 0) then ExternalOp Fs.fsExt.name "Close" "fd"
      else ExternalOp Fs.fsExt.name "DirClose" "fd" in
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
          let: "r" := ExternalOp Fs.fsExt.name "PRead" ("fd", ("off",
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
as `string(p[nn:max])`, as goose models `string(b)` (never empty: the loop runs only while
`nn < len`, and `PWriteStart` is stuck on empty data). `PWriteFinish` writes all of the data with
errno 0, a non-empty prefix with errno 0 (a short write), or a prefix with a nonzero errno, which
the loop treats as Go treats the system call's
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
          let: "t" := ExternalOp Fs.fsExt.name "PWriteStart" ("fd",
            ("off" +⟨go.int64⟩ Convert go.int go.int64 "nn",
             Convert (go.GoType.SliceType go.byte) go.string
               (Slice (go.GoType.SliceType go.byte) ("b", "nn", "max")))) in
          let: "r" := ExternalOp Fs.fsExt.name "PWriteFinish" "t" in
          if: Snd "r" =⟨go.uintptr⟩ #(W64 4) then "pwrite" "nn" -- EINTR
          else
            let: "nn" := "nn" +⟨go.int⟩ Fst "r" in
            if: ("nn" =⟨go.int⟩ "len") && (Snd "r" =⟨go.uintptr⟩ #(W64 0)) then
              ("len", #GoInterface.nil)
            else if: Snd "r" ≠⟨go.uintptr⟩ #(W64 0) then
              (#(W64 0), model.wrapErrno #"write" "inner" (Snd "r"))
            else "pwrite" "nn") #(W64 0)

/-- The bound below which the model keeps file offsets (`2^62`), so that an `int64` sum of two of
them cannot wrap: past it the model does not go (a panic, never reached by a proved program). A
read or write there is a superset of Linux's answers anyway (any errno, `EFBIG`); `Seek` has the
filesystem's own bound, `model.seekMax`. -/
abbrev model.offMax : w64 := W64 0x4000000000000000

/-- The largest offset `lseek` accepts on the target configuration's ext4 (extent files, 4 KiB
blocks): `s_maxbytes = (2^32 - 1) · 4096 = 2^44 - 4096` (`ext4_max_size`; `generic_file_llseek_size`
→ `vfs_setpos` returns `EINVAL` past it). Measured on configuration C
(`notes/axiom-review/fs-v2-r8/`, `TestSeekPastMaxBytes`): `Seek(0xffffffff000)` succeeds,
`Seek(0xffffffff001)` is `EINVAL`. -/
abbrev model.seekMax : w64 := W64 0xffffffff000

/-- `(*File).Seek(offset int64, whence int) (int64, error)` (`file.go`, `file_unix.go`'s
`seek`, `poll.FD.Seek`): one `lseek(2)`, whose result Go returns, an error being
`&PathError{"seek", name, Errno(e)}`. Linux's `lseek` on a regular file computes the new offset
from the start (`SEEK_SET`, 0), the offset (`SEEK_CUR`, 1) or the size (`SEEK_END`, 2), and fails
with `EINVAL` on another `whence` or a negative result, changing nothing. The model keeps the
offset in the `file`'s `off` (the module docstring) and reads the size by the extension's `Fstat`
(an `lseek` is not a call to `fstat`, and cannot fail with its errnos: the model has more outcomes
than Linux, which only weakens what a proof shows). A `SEEK_CUR` after a failed `Write` (whose
effect on the offset the model does not know, `off` being -1) and a result at or past
`model.offMax` are not modelled (a panic); a result past `model.seekMax` is `EINVAL`, as ext4 on
the target configuration answers. A closed file (fd -1) is not modelled (a panic; Go returns
`ErrClosed` before the system call). The check of Go's `Seek` that a directory's fd (one
`Readdirnames` used) returns `EISDIR` does not arise: the extension's `Fstat` is stuck on a
directory's fd, and `Seek` of one is not modelled. -/
noncomputable def File.Seek.impl : val :=
  λ: "f" "offset" "whence",
    let: "inner" := model.inner "f" in
    let: "fd" := ![go.int] (StructFieldRef model.file go!"fd" "inner") in
    if: "fd" <⟨go.int⟩ #(W64 0) then Panic "os: Seek of a closed file not modelled" else
    let: "cur" := ![go.int64] (StructFieldRef model.file go!"off" "inner") in
    let: "base" :=
      if: "whence" =⟨go.int⟩ #(W64 0) then (#(W64 0), #(W64 0))
      else if: "whence" =⟨go.int⟩ #(W64 1) then
        (if: "cur" <⟨go.int64⟩ #(W64 0) then Panic "os: Seek from an unknown offset not modelled"
         else ("cur", #(W64 0)))
      else if: "whence" =⟨go.int⟩ #(W64 2) then ExternalOp Fs.fsExt.name "Fstat" "fd"
      else (#(W64 0), #(W64 22)) in -- EINVAL
    if: Snd "base" ≠⟨go.uintptr⟩ #(W64 0) then
      (#(W64 0), model.wrapErrno #"seek" "inner" (Snd "base"))
    else
      let: "n" := Fst "base" +⟨go.int64⟩ "offset" in
      if: "n" <⟨go.int64⟩ #(W64 0) then (#(W64 0), model.wrapErrno #"seek" "inner" #(W64 22))
      else if: (#model.offMax ≤⟨go.int64⟩ "n") || (#model.offMax ≤⟨go.int64⟩ Fst "base") ||
          (#model.offMax ≤⟨go.int64⟩ "offset") then
        Panic "os: Seek past 2^62 not modelled"
      else if: #model.seekMax <⟨go.int64⟩ "n" then
        (#(W64 0), model.wrapErrno #"seek" "inner" #(W64 22)) -- EINVAL past ext4's maximum
      else
        StructFieldRef model.file go!"off" "inner" <-[go.int64] "n" ;;
        ("n", #GoInterface.nil)

/-- `(*File).Write(b []byte) (n int, err error)` (`file.go`, `file_posix.go`'s `write`,
`poll.FD.Write`): `write(2)` calls at the file offset until all of `b` is written, `EINTR`
retried, an error being `&PathError{"write", name, Errno(e)}`; the offset advances by what was
written. A `write(2)` is a `pwrite(2)` at the offset that then moves it: the model calls `WriteAt`
(`File.WriteAt.impl`, the same loop of the extension's `PWriteStart`/`PWriteFinish` as Go's
`Pwrite`) at `off`, then `off` moves past `b`. On success Go returns `len(b)` and nil. On an error
Go returns the bytes written before it (`poll.FD.Write`'s `nn`, which a short `write(2)` followed
by a failing one makes positive), which the model's `WriteAt` does not keep: the model returns any
count (`ArbitraryInt`), and the offset is unknown (`off` set to -1): a later `Write`, `Read` or
`SEEK_CUR` is not modelled (a panic; a `SEEK_SET` sets a known offset again). A write reaching
`model.offMax` is not modelled. Not modelled either (a panic): a closed file (fd -1: Go returns
`ErrClosed`). An empty `b`, for which Go (with no empty-buffer shortcut in `poll.FD.Write`)
issues a zero-byte `write(2)` whose answer depends on the fd's mode (`EBADF` on a read-only fd,
measured on C, `notes/axiom-review/fs-v2-r8/`), returns `(0, nil)` or `(0, &PathError{"write",
name, Errno(e)})` for any errno, with no extension step and the offset unchanged: a zero-byte
`write(2)` on a regular file changes nothing (POSIX: "if count is zero and fd refers to a regular
file, write() may detect the errors ... and otherwise returns 0 without any other effect"; measured,
`TestEmptyWrite`), and the model does not know the fd's mode, so it allows both answers
(2026-11-13: `os.WriteFile(f, []byte(""), ...)`, fileutil's `IsDirWriteable`; until then a panic;
Go example `examples/osfs/semantics/model_os_writefile.go`). -/
noncomputable def File.Write.impl : val :=
  λ: "f" "b",
    let: "inner" := model.inner "f" in
    let: "fd" := ![go.int] (StructFieldRef model.file go!"fd" "inner") in
    let: "off" := ![go.int64] (StructFieldRef model.file go!"off" "inner") in
    let: "len" := (FuncResolve go.len [go.GoType.SliceType go.byte]) #() "b" in
    if: "fd" <⟨go.int⟩ #(W64 0) then Panic "os: Write of a closed file not modelled"
    else if: "len" =⟨go.int⟩ #(W64 0) then
      (let: "e" := ArbitraryInt in
       if: "e" =⟨go.uintptr⟩ #(W64 0) then (#(W64 0), #GoInterface.nil)
       else (#(W64 0), model.wrapErrno #"write" "inner" "e"))
    else if: "off" <⟨go.int64⟩ #(W64 0) then Panic "os: Write at an unknown offset not modelled"
    else if: #model.offMax ≤⟨go.int64⟩ ("off" +⟨go.int64⟩ Convert go.int go.int64 "len") then
      Panic "os: Write past 2^62 not modelled"
    else
      let: "r" := (MethodResolve (go.PointerType model.File) go!"WriteAt") "f" "b" "off" in
      if: Snd "r" =⟨go.error⟩ #GoInterface.nil then
        StructFieldRef model.file go!"off" "inner" <-[go.int64]
          ("off" +⟨go.int64⟩ Convert go.int go.int64 "len") ;;
        "r"
      else
        StructFieldRef model.file go!"off" "inner" <-[go.int64] #(W64 (-1)) ;;
        (ArbitraryInt, Snd "r")

/-- `(*File).Read(b []byte) (n int, err error)` (`file.go`, `file_posix.go`'s `read`,
`poll.FD.Read`): for a non-empty `b`, one `read(2)` at the file offset of at most `maxRW` (1 GiB)
bytes, `EINTR` retried; the offset advances by what was read; 0 bytes is `io.EOF`; an error is
`&PathError{"read", name, Errno(e)}` with `n = 0`, the offset unchanged. A `read(2)` is a
`pread(2)` at the offset that then moves it: the extension's `PRead` at `off` (as
`File.ReadAt.impl`'s), whose bytes are copied into `b`. An empty `b` returns `0, nil` at once
(`poll.FD.Read`, after its lock). A closed file (fd -1: Go returns `ErrClosed` from that lock), a
read from an unknown offset (after a failed `Write`), or one reaching `model.offMax` is not
modelled (a panic). -/
noncomputable def File.Read.impl : val :=
  λ: "f" "b",
    let: "inner" := model.inner "f" in
    let: "fd" := ![go.int] (StructFieldRef model.file go!"fd" "inner") in
    let: "off" := ![go.int64] (StructFieldRef model.file go!"off" "inner") in
    let: "len" := (FuncResolve go.len [go.GoType.SliceType go.byte]) #() "b" in
    if: "fd" <⟨go.int⟩ #(W64 0) then Panic "os: Read of a closed file not modelled"
    else if: "len" =⟨go.int⟩ #(W64 0) then (#(W64 0), #GoInterface.nil)
    else if: "off" <⟨go.int64⟩ #(W64 0) then Panic "os: Read at an unknown offset not modelled"
    else if: #model.offMax ≤⟨go.int64⟩ ("off" +⟨go.int64⟩ Convert go.int go.int64 "len") then
      Panic "os: Read past 2^62 not modelled"
    else
      (rec: "read" <> :=
        let: "r" := ExternalOp Fs.fsExt.name "PRead" ("fd", ("off",
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
extension's `Fstat` gives only the size (`fd ↦ (size, errno)`), stored in a fresh `fileStat`
with a regular file's mode of arbitrary permission bits (`model.arbitraryMode`: the extension's
`Fstat` is stuck on a directory's fd, so the fd is a regular file's); it is returned as a `FileInfo`
(`&fs`), whose `Size()` and `Mode()` read it. -/
noncomputable def File.Stat.impl : val :=
  λ: "f" <>,
    let: "inner" := model.inner "f" in
    let: "fd" := ![go.int] (StructFieldRef model.file go!"fd" "inner") in
    (rec: "fstat" <> :=
      let: "r" := ExternalOp Fs.fsExt.name "Fstat" "fd" in
      if: Snd "r" =⟨go.uintptr⟩ #(W64 4) then "fstat" #() -- EINTR
      else if: Snd "r" ≠⟨go.uintptr⟩ #(W64 0) then
        (GoZeroVal io.fs.FileInfo.ty #(), model.wrapErrno #"stat" "inner" (Snd "r"))
      else
        let: "fs" := GoAlloc model.fileStat (GoZeroVal model.fileStat #()) in
        StructFieldRef model.fileStat go!"size" "fs" <-[go.int64] Fst "r" ;;
        StructFieldRef model.fileStat go!"mode" "fs" <-[model.FileMode]
          model.arbitraryMode #(W32 0) ;;
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
        let: "e" := ExternalOp Fs.fsExt.name "FtruncateFinish"
          (ExternalOp Fs.fsExt.name "FtruncateStart" ("fd", "size")) in
        if: "e" =⟨go.uintptr⟩ #(W64 4) then "ftruncate" #() -- EINTR
        else if: "e" ≠⟨go.uintptr⟩ #(W64 0) then model.wrapErrno #"truncate" "inner" "e"
        else #GoInterface.nil) #()

/-- `(*File).Sync() error` (`file_posix.go`, `poll.FD.Fsync`): `fsync(2)`, `EINTR` retried, an
error being `&PathError{"sync", name, Errno(e)}`: the extension's `Fsync` (`fd ↦ errno`), or
`DirSync` for a directory's fd (`FdKind`, as in `Close`). A failed `Fsync` changes nothing (the
semantics assumes no failed writeback, `Impl.lean`'s header) and never returns `EINTR`, so the
retry is reachable only for `DirSync`. -/
noncomputable def File.Sync.impl : val :=
  λ: "f" <>,
    let: "inner" := model.inner "f" in
    let: "fd" := ![go.int] (StructFieldRef model.file go!"fd" "inner") in
    let: "kind" := ExternalOp Fs.fsExt.name "FdKind" "fd" in
    (rec: "fsync" <> :=
      let: "e" := if: "kind" =⟨go.uintptr⟩ #(W64 0) then ExternalOp Fs.fsExt.name "Fsync" "fd"
        else ExternalOp Fs.fsExt.name "DirSync" "fd" in
      if: "e" =⟨go.uintptr⟩ #(W64 4) then "fsync" #() -- EINTR
      else if: "e" ≠⟨go.uintptr⟩ #(W64 0) then model.wrapErrno #"sync" "inner" "e"
      else #GoInterface.nil) #()


/-! The directory tree (`notes/fs-semantics-v2.md`). -/

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

The `lstat` of `newname` is the extension's `LstatDir` (`(tok, newname) ↦ (isDir, e)`, after its
own `CallBegin`): `isDir` is 1
only for a directory, with a nonzero `e`; for a directory Go returns a `LinkError` whose error is
`EEXIST`, or the error of the `lstat` of `oldname` (two distinct names of the namespace are never
the same file: no hard links, and the filesystem is case-sensitive), so the model returns one with
`Errno(e)`. `isDir` is 0 for anything else, and for a directory whose `lstat` failed, as in Go.
Then `rename(2)` is the extension's `Rename`, each attempt after its own `CallBegin`, `EINTR`
retried. -/
noncomputable def Rename.impl : val :=
  λ: "oldname" "newname",
    let: "lc" := ExternalOp Fs.fsExt.name "CallBegin" #() in
    let: "l" := ExternalOp Fs.fsExt.name "LstatDir" ("lc", "newname") in
    if: Fst "l" =⟨go.uintptr⟩ #(W64 1) then
      model.linkError #"rename" "oldname" "newname" (syscall.model.errno (Snd "l"))
    else
      (rec: "rename" <> :=
        let: "c" := ExternalOp Fs.fsExt.name "CallBegin" #() in
        let: "e" := ExternalOp Fs.fsExt.name "Rename" ("c", ("oldname", "newname")) in
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

`unlink(2)` and `rmdir(2)` are the extension's `Unlink` and `Rmdir`, each attempt after its own
`CallBegin`. -/
noncomputable def Remove.impl : val :=
  λ: "name",
    let: "e" := (rec: "unlink" <> :=
      let: "c" := ExternalOp Fs.fsExt.name "CallBegin" #() in
      let: "e" := ExternalOp Fs.fsExt.name "Unlink" ("c", "name") in
      if: "e" =⟨go.uintptr⟩ #(W64 4) then "unlink" #() else "e") #() in
    if: "e" =⟨go.uintptr⟩ #(W64 0) then #GoInterface.nil
    else
      let: "e1" := (rec: "rmdir" <> :=
        let: "c" := ExternalOp Fs.fsExt.name "CallBegin" #() in
        let: "e1" := ExternalOp Fs.fsExt.name "Rmdir" ("c", "name") in
        if: "e1" =⟨go.uintptr⟩ #(W64 4) then "rmdir" #() else "e1") #() in
      if: "e1" =⟨go.uintptr⟩ #(W64 0) then #GoInterface.nil
      else model.pathError #"remove" "name"
        (syscall.model.errno (if: "e1" ≠⟨go.uintptr⟩ #(W64 20) then "e1" else "e")) -- ENOTDIR

/-- `Mkdir(name string, perm FileMode) error` (`file.go`): `mkdir(2)` (`EINTR` retried), an error
being `&PathError{"mkdir", name, Errno(e)}` (the extension's `Mkdir`, each attempt after its own
`CallBegin`); on Linux
nothing follows it
(`supportsCreateWithStickyBit`). `fixLongPath` is the identity off Windows; `perm` matters only to
the mode, which the extension does not model. -/
noncomputable def Mkdir.impl : val :=
  λ: "name" "perm",
    (rec: "mkdir" <> :=
      let: "c" := ExternalOp Fs.fsExt.name "CallBegin" #() in
      let: "e" := ExternalOp Fs.fsExt.name "Mkdir" ("c", "name") in
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
        let: "r" := ExternalOp Fs.fsExt.name "DirReadNext" "fd" in
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

/-! ## Path lookups and recursive tree changes (2026-11-13, the WAL over `fsExt`:
`notes/wal-fsext-plan.md`, section 4.3; drafts pending the user's review) -/

/-- `Stat(name)`'s and `Lstat(name)`'s body (`stat_unix.go`'s `statNolog`/`lstatNolog`): one
`stat(2)` (or `lstat(2)`) of the path, `EINTR` retried, into a fresh `fileStat`
(`fillFileStatFromSys`); an error is `&PathError{op, name, Errno(e)}` with a nil `FileInfo`.

The extension has no `stat` of a path (its `LstatDir` answers only `os.Rename`'s question, and
only with an error for a directory), so the model asks what a `stat` would by the steps it has: an
`open(name, O_RDONLY|O_CLOEXEC)` (the extension's `Open`, after its own `CallBegin`), whose fd says
whether the path is a file or a directory (`FdKind`), the size of a file (`Fstat`), and the fd is
closed at once (`Close`/`DirClose`, whose errno is ignored). Why this contains every answer of
Linux's `stat`: an `open` without `O_CREAT`/`O_TRUNC` changes no state but the fd table (the
`OpenEffect` of an existing path is none, and the fd is freed by the close before the model
returns; fd numbers are chosen arbitrarily by the extension anyway, so no other thread can tell);
where `stat` succeeds the path exists (in the roots' trees every entry is a regular file or a
directory, and there are no symlinks, so `stat` and `lstat` agree), and the extension's `Open`,
`FdKind` and `Fstat` can succeed with its kind and size (permissions are not modelled, so a
mode-000 file that `open` refuses with `EACCES` and `stat` does not still opens in the model);
where it fails, `Open` can fail with the same errno. The model has more answers than Linux (any
errno, `EMFILE` included, on an existing path), which only weakens what a proof shows. The mode
is the type (0 for a regular file, `ModeDir` for a directory) with arbitrary permission,
`setuid`, `setgid` and sticky bits (`model.arbitraryMode`; permissions are not modelled), and a
directory's size is arbitrary (Linux reports its blocks' bytes, which the extension does not
model). As every step on a path, the model is stuck on a path outside the roots' trees (Linux
answers there). The `CallBegin` makes a directory rename by another thread stuck until the `open`
(as for every path call), so `stat`'s walk never meets a moved directory. Go example:
`examples/osfs/semantics/model_os_stat.go`. -/
noncomputable def model.stat : val :=
  λ: "op" "name",
    (rec: "stat" <> :=
      let: "c" := ExternalOp Fs.fsExt.name "CallBegin" #() in
      let: "r" := ExternalOp Fs.fsExt.name "Open" ("c", ("name", #(W64 0x80000))) in
      if: Snd "r" =⟨go.uintptr⟩ #(W64 4) then "stat" #() -- EINTR
      else if: Snd "r" ≠⟨go.uintptr⟩ #(W64 0) then
        (GoZeroVal io.fs.FileInfo.ty #(),
         model.pathError "op" "name" (syscall.model.errno (Snd "r")))
      else
        let: "fd" := Fst "r" in
        let: "kind" := ExternalOp Fs.fsExt.name "FdKind" "fd" in
        let: "z" := if: "kind" =⟨go.uintptr⟩ #(W64 0) then ExternalOp Fs.fsExt.name "Fstat" "fd"
          else (ArbitraryInt, #(W64 0)) in
        (if: "kind" =⟨go.uintptr⟩ #(W64 0) then ExternalOp Fs.fsExt.name "Close" "fd"
         else ExternalOp Fs.fsExt.name "DirClose" "fd") ;;
        if: Snd "z" =⟨go.uintptr⟩ #(W64 4) then "stat" #() -- EINTR
        else if: Snd "z" ≠⟨go.uintptr⟩ #(W64 0) then
          (GoZeroVal io.fs.FileInfo.ty #(),
           model.pathError "op" "name" (syscall.model.errno (Snd "z")))
        else
          let: "fs" := GoAlloc model.fileStat (GoZeroVal model.fileStat #()) in
          StructFieldRef model.fileStat go!"size" "fs" <-[go.int64] Fst "z" ;;
          StructFieldRef model.fileStat go!"mode" "fs" <-[model.FileMode]
            model.arbitraryMode (if: "kind" =⟨go.uintptr⟩ #(W64 0) then #(W32 0)
              else #(W32 0x80000000)) ;;
          (Convert (go.PointerType model.fileStat) io.fs.FileInfo.ty "fs", #GoInterface.nil)) #()

/-- `Stat(name string) (FileInfo, error)` (`stat.go`: `testlog.Stat(name)`, a no-op outside
`go test`'s logging, then `statNolog`): `model.stat` with `Op` "stat". -/
noncomputable def Stat.impl : val :=
  λ: "name", model.stat #"stat" "name"

/-- `Lstat(name string) (FileInfo, error)` (`stat.go`, `lstatNolog`): `model.stat` with `Op`
"lstat". In the roots' trees there are no symlinks (the extension's environment), so `lstat`
answers as `stat` does. -/
noncomputable def Lstat.impl : val :=
  λ: "name", model.stat #"lstat" "name"

/-- `MkdirAll(path string, perm FileMode) error` (`path.go`): Go's body, as goose would translate
it, but for `len(filepathlite.VolumeName(path))`, which is 0 on Linux (`volumeNameLen` returns 0
in `internal/filepathlite`'s `path_unix.go`; `FromSlash` of the empty string is itself), so the
model writes 0 (`internal/filepathlite` is translated nowhere, which is why `MkdirAll` is a model):

```go
	dir, err := Stat(path)
	if err == nil {
		if dir.IsDir() {
			return nil
		}
		return &PathError{Op: "mkdir", Path: path, Err: syscall.ENOTDIR}
	}
	i := len(path) - 1
	for i >= 0 && IsPathSeparator(path[i]) {
		i--
	}
	for i >= 0 && !IsPathSeparator(path[i]) {
		i--
	}
	if i < 0 {
		i = 0
	}
	if parent := path[:i]; len(parent) > len(filepathlite.VolumeName(path)) {
		err = MkdirAll(parent, perm)
		if err != nil {
			return err
		}
	}
	err = Mkdir(path, perm)
	if err != nil {
		dir, err1 := Lstat(path)
		if err1 == nil && dir.IsDir() {
			return nil
		}
		return err
	}
	return nil
```

`Stat`, `Lstat`, `Mkdir`, `IsPathSeparator` and the recursive `MkdirAll` are called as Go calls
them (the models above, the translated `IsPathSeparator`), and `IsDir` through the `FileInfo`.
Go example: `examples/osfs/semantics/model_os_mkdirall.go`. -/
noncomputable def MkdirAll.impl : val :=
  λ: "path" "perm",
    let: "st" := (FuncResolve go!"os.Stat" []) #() "path" in
    if: Snd "st" =⟨go.error⟩ #GoInterface.nil then
      (if: (MethodResolve io.fs.FileInfo.ty go!"IsDir") (Fst "st") #() then #GoInterface.nil
       else model.pathError #"mkdir" "path" (syscall.model.errno #(W64 20))) -- ENOTDIR
    else
      let: "len" := (FuncResolve go.len [go.string]) #() "path" in
      let: "i" := (rec: "trail" "i" :=
          if: ("i" ≥⟨go.int⟩ #(W64 0)) &&
              ((FuncResolve go!"os.IsPathSeparator" []) #() (Index go.string ("path", "i")))
          then "trail" ("i" -⟨go.int⟩ #(W64 1)) else "i") ("len" -⟨go.int⟩ #(W64 1)) in
      let: "i" := (rec: "back" "i" :=
          if: ("i" ≥⟨go.int⟩ #(W64 0)) &&
              (⟨go.bool⟩! ((FuncResolve go!"os.IsPathSeparator" []) #()
                (Index go.string ("path", "i"))))
          then "back" ("i" -⟨go.int⟩ #(W64 1)) else "i") "i" in
      let: "i" := if: "i" <⟨go.int⟩ #(W64 0) then #(W64 0) else "i" in
      let: "parent" := Slice go.string ("path", #(W64 0), "i") in
      let: "e" := if: (FuncResolve go.len [go.string]) #() "parent" >⟨go.int⟩ #(W64 0)
        then (FuncResolve go!"os.MkdirAll" []) #() "parent" "perm" else #GoInterface.nil in
      if: "e" ≠⟨go.error⟩ #GoInterface.nil then "e"
      else
        let: "e" := (FuncResolve go!"os.Mkdir" []) #() "path" "perm" in
        if: "e" =⟨go.error⟩ #GoInterface.nil then #GoInterface.nil
        else
          let: "l" := (FuncResolve go!"os.Lstat" []) #() "path" in
          if: (Snd "l" =⟨go.error⟩ #GoInterface.nil) &&
              ((MethodResolve io.fs.FileInfo.ty go!"IsDir") (Fst "l") #())
          then #GoInterface.nil else "e"

/-- `&PathError{Op: op, Path: path, Err: err}`, the pointer (`model.pathError` converts it to an
`error`): `RemoveAll`'s model changes its `Path` after making it, as Go does. -/
noncomputable def model.pathErrorPtr : val :=
  λ: "op" "path" "err",
    let: "pe" := GoAlloc io.fs.PathError.ty (GoZeroVal io.fs.PathError.ty #()) in
    StructFieldRef io.fs.PathError.ty go!"Op" "pe" <-[go.string] "op" ;;
    StructFieldRef io.fs.PathError.ty go!"Path" "pe" <-[go.string] "path" ;;
    StructFieldRef io.fs.PathError.ty go!"Err" "pe" <-[go.error] "err" ;;
    "pe"

/-- `pe.Path = pre + "/" + pe.Path` for a non-nil `*PathError` `pe` (`removeall_at.go`). -/
noncomputable def model.prefixPath : val :=
  λ: "pe" "pre",
    if: "pe" =⟨go.PointerType io.fs.PathError.ty⟩ #null then #()
    else
      StructFieldRef io.fs.PathError.ty go!"Path" "pe" <-[go.string]
        ("pre" +⟨go.string⟩ #"/" +⟨go.string⟩
          ![go.string] (StructFieldRef io.fs.PathError.ty go!"Path" "pe"))

/-- `unlink(2)` of `p`, each attempt after its own `CallBegin`, `EINTR` retried: the errno. -/
noncomputable def model.unlinkLoop : val :=
  λ: "p", (rec: "unlink" <> :=
    let: "c" := ExternalOp Fs.fsExt.name "CallBegin" #() in
    let: "e" := ExternalOp Fs.fsExt.name "Unlink" ("c", "p") in
    if: "e" =⟨go.uintptr⟩ #(W64 4) then "unlink" #() else "e") #()

/-- `rmdir(2)` of `p`, each attempt after its own `CallBegin`, `EINTR` retried: the errno. -/
noncomputable def model.rmdirLoop : val :=
  λ: "p", (rec: "rmdir" <> :=
    let: "c" := ExternalOp Fs.fsExt.name "CallBegin" #() in
    let: "e" := ExternalOp Fs.fsExt.name "Rmdir" ("c", "p") in
    if: "e" =⟨go.uintptr⟩ #(W64 4) then "rmdir" #() else "e") #()

/-- `open(p, O_RDONLY|O_CLOEXEC)`, each attempt after its own `CallBegin`, `EINTR` retried:
`(fd, errno)`. -/
noncomputable def model.openLoop : val :=
  λ: "p", (rec: "open" <> :=
    let: "c" := ExternalOp Fs.fsExt.name "CallBegin" #() in
    let: "r" := ExternalOp Fs.fsExt.name "Open" ("c", ("p", #(W64 0x80000))) in
    if: Snd "r" =⟨go.uintptr⟩ #(W64 4) then "open" #() else "r") #()

/-- Close the fd `fd` of a file or of a directory (`FdKind`), ignoring the errno. -/
noncomputable def model.closeFd : val :=
  λ: "fd",
    if: ExternalOp Fs.fsExt.name "FdKind" "fd" =⟨go.uintptr⟩ #(W64 0) then
      ExternalOp Fs.fsExt.name "Close" "fd" ;; #()
    else ExternalOp Fs.fsExt.name "DirClose" "fd" ;; #()

/-- `removeAllFrom(parentFd, base)` (`removeall_at.go`), with the entry named by its path
`parent + "/" + base` instead of `base` under the fd of `parent` (`RemoveAll.impl` says why that
is faithful): the result is a `*PathError` (nil for success) whose `Path` is relative to `parent`,
as Go's.

```go
	err := removefileat(parentFd, base)          // unlinkat(parentFd, base, 0), EINTR retried
	if err == nil || IsNotExist(err) {
		return nil
	}
	if err != syscall.EISDIR && err != syscall.EPERM && err != syscall.EACCES {
		return &PathError{Op: "unlinkat", Path: base, Err: err}
	}
	uErr := err
	var recurseErr error
	for {
		const reqSize = 1024
		var respSize int
		file, err := openDirAt(parentFd, base)   // openat(O_DIRECTORY|O_NOFOLLOW|O_CLOEXEC)
		if err != nil {
			if IsNotExist(err) {
				return nil
			}
			if err == syscall.ENOTDIR {
				return &PathError{Op: "unlinkat", Path: base, Err: uErr}
			}
			...                                   // errSymlink: no symlinks in the roots' trees
			recurseErr = &PathError{Op: "openfdat", Path: base, Err: err}
			break
		}
		for {
			numErr := 0
			names, readErr := file.Readdirnames(reqSize)
			if readErr != nil && readErr != io.EOF {
				file.Close()
				if IsNotExist(readErr) {
					return nil
				}
				return &PathError{Op: "readdirnames", Path: base, Err: readErr}
			}
			respSize = len(names)
			for _, name := range names {
				err := removeAllFrom(sysfdType(file.Fd()), name)
				if err != nil {
					if pathErr, ok := err.(*PathError); ok {
						pathErr.Path = base + string(PathSeparator) + pathErr.Path
					}
					numErr++
					if recurseErr == nil {
						recurseErr = err
					}
				}
			}
			if numErr != reqSize {
				break
			}
		}
		file.Close()
		if respSize < reqSize {
			break
		}
	}
	unlinkError := removedirat(parentFd, base)   // unlinkat(parentFd, base, AT_REMOVEDIR)
	if unlinkError == nil || IsNotExist(unlinkError) {
		return nil
	}
	if recurseErr != nil {
		return recurseErr
	}
	return &PathError{Op: "unlinkat", Path: base, Err: unlinkError}
```

The `unlinkat`s are the extension's `Unlink` and `Rmdir` of the path, and `openDirAt` its `Open`
of the path (`O_RDONLY|O_CLOEXEC`: the extension does not take `O_DIRECTORY`; an fd of a file,
`FdKind`, is closed and answered as `ENOTDIR`, which Linux returns without opening). The reads of
a pass are one `Readdirnames(-1)` of the directory (the extension's `DirReadNext` until the end,
`EINTR` retried, as `File.Readdirnames.impl`; an error is `&PathError{"readdirent", base,
Errno(e)}`, as Go's `readdir` makes it), all of whose names are then removed. Go's pass is not
that: it reads one chunk of up to 1024 names, removes them, and (unless all 1024 removals failed,
when it reads the next chunk from the same fd) closes the directory and reopens it, so under a
concurrent creation a later pass reads new entries mixed with old ones not yet removed (measured:
an entry created after the first unlink removed while older entries were still present, 20 of 20
runs; `notes/wal-fsext-models-review.md`, finding 3). The model still has each such run, for a
reason that is load-bearing: the extension's `Unlink` and `Rmdir` may fail with any errno and no
effect, `ENOENT` included, and `ENOENT` is success here (`IsNotExist`, no error recorded). So the
model's first pass may read every name and remove only Go's first chunk (the other removals
failing with `ENOENT` and no effect), and each later pass reads what Go's next one reads (POSIX's
`readdir`: by the end, every name present throughout the read; an entry added or removed meanwhile
may or may not be returned) and does the same. A tightening of the extension's failure branches
(say, `ENOENT` only when there is no entry) would make this model unsound: it would then need
passes that stop reading at a chunk. Whether another pass follows is arbitrary (`ArbitraryInt`):
Go makes one more exactly when a chunk was full, which depends on the directory's size and on
entries added meanwhile; the model allows every number of passes. Errors
are Go's (`ENOENT` is `IsNotExist`'s errno; `ENOTDIR` 20, `EISDIR` 21, `EPERM` 1, `EACCES` 13). -/
noncomputable def model.removeAllFrom : val :=
  rec: "from" "parent" "base" :=
    let: "p" := "parent" +⟨go.string⟩ #"/" +⟨go.string⟩ "base" in
    let: "e" := model.unlinkLoop "p" in
    if: ("e" =⟨go.uintptr⟩ #(W64 0)) || ("e" =⟨go.uintptr⟩ #(W64 2)) then #null
    else if: ("e" ≠⟨go.uintptr⟩ #(W64 21)) && ("e" ≠⟨go.uintptr⟩ #(W64 1)) &&
        ("e" ≠⟨go.uintptr⟩ #(W64 13)) then
      model.pathErrorPtr #"unlinkat" "base" (syscall.model.errno "e")
    else
      -- the passes: `(#0, pe)` returns `pe` at once, `(#1, recurseErr)` goes on to the `rmdir`
      let: "res" := (rec: "pass" "rerr" :=
        let: "o" := model.openLoop "p" in
        if: Snd "o" ≠⟨go.uintptr⟩ #(W64 0) then
          (if: Snd "o" =⟨go.uintptr⟩ #(W64 2) then (#(W64 0), #null)
           else if: Snd "o" =⟨go.uintptr⟩ #(W64 20) then
             (#(W64 0), model.pathErrorPtr #"unlinkat" "base" (syscall.model.errno "e"))
           else (#(W64 1), model.pathErrorPtr #"openfdat" "base" (syscall.model.errno (Snd "o"))))
        else
          let: "fd" := Fst "o" in
          if: ExternalOp Fs.fsExt.name "FdKind" "fd" =⟨go.uintptr⟩ #(W64 0) then
            ExternalOp Fs.fsExt.name "Close" "fd" ;;
            (#(W64 0), model.pathErrorPtr #"unlinkat" "base" (syscall.model.errno "e"))
          else
            let: "rd" := (rec: "read" "names" :=
              let: "r" := ExternalOp Fs.fsExt.name "DirReadNext" "fd" in
              let: "re" := Snd (Snd "r") in
              if: "re" =⟨go.uintptr⟩ #(W64 4) then "read" "names" -- EINTR
              else if: "re" ≠⟨go.uintptr⟩ #(W64 0) then ("names", "re")
              else if: Fst (Snd "r") =⟨go.uintptr⟩ #(W64 1) then ("names", #(W64 0))
              else
                let: "nm" := Fst "r" in
                "read" ((FuncResolve go.append [go.GoType.SliceType go.string]) #() "names"
                  (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.string))))
                    (LiteralValue [KeyedElement none (ElementExpression go.string (Var "nm"))]))))
              (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.string))))
                (LiteralValue [])) in
            if: Snd "rd" ≠⟨go.uintptr⟩ #(W64 0) then
              ExternalOp Fs.fsExt.name "DirClose" "fd" ;;
              (if: Snd "rd" =⟨go.uintptr⟩ #(W64 2) then (#(W64 0), #null)
               else (#(W64 0), model.pathErrorPtr #"readdirnames" "base"
                 (model.pathError #"readdirent" "base" (syscall.model.errno (Snd "rd")))))
            else
              let: "names" := Fst "rd" in
              let: "n" := (FuncResolve go.len [go.GoType.SliceType go.string]) #() "names" in
              let: "rerr" := (rec: "each" "k" "rerr" :=
                if: "k" =⟨go.int⟩ "n" then "rerr"
                else
                  let: "pe" := "from" "p"
                    (![go.string] (IndexRef (go.GoType.SliceType go.string) ("names", "k"))) in
                  model.prefixPath "pe" "base" ;;
                  "each" ("k" +⟨go.int⟩ #(W64 1))
                    (if: "rerr" =⟨go.PointerType io.fs.PathError.ty⟩ #null then "pe" else "rerr"))
                #(W64 0) "rerr" in
              ExternalOp Fs.fsExt.name "DirClose" "fd" ;;
              if: ArbitraryInt =⟨go.uint64⟩ #(W64 0) then (#(W64 1), "rerr") else "pass" "rerr")
        #null in
      if: Fst "res" =⟨go.uint64⟩ #(W64 0) then Snd "res"
      else
        let: "e4" := model.rmdirLoop "p" in
        if: ("e4" =⟨go.uintptr⟩ #(W64 0)) || ("e4" =⟨go.uintptr⟩ #(W64 2)) then #null
        else if: Snd "res" ≠⟨go.PointerType io.fs.PathError.ty⟩ #null then Snd "res"
        else model.pathErrorPtr #"unlinkat" "base" (syscall.model.errno "e4")

/-- `RemoveAll(path string) error` (`path.go`, `removeall_at.go`'s `removeAll`):

```go
	if path == "" {
		return nil
	}
	if endsWithDot(path) {
		return &PathError{Op: "RemoveAll", Path: path, Err: syscall.EINVAL}
	}
	err := Remove(path)
	if err == nil || IsNotExist(err) {
		return nil
	}
	parentDir, base := splitPath(path)
	parent, err := OpenFile(parentDir, O_RDONLY, 0)
	if IsNotExist(err) {
		return nil
	}
	if err != nil {
		return err
	}
	defer parent.Close()
	if err := removeAllFrom(sysfdType(parent.Fd()), base); err != nil {
		if pathErr, ok := err.(*PathError); ok {
			pathErr.Path = parentDir + string(PathSeparator) + pathErr.Path
			err = pathErr
		}
		return err
	}
	return nil
```

Go's body is not translated: below `Remove` it is over the `*at` system calls (`unlinkat`,
`openat` relative to a directory's fd), which the extension does not have (its steps name paths).
The model is that body over paths: `Remove` as `Remove.impl` (inlined, for its errno), the parent
opened as `OpenFile` does (and closed), and `removeAllFrom` with each entry named by its path
(`model.removeAllFrom`). A path and a name under an open directory's fd name the same entry as long
as no directory above it is moved: the model takes a `CallBegin` at its start and ends it at its
return (with a `LstatDir` of `path`, a step without effect), so that every rename of a directory by
another thread is stuck while it runs (the extension's `Rename`), and the proved programs, which are
never stuck, have no such rename. What is left is a directory above it removed and another made
in its place by another thread (Go's `*at` calls then act on the removed one, which no path names,
and fail or change nothing a path can see; the model's calls on the new one may fail with any errno
and no effect, which is the outcome Linux's leave visible). `IsNotExist` of these errors is an
errno of `ENOENT` (2); `ENOTDIR` 20; `EINVAL` 22. `splitPath` and `endsWithDot` are the translated
Go helpers. Go example: `examples/osfs/semantics/model_os_removeall.go`. -/
noncomputable def RemoveAll.impl : val :=
  λ: "path",
    if: "path" =⟨go.string⟩ #"" then #GoInterface.nil
    else if: (FuncResolve go!"os.endsWithDot" []) #() "path" then
      model.pathError #"RemoveAll" "path" (syscall.model.errno #(W64 22))
    else
      let: "g" := ExternalOp Fs.fsExt.name "CallBegin" #() in
      let: "r" :=
        (let: "e" := model.unlinkLoop "path" in
         if: "e" =⟨go.uintptr⟩ #(W64 0) then #GoInterface.nil
         else
           let: "e1" := model.rmdirLoop "path" in
           if: "e1" =⟨go.uintptr⟩ #(W64 0) then #GoInterface.nil
           else
             let: "e" := if: "e1" ≠⟨go.uintptr⟩ #(W64 20) then "e1" else "e" in
             if: "e" =⟨go.uintptr⟩ #(W64 2) then #GoInterface.nil
             else
               let: "sp" := (FuncResolve go!"os.splitPath" []) #() "path" in
               let: "parentDir" := Fst "sp" in
               let: "o" := model.openLoop "parentDir" in
               if: Snd "o" =⟨go.uintptr⟩ #(W64 2) then #GoInterface.nil
               else if: Snd "o" ≠⟨go.uintptr⟩ #(W64 0) then
                 model.pathError #"open" "parentDir" (syscall.model.errno (Snd "o"))
               else
                 let: "pe" := model.removeAllFrom "parentDir" (Snd "sp") in
                 model.closeFd (Fst "o") ;;
                 if: "pe" =⟨go.PointerType io.fs.PathError.ty⟩ #null then #GoInterface.nil
                 else
                   model.prefixPath "pe" "parentDir" ;;
                   Convert (go.PointerType io.fs.PathError.ty) go.error "pe") in
      ExternalOp Fs.fsExt.name "LstatDir" ("g", "path") ;;
      "r"

/-! ## The initializer's untranslated pieces (2026-11-07, as Perennial's `TrustedCode/os.lean`) -/

/-- `runtime_args() []string` (`proc.go`: `func runtime_args() []string // in package
runtime`): a `go:linkname` with no Go body; the runtime returns a copy of the command-line
arguments. The model: an arbitrary `[]string` (`syscall.arbitraryStrings`), which covers every
argument list. -/
noncomputable def runtime_args.impl : val :=
  syscall.arbitraryStrings

/-! ## The standard streams

```go
var (
	Stdin  = NewFile(uintptr(syscall.Stdin), "/dev/stdin")
	Stdout = NewFile(uintptr(syscall.Stdout), "/dev/stdout")
	Stderr = NewFile(uintptr(syscall.Stderr), "/dev/stderr")
)
```

`NewFile` wraps the descriptor in a `*File`: it reads the descriptor's flags (`unix.Fcntl`, a
system call), registers it with the runtime's poller (`runtime_pollServerInit`,
`runtime_pollOpen`, linknames) and sets a finalizer (`runtime.SetFinalizer(f.file,
(*file).close)`). It cannot panic. These initializers are not translated, by the user's decision
(Perennial fix-semantics Case 33, 2026-11-04: "I don't want to reason about any of that. What about a
trusted model that does nothing? This is conservative because it leaves Stdin, Stdout, Stderr as
undefined, so any code relying on it will be unprovable. I do not want to follow the rule
'translatable => *must* verify' in this case."). The models give a proof less than Go does,
never more: -/

/-- `Stdin`'s initializer. The model does nothing: the variable is not allocated, so code that
loads `os.Stdin` is stuck (has no proof), where Go reads a `*File`. -/
def Stdin.init : val :=
  λ: <>, #()

/-- `Stdout`'s initializer. The model does nothing: the variable is not allocated, so code that
loads `os.Stdout` is stuck (has no proof), where Go reads a `*File`. -/
def Stdout.init : val :=
  λ: <>, #()

/-- `Stderr`'s initializer. Unlike `Stdin` and `Stdout`, the model allocates the variable,
because package initializers that only load `os.Stderr` (raft's `defaultLogger`,
`log.New(os.Stderr, ...)`) must be provable. It stores a pointer from `GoPrealloc`: an arbitrary
address in `(0, maxAddr)` (`go_prealloc_step`), at which the model allocates no cell. So the
variable holds a non-`nil` `*File`, as in Go, and loading it steps; anything that reads or writes
through it (a method call, a field, `*os.Stderr = File{}`) has no proof: a proof covers every
placement, and in those where no later allocation lands at that address the access is stuck,
where Go reads or writes the `File`. `GoPrealloc` reserves nothing: a later allocation may land at
the address, so the address's order against allocations, and whether it equals a later
allocation's, are nondeterministic; a program that compares them (`unsafe.Pointer(os.Stderr) ==
unsafe.Pointer(new(File))`) may then fail in the model where Go does not, which only makes the
model less defined than Go. (2026-11-07, the review of `os-init-lean`: first a fresh `Alloc #()`,
a writable cell, so `*os.Stderr = os.File{}; log.Printf("x")` ran in the model and panics in Go;
then `maxAddr + 1`, outside every allocation, which a program walking addresses from
`os.Stderr` up to a later allocation could tell apart from Go's.) -/
def Stderr.init : val :=
  λ: <>,
    go.GlobalAlloc go!"os.Stderr" (go.GoType.PointerType (go.GoType.Named go!"os.File" [])) #() ;;
    GlobalVarAddr go!"os.Stderr" #() <-[go.GoType.PointerType (go.GoType.Named go!"os.File" [])]
      (GoPrealloc #())

end code
end os

end Perennial
