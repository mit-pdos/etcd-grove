/-
Trusted code of `os` (namespace of the generated package; project bboltfs of `etc/goose.py`,
`Code/os.toml`): the GooseLang models of the primitive stubs of `os`'s Go model
(`models/os/stubs.go`; the model itself, `models/os/model.go`, is Go, translated), each one
operation of the Linux file extension of `GooseLang.Ext.Fs.Impl` (`Fs.fsExt`), or one call's two
steps; `runtime_args`, a linkname into the runtime with no Go body; and the initializers of the
standard streams. linux/amd64, Go 1.27.3. Perennial's own
translation of `os` (`Perennial.Code.os`) must not be in the same import closure.

Until 2026-11-24 (Go-model overlays S5, perennial#692) this file held the whole model as
hand-written GooseLang: the layouts of `file` and `fileStat` (with hand-stated field facts,
`os.file.FieldAssumptions`/`os.fileStat.FieldAssumptions`) and the models of `OpenFile`, the
`File` methods, `Stat`, `MkdirAll`, `RemoveAll`, ...; `models/os/model.go` is that model in Go,
function by function, `file` is Go's layout plus the kernel's offset, and `fileStat` is Go's.

Each stub's `.impl` passes its arguments to the operation as the extension takes them (nested pairs)
and returns its result as goose returns the Go results (a pair, or `((a, b), c)` for three). An
errno is a `w64`, the value of a `uintptr`. The path operations take their `CallBegin` (the
extension's start of a call on a path, whose token its next step takes) inside the stub, so the
token, an extension value, never reaches a Go variable.
-/
module

public import Perennial.Golang.Defn
public import GooseLang.Ext.Fs.Impl
public import TrustedCode.syscall

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace os
section code
variable [GooseExts] [GoGlobalContext]

/-- `fsOpen(name string, flag int, perm uint32) (int, uintptr)`: `CallBegin` of `name`, then the
extension's `Open` of `(token, name, flag)`: `(fd, errno)`. `perm` is not passed: the extension does
not model file modes. -/
noncomputable def fsOpen.impl : val :=
  λ: "name" "flag" "perm",
    ExternalOp Fs.fsExt.name "Open" (ExternalOp Fs.fsExt.name "CallBegin" "name", ("name", "flag"))

/-- `fsPRead(fd int, off int64, n int) (string, uintptr)`: the extension's `PRead`. -/
noncomputable def fsPRead.impl : val :=
  λ: "fd" "off" "n", ExternalOp Fs.fsExt.name "PRead" ("fd", ("off", "n"))

/-- `fsPWrite(fd int, off int64, data string) (int, uintptr)`: the extension's `PWriteStart`
(announcing the write), then `PWriteFinish` of its token: `(written, errno)`. -/
noncomputable def fsPWrite.impl : val :=
  λ: "fd" "off" "data",
    ExternalOp Fs.fsExt.name "PWriteFinish"
      (ExternalOp Fs.fsExt.name "PWriteStart" ("fd", ("off", "data")))

/-- `fsFdKind(fd int) uintptr`: the extension's `FdKind` (a query of its state). -/
noncomputable def fsFdKind.impl : val :=
  λ: "fd", ExternalOp Fs.fsExt.name "FdKind" "fd"

/-- `fsClose(fd int) uintptr`: the extension's `Close`. -/
noncomputable def fsClose.impl : val :=
  λ: "fd", ExternalOp Fs.fsExt.name "Close" "fd"

/-- `fsDirClose(fd int) uintptr`: the extension's `DirClose`. -/
noncomputable def fsDirClose.impl : val :=
  λ: "fd", ExternalOp Fs.fsExt.name "DirClose" "fd"

/-- `fsOutClose(fd int) uintptr`: the extension's `OutClose`. -/
noncomputable def fsOutClose.impl : val :=
  λ: "fd", ExternalOp Fs.fsExt.name "OutClose" "fd"

/-- `fsFstat(fd int) (int64, uintptr)`: the extension's `Fstat`: `(size, errno)`. -/
noncomputable def fsFstat.impl : val :=
  λ: "fd", ExternalOp Fs.fsExt.name "Fstat" "fd"

/-- `fsFtruncate(fd int, size int64) uintptr`: the extension's `FtruncateStart`, then
`FtruncateFinish` of its token. -/
noncomputable def fsFtruncate.impl : val :=
  λ: "fd" "size",
    ExternalOp Fs.fsExt.name "FtruncateFinish"
      (ExternalOp Fs.fsExt.name "FtruncateStart" ("fd", "size"))

/-- `fsFsync(fd int) uintptr`: the extension's `Fsync`. -/
noncomputable def fsFsync.impl : val :=
  λ: "fd", ExternalOp Fs.fsExt.name "Fsync" "fd"

/-- `fsDirSync(fd int) uintptr`: the extension's `DirSync`. -/
noncomputable def fsDirSync.impl : val :=
  λ: "fd", ExternalOp Fs.fsExt.name "DirSync" "fd"

/-- `fsOutSync(fd int) uintptr`: the extension's `OutSync`. -/
noncomputable def fsOutSync.impl : val :=
  λ: "fd", ExternalOp Fs.fsExt.name "OutSync" "fd"

/-- `fsLstatDir(name string) (uintptr, uintptr)`: `CallBegin` of `name`, then the extension's
`LstatDir` of `(token, name)`: `(isDir, errno)`. -/
noncomputable def fsLstatDir.impl : val :=
  λ: "name",
    ExternalOp Fs.fsExt.name "LstatDir" (ExternalOp Fs.fsExt.name "CallBegin" "name", "name")

/-- `fsRename(oldpath, newpath string) uintptr`: `CallBegin` of `oldpath`, then the extension's
`Rename` of `(token, oldpath, newpath)`. -/
noncomputable def fsRename.impl : val :=
  λ: "oldpath" "newpath",
    ExternalOp Fs.fsExt.name "Rename"
      (ExternalOp Fs.fsExt.name "CallBegin" "oldpath", ("oldpath", "newpath"))

/-- `fsUnlink(name string) uintptr`: `CallBegin` of `name`, then the extension's `Unlink`. -/
noncomputable def fsUnlink.impl : val :=
  λ: "name",
    ExternalOp Fs.fsExt.name "Unlink" (ExternalOp Fs.fsExt.name "CallBegin" "name", "name")

/-- `fsRmdir(name string) uintptr`: `CallBegin` of `name`, then the extension's `Rmdir`. -/
noncomputable def fsRmdir.impl : val :=
  λ: "name",
    ExternalOp Fs.fsExt.name "Rmdir" (ExternalOp Fs.fsExt.name "CallBegin" "name", "name")

/-- `fsDirReadNext(fd int) (string, uintptr, uintptr)`: the extension's `DirReadNext`, whose
`(name, (done, errno))` is returned as goose returns three results, `((name, done), errno)`. -/
noncomputable def fsDirReadNext.impl : val :=
  λ: "fd",
    let: "r" := ExternalOp Fs.fsExt.name "DirReadNext" "fd" in
    ((Fst "r", Fst (Snd "r")), Snd (Snd "r"))

/-- `fsPathKind(name string) uintptr`: the extension's `PathKind` (a query of its environment). -/
noncomputable def fsPathKind.impl : val :=
  λ: "name", ExternalOp Fs.fsExt.name "PathKind" "name"

/-- `fsWithCall(path string, body func() error) error`: `body()` inside a `CallBegin` of `path`,
ended after it returns by the extension's `LstatDir` of `(token, path)` (a step without effect, whose
result is dropped): `RemoveAll`'s model holds the call so that a concurrent rename of a directory in
`path`'s root's tree is stuck meanwhile (`models/os/model.go`, `RemoveAll`). -/
noncomputable def fsWithCall.impl : val :=
  λ: "path" "body",
    let: "g" := ExternalOp Fs.fsExt.name "CallBegin" "path" in
    let: "r" := "body" #() in
    ExternalOp Fs.fsExt.name "LstatDir" ("g", "path") ;;
    "r"

/-- `runtime_args() []string` (`proc.go`: `func runtime_args() []string // in package
runtime`): a `go:linkname` with no Go body; the runtime returns a copy of the command-line
arguments. The model: an arbitrary `[]string` (`syscall.arbitraryStrings`), which covers every
argument list. (2026-11-24, Go-model overlays: a local equivalent, to become
`internal.gomodel.ChooseStrings`, Perennial's translated Go, at the integration pin bump.) -/
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
