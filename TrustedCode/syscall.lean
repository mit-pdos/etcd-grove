/-
Trusted code of `syscall` (namespace of the generated package; project bboltfs of `etc/goose.py`,
`Code/syscall.toml`): the GooseLang models of the primitive stubs of `syscall`'s Go model
(`models/syscall/stubs.go`; the model itself, `models/syscall/model.go`, is Go, translated), each
one operation of the Linux file extension of `GooseLang.Ext.Fs.Impl` (`Fs.fsExt`), or one call's two
steps; `runtime_envs`, a linkname into the runtime with no Go body, a primitive; and `Exit`, a
body-less declaration the runtime provides (zap-z2, 2026-11-23). linux/amd64.

Until 2026-11-24 (Go-model overlays S5, perennial#692) this file held hand-written GooseLang models
of `Fdatasync`, `Flock`, `Fallocate`, `FcntlFlock`, `Errno.Error` and `init.0`;
`models/syscall/model.go` is that model in Go, function by function (`Errno.Error` is translated
with Go's body since origin/lean's fmt stage 1, 2026-11-24). An errno is a `w64`, the value
of an `Errno` (`uintptr`).
-/
module

public import Perennial.Golang.Defn
public import GooseLang.Ext.Fs.Impl
public import Perennial.TrustedCode.fmt

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace syscall
section code
variable [GooseExts] [GoGlobalContext]

/-- `errnoErr(e)` (`syscall_unix.go`): `nil` for 0, else `Errno(e)` as an `error`. Not a Go
function: a helper of `golang.org/x/sys/unix`'s hand-written models
(`TrustedCode/golang_org/x/sys/unix.lean`). -/
noncomputable def model.errno : val :=
  λ: "e", if: "e" =⟨go.uintptr⟩ #(W64 0) then #GoInterface.nil
    else Convert (go.GoType.Named go!"syscall.Errno" []) go.error "e"

/-- `fsFsync(fd int) uintptr`: the extension's `Fsync`. -/
noncomputable def fsFsync.impl : val :=
  λ: "fd", ExternalOp Fs.fsExt.name "Fsync" "fd"

/-- `fsFlock(fd int, how int) uintptr`: the extension's `Flock` of `(fd, how)`. -/
noncomputable def fsFlock.impl : val :=
  λ: "fd" "how", ExternalOp Fs.fsExt.name "Flock" ("fd", "how")

/-- `fsFalloc(fd int, off int64, len int64) uintptr`: the extension's `FallocStart` of
`(fd, off, len)`, then `FallocFinish` of its token. -/
noncomputable def fsFalloc.impl : val :=
  λ: "fd" "off" "len",
    ExternalOp Fs.fsExt.name "FallocFinish"
      (ExternalOp Fs.fsExt.name "FallocStart" ("fd", ("off", "len")))

/-- `fsFallocKeep(fd int, off int64, len int64) uintptr`: the extension's `FallocKeep`. -/
noncomputable def fsFallocKeep.impl : val :=
  λ: "fd" "off" "len", ExternalOp Fs.fsExt.name "FallocKeep" ("fd", ("off", "len"))

/-- `fsOfdLock(fd uintptr, cmd int, typ int) uintptr`: the extension's `OfdLock` of
`(fd, (cmd, typ))`. -/
noncomputable def fsOfdLock.impl : val :=
  λ: "fd" "cmd" "typ", ExternalOp Fs.fsExt.name "OfdLock" ("fd", ("cmd", "typ"))

/-- `fsMkdir(path string, mode uint32) uintptr`: `CallBegin` of `path`, then the extension's
`Mkdir`; `mode` is not passed (the extension does not model modes). -/
noncomputable def fsMkdir.impl : val :=
  λ: "path" "mode",
    ExternalOp Fs.fsExt.name "Mkdir" (ExternalOp Fs.fsExt.name "CallBegin" "path", "path")

/-- `fsUnlink(path string) uintptr`: `CallBegin` of `path`, then the extension's `Unlink`. -/
noncomputable def fsUnlink.impl : val :=
  λ: "path",
    ExternalOp Fs.fsExt.name "Unlink" (ExternalOp Fs.fsExt.name "CallBegin" "path", "path")

/-- `fsRmdir(path string) uintptr`: `CallBegin` of `path`, then the extension's `Rmdir`. -/
noncomputable def fsRmdir.impl : val :=
  λ: "path",
    ExternalOp Fs.fsExt.name "Rmdir" (ExternalOp Fs.fsExt.name "CallBegin" "path", "path")

/-- `fsPathKind(path string) uintptr`: the extension's `PathKind` (a query of its environment). -/
noncomputable def fsPathKind.impl : val :=
  λ: "path", ExternalOp Fs.fsExt.name "PathKind" "path"

/-- An arbitrary `[]string`: the model of a `go:linkname` into the runtime that returns the
process's strings (`runtime_envs` here, `os.runtime_args`). It is goose's translation of

```go
func arbitraryStrings() []string {
	var a []string
	if arbitrary() != 0 {
		a = []string{}
	}
	for arbitrary() != 0 {
		a = append(a, arbitraryString())
	}
	return a
}
```

with each call `arbitrary()` replaced by `ArbitraryInt` (an arbitrary `uint64`) and
`arbitraryString()` by `fmt.arbitraryString` (every string). It can return every slice of
strings, `nil` and a non-`nil` empty slice included (and may also not terminate, which
partial correctness allows). Go's `runtime_envs`/`runtime_args` never return `nil` (`envs` is a
non-`nil` empty slice under `env -i`, on any kernel); `nil` is a behavior of the model only, which
a proof must also cover. -/
noncomputable def arbitraryStrings : val :=
  (LamV BAnon
  (Let "$res0" (App (Val (GoInstruction (GoAlloc (go.GoType.SliceType go.string)))) (App (Val (GoInstruction (GoZeroVal (go.GoType.SliceType go.string)))) (Val #())))
  (Seq (App (Val exceptionDo)
  (Let "a" (App (Val (GoInstruction (GoAlloc (go.GoType.SliceType go.string)))) (App (Val (GoInstruction (GoZeroVal (go.GoType.SliceType go.string)))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.string)))) (Var "a"))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore (go.GoType.SliceType go.string)))) (Pair (Var "$res0") (Var "$r0"))))))))
  (App (App (App (Val doFor) (Lam BAnon
  (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.uint64))) (Pair ArbitraryInt (Val #(W64 0))))))) (Lam BAnon
  (Let "$r0" (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.string)))) (Var "a"))
  (Let "$a1" (Let "$sl0" (App (Val fmt.arbitraryString) (Val #()))
  (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.string)))) (LiteralValue [(KeyedElement none (ElementExpression go.string (Var "$sl0")))])))
  (App (App (App (Val (GoInstruction (FuncResolve go.append [(go.GoType.SliceType go.string)]))) (Val #())) (Var "$a0")) (Var "$a1"))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore (go.GoType.SliceType go.string)))) (Pair (Var "a") (Var "$r0")))))))
  (Lam BAnon
  (Val #()))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.uint64))) (Pair ArbitraryInt (Val #(W64 0))))))
  (Let "$r0" (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.string)))) (LiteralValue []))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore (go.GoType.SliceType go.string)))) (Pair (Var "a") (Var "$r0")))))
  (App (Val doExecute)
  (Val #()))))))
  (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.string)))) (Var "$res0")))))

/-- `runtime_envs() []string` (`env_unix.go`: `func runtime_envs() []string // in package
runtime`): a `go:linkname` with no Go body; the runtime returns a copy of the process's
environment. The model: an arbitrary `[]string` (`arbitraryStrings`), which covers every
environment. (2026-11-24, Go-model overlays: a local equivalent, to become
`internal.gomodel.ChooseStrings`, Perennial's translated Go, at the integration pin bump.) -/
noncomputable def runtime_envs.impl : val :=
  arbitraryStrings

/-- `Exit(code int)` (`syscall.go`: `func Exit(code int)`, no Go body; the runtime provides it,
`runtime.syscall_Exit`, the `exit_group` system call; zap-z2, 2026-11-23, as Perennial's
`TrustedCode/syscall.lean` since `ca6df841b`): the process ends with status `code`; no deferred
function runs and no goroutine takes another step. The model: `AngelicExit`, which steps to itself
for good, so the calling goroutine never returns (its deferred functions never run) and the code
after the call is never reached. The other goroutines keep running in the model, where Go stops
them: the model has more executions than Go, each of whose prefixes up to the exit is one of Go's
(Perennial's `goose/model/runtime/exit_test.go`), as when `main` returns. -/
def Exit.impl : val :=
  λ: "code",
    AngelicExit #()

end code
end syscall

end Perennial
