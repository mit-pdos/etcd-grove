/-
Trusted Go model of `syscall` (namespace of the generated package; project bboltfs of
`etc/goose.py`, `Code/syscall.toml`), in terms of the Linux file extension of
`GooseLang.Ext.Fs.Impl` (`Fs.fsExt`, `ExternalOp Fs.fsExt.name "Fsync"`, ...), for any program
whose extensions include it. linux/amd64.

The functions are `zsyscall_linux_amd64.go`'s system-call stubs: one `Syscall` and
`errnoErr(e1)`, which is `nil` for errno 0 and otherwise `Errno(e1)` boxed as an `error` (some
values from preallocated variables, `errEAGAIN`, ..., which are equal to the boxed `Errno` as
interface values, and so indistinguishable). There is no `EINTR` retry at this level. An errno is
a `w64`, the value of an `Errno` (`uintptr`).
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
function of the model: a helper of the models here, of `os`'s and of `golang.org/x/sys/unix`'s
(`errnoErr` there is the same). -/
noncomputable def model.errno : val :=
  λ: "e", if: "e" =⟨go.uintptr⟩ #(W64 0) then #GoInterface.nil
    else Convert (go.GoType.Named go!"syscall.Errno" []) go.error "e"

/-- `Fdatasync(fd int) error`: `fdatasync(2)`, which the extension does not distinguish from
`fsync(2)` (`notes/osfs-ext-plan.md`, D3: Linux's `fdatasync` also flushes the size, which is
all the metadata the extension has): its `Fsync` (stuck on an fd that is not open, else success
or any nonzero errno). -/
noncomputable def Fdatasync.impl : val :=
  λ: "fd", model.errno (ExternalOp Fs.fsExt.name "Fsync" "fd")

/-- `Flock(fd int, how int) error`: `flock(2)`, trivial (`notes/osfs-ext-plan.md`, D7): the
specifications are about one process, which never contends with itself for a lock it holds
through one open file description, so the lock state is not modelled. The result is `nil` or an
arbitrary nonzero `Errno`, the extension's `Flock`: it covers every answer Linux gives, a lock
held elsewhere (`EWOULDBLOCK` with `LOCK_NB`), `EINTR`, `EINVAL` for a bad `how`, `ENOLCK`. It is
stuck on an fd that is not open (D6). A blocking `flock` that never returns is a run the model
need not contain. -/
noncomputable def Flock.impl : val :=
  λ: "fd" "how", model.errno (ExternalOp Fs.fsExt.name "Flock" ("fd", "how"))

/-- `(Errno).Error() string` (`syscall_unix.go`): some string. Go's body

```go
	if 0 <= int(e) && int(e) < len(errors) {
		s := errors[e]
		if s != "" {
			return s
		}
	}
	return "errno " + strconv.Itoa(int(e))
```

reads the read-only table `errors` (`zerrors_linux_amd64.go`, whose initializer goose does not
translate) inside its bounds, and calls `strconv.Itoa`: it returns a string, never panics, and
touches no memory a caller owns. The model returns an arbitrary string (Perennial's
`fmt.arbitraryString`, which can return every string), so every result of Go's is one of the
model's. -/
noncomputable def Errno.Error.impl : val :=
  λ: "e" <>, _root_.Perennial.fmt.arbitraryString #()

/-! ## fileutil's calls (2026-11-13, the WAL over `fsExt`; drafts pending the user's review) -/

/-- `Fallocate(fd int, mode uint32, off int64, len int64) error` (`zsyscall_linux_amd64.go`: one
`fallocate(2)`, `Syscall6(SYS_FALLOCATE, ...)` and `errnoErr`, `EINTR` not retried): the same system
call stub as `golang.org/x/sys/unix.Fallocate`, and the same model
(`TrustedCode/golang_org/x/sys/unix.lean`, which imports this file, so the body is repeated here).
Mode 0 is the extension's `FallocStart`, a resize to `max size (off + len)` in flight, and
`FallocFinish` (on failure, any size between); `FALLOC_FL_KEEP_SIZE` (1) is `FallocKeep`, no
visible change, any errno. Both are stuck on a negative `off` or a `len` not above 0 (Linux:
`EINVAL`: misuse) and on an fd that is not a writable file's. Other modes (punching or zeroing a
range, collapsing, inserting) are not modelled: a panic, never reached by a proved program.
fileutil's `Preallocate` (`preallocate_unix.go`) issues modes 0 and 1 only. Go example:
`examples/osfs/semantics/model_syscall_fallocate.go`. -/
noncomputable def Fallocate.impl : val :=
  λ: "fd" "mode" "off" "len",
    if: "mode" =⟨go.uint32⟩ #(W32 0) then
      model.errno (ExternalOp Fs.fsExt.name "FallocFinish"
        (ExternalOp Fs.fsExt.name "FallocStart" ("fd", ("off", "len"))))
    else if: "mode" =⟨go.uint32⟩ #(W32 1) then
      model.errno (ExternalOp Fs.fsExt.name "FallocKeep" ("fd", ("off", "len")))
    else Panic "syscall.Fallocate: mode not modelled"

/-- `syscall.Flock_t` as goose names it (its `.ty` is in `Code.syscall`, which imports this file). -/
@[reducible] def model.Flock_t : go.GoType := go.GoType.Named go!"syscall.Flock_t" []

/-- `FcntlFlock(fd uintptr, cmd int, lk *Flock_t) error` (`flock_linux.go`):

```go
	_, _, errno := Syscall(fcntl64Syscall, fd, uintptr(cmd), uintptr(unsafe.Pointer(lk)))
	if errno == 0 {
		return nil
	}
	return errno
```

one `fcntl(2)` with the lock description `lk` (`fcntl64Syscall` is `SYS_FCNTL` on amd64). As
`golang.org/x/sys/unix.FcntlFlock`'s model for the commands that set a lock, `F_SETLK` (6),
`F_SETLKW` (7), `F_OFD_SETLK` (37) and `F_OFD_SETLKW` (38): the extension's `OfdLock`, trivial (any
errno; the lock state is not modelled, `notes/osfs-ext-plan.md` D7, `notes/walfs-ext-plan.md`;
the user's decision on lock state is pending, `notes/wal-fsext-plan.md` Q1), stuck on an fd that is
not a file's; `lk` is not read.

`F_OFD_GETLK` (36), the query fileutil's package initializer makes on fd 0 (`lock_linux.go`'s
`init`, to choose OFD locks over `flock`), on any fd, one the process opened or not (fd 0 is
whatever the process inherited: a terminal, `/dev/null`, a pipe, or closed): no extension step (a
query changes no state the model has), and the result is `nil` or any nonzero errno
(`ArbitraryInt`; Linux answers `EBADF` on a closed fd, `EINVAL` for a bad `l_type`, ...). On
success Linux writes the lock description back into `*lk` (`l_type = F_UNLCK` if nothing
conflicts, else the conflicting lock's type, range and `l_pid = -1`), so the model stores arbitrary
values in its fields `Type`, `Whence`, `Start`, `Len` and `Pid` (the padding is left as it is:
measured, `TestOFDGetlkPadding`); on failure `*lk` is unchanged (the errors come before the
copy-out: `EBADF`, `EINVAL`; `EFAULT` needs a bad `lk`, which a Go pointer is not). A nil `lk` is
stuck (Linux: `EFAULT`). Any other command (`F_GETLK`, or one that is not about locks) is not
modelled: a panic, never reached by a proved program. Go example:
`examples/osfs/semantics/model_syscall_fcntlflock.go`. -/
noncomputable def FcntlFlock.impl : val :=
  λ: "fd" "cmd" "lk",
    if: ("cmd" =⟨go.int⟩ #(W64 6)) || ("cmd" =⟨go.int⟩ #(W64 7)) ||
        ("cmd" =⟨go.int⟩ #(W64 37)) || ("cmd" =⟨go.int⟩ #(W64 38)) then
      model.errno (ExternalOp Fs.fsExt.name "OfdLock" ("fd", "cmd"))
    else if: "cmd" =⟨go.int⟩ #(W64 36) then
      let: "e" := ArbitraryInt in
      if: "e" =⟨go.uintptr⟩ #(W64 0) then
        StructFieldRef model.Flock_t go!"Type" "lk" <-[go.int16] Convert go.uint64 go.int16 ArbitraryInt ;;
        StructFieldRef model.Flock_t go!"Whence" "lk" <-[go.int16]
          Convert go.uint64 go.int16 ArbitraryInt ;;
        StructFieldRef model.Flock_t go!"Start" "lk" <-[go.int64] ArbitraryInt ;;
        StructFieldRef model.Flock_t go!"Len" "lk" <-[go.int64] ArbitraryInt ;;
        StructFieldRef model.Flock_t go!"Pid" "lk" <-[go.int32] Convert go.uint64 go.int32 ArbitraryInt ;;
        #GoInterface.nil
      else model.errno "e"
    else Panic "syscall.FcntlFlock: a command that sets no lock, other than F_OFD_GETLK, is not modelled"

/-! ## The initializer's untranslated pieces (2026-11-07, as Perennial's `TrustedCode/syscall.lean`) -/

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
environment. -/
noncomputable def runtime_envs.impl : val :=
  arbitraryStrings

/-- `syscall`'s `init` function (`rlimit.go`):

```go
func init() {
	var lim Rlimit
	if err := Getrlimit(RLIMIT_NOFILE, &lim); err == nil && lim.Max > 0 && lim.Cur < lim.Max-1 {
		origRlimitNofile.Store(&lim)
		nlim := lim
		nlim.Cur = nlim.Max - 1
		adjustFileLimit(&nlim)
		setrlimit(RLIMIT_NOFILE, &nlim)
	}
}
```

It raises the process's soft limit on open files through the raw `prlimit` system call
(`RawSyscall6`, assembly), and records the original limit in `origRlimitNofile`, which only
`Setrlimit` and `exec` (`forkExec`, to restore the child's limit) read. It cannot panic. The model
does nothing: the changed limit and `origRlimitNofile` are observable only through `exec`, a
`Getrlimit` system call (neither modelled) or running out of file descriptors. The model does not
model the limit: the Linux file extension's `Open` (`GooseLang/Ext/Fs/Impl.lean`) may fail with
any errno, `EMFILE` included, whatever the limit. Running out is not only an errno in Go, though:
the first file `os` opens starts the runtime's netpoller, and if its `epoll_create1` or `eventfd`
fails (a hard `ulimit -n` of 4 or 5; measured, `notes/axiom-review/fs-lean-merge/netpoll/`) Go
dies with `fatal error: runtime: netpollinit failed`, after `open(2)` created the file: a run of
the model's (`Open`'s step) that the process ends. A Hoare triple is partial correctness, so a
process that stops after a prefix of a model run contradicts none (as `os.Exit` does not); under
the file extension's restart assumption (`GooseLang/Ext/Fs/Impl.lean`'s header, "Restarts") the
death is a machine crash, which the crash results cover. So it is not a gap. (The
user's decision, Perennial fix-semantics Case 33: "P1: (ii)", 2026-11-04.) -/
def init.«0».impl : val :=
  λ: <>, #()

end code
end syscall

end Perennial
