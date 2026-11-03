/-
Trusted Go model of `syscall` (namespace of the generated package; project bboltfs of
`etc/goose.py`, `Code/syscall.toml`), in terms of the Linux file extension of
`GooseLang.Ext.OsFs.Impl` (`osFsExt`, `ExternalOp osFsExt.name "Fsync"`, ...), for any program
whose extensions include it. linux/amd64.

The functions are `zsyscall_linux_amd64.go`'s system-call stubs: one `Syscall` and
`errnoErr(e1)`, which is `nil` for errno 0 and otherwise `Errno(e1)` boxed as an `error` (some
values from preallocated variables, `errEAGAIN`, ..., which are equal to the boxed `Errno` as
interface values, and so indistinguishable). There is no `EINTR` retry at this level. An errno is
a `w64`, the value of an `Errno` (`uintptr`).
-/
module

public import Perennial.Golang.Defn
public import GooseLang.Ext.OsFs.Impl

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
  λ: "fd", model.errno (ExternalOp osFsExt.name "Fsync" "fd")

/-- `Flock(fd int, how int) error`: `flock(2)`, trivial (`notes/osfs-ext-plan.md`, D7): the
specifications are about one process, which never contends with itself for a lock it holds
through one open file description, so the lock state is not modelled. The result is `nil` or an
arbitrary nonzero `Errno`, the extension's `Flock`: it covers every answer Linux gives, a lock
held elsewhere (`EWOULDBLOCK` with `LOCK_NB`), `EINTR`, `EINVAL` for a bad `how`, `ENOLCK`. It is
stuck on an fd that is not open (D6). A blocking `flock` that never returns is a run the model
need not contain. -/
noncomputable def Flock.impl : val :=
  λ: "fd" "how", model.errno (ExternalOp osFsExt.name "Flock" ("fd", "how"))

end code
end syscall

end Perennial
