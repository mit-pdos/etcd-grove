/-
Trusted code of `net` (namespace of the generated package; project net of `etc/goose.py`,
`Net/Code/net.toml`): the primitive stubs of its Go model (`models/net/model.go`), each one
operation of the net extension `GooseLang.Ext.Net.Impl` (`Net.netExt`), for any program whose
extensions include it; `errClosed`'s initializer; and, for now, the models of `OpError.Error`,
`Timeout` and `Temporary`. linux/amd64, Go 1.27.3, the `netgo` build. The design is
`notes/net-tcp.md` (v3: `notes/net-tcp-v3-plan.md`).

Since the Go-model overlays (S6, 2026-11-24) Go's own code is translated down to the socket: the
types `conn`, `TCPConn`, `TCPListener`, `netFD` and their methods (`ok()`, the `OpError`s Go
builds), and the model (Go, translated) replaces only what is under them: `netFD`'s methods, the
socket options, the listener's `accept`/`close`, `Listen`, `Dial`, `DialTimeout`,
`TCPAddr.String` (`models/net/model.go`'s `MODEL:` comments say why each has every behavior of
Go's). A model `netFD` holds the extension's id of its connection end or listener in Go's own
`pfd.Sysfd`. What is left here has no Go body: the extension's operations (each stub's argument is
the tuple `Impl.lean`'s table names, and its result the operation's), `poll.ErrNetClosing`'s
value (net cannot name its type), and the shared stuck point.
-/
module

public import Perennial.Golang.Defn
public import Perennial.Code.io
public import Perennial.Code.time
public import Perennial.TrustedCode.internal.gomodel
public import Code.os
public import Code.internal.poll
public import GooseLang.Ext.Net.Impl

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace net

section code
variable [GooseExts] [GoGlobalContext]

/-! ## The primitive stubs (`models/net/model.go`) -/

/-- `extListen(address)`: the extension's `Listen` (D6): the listener's id and the code. -/
noncomputable def extListen.impl : val :=
  λ: "address", ExternalOp Net.netExt.name "Listen" "address"

/-- `extDial(address)`: the extension's `Dial` (D8, D16): the end's id and the code. -/
noncomputable def extDial.impl : val :=
  λ: "address", ExternalOp Net.netExt.name "Dial" "address"

/-- `extAccept(id)`: the extension's `Accept` on the listener `id` (D7). -/
noncomputable def extAccept.impl : val :=
  λ: "id", ExternalOp Net.netExt.name "Accept" "id"

/-- `extRead(id, n)`: the extension's `Read` of `n` bytes at the end `id` (D1): the bytes and the
code (`4` EOF). -/
noncomputable def extRead.impl : val :=
  λ: "id" "n", ExternalOp Net.netExt.name "Read" ("id", "n")

/-- `extWrite(id, bs, first)`: one step of the extension's `Write` of `bs` at the end `id` (D2,
D25: `first` says whether it is the call's first step): the count and the code. -/
noncomputable def extWrite.impl : val :=
  λ: "id" "bs" "first", ExternalOp Net.netExt.name "Write" ("id", ("bs", "first"))

/-- `extClose(id)`: the extension's `Close` of the end `id` (D3). -/
noncomputable def extClose.impl : val :=
  λ: "id", ExternalOp Net.netExt.name "Close" "id"

/-- `extLisClose(id)`: the extension's `LisClose` of the listener `id` (D9). -/
noncomputable def extLisClose.impl : val :=
  λ: "id", ExternalOp Net.netExt.name "LisClose" "id"

/-- `extCloseWrite(id)`: the extension's `CloseWrite` of the end `id` (D4). -/
noncomputable def extCloseWrite.impl : val :=
  λ: "id", ExternalOp Net.netExt.name "CloseWrite" "id"

/-- `extSetDeadline(id, kind, t)`: the extension's `SetDeadline` of the deadlines of kind `kind`
(`0` both, `1` read, `2` write) of the end `id` to the time `t` (D5): `t`'s two words (`wall`,
`ext`, which net cannot read: `time`'s unexported fields; the extension decides whether it is Go's
zero time, `Net.timeIsZero`), read through a copy of `t` (a cell the program never sees). -/
noncomputable def extSetDeadline.impl : val :=
  λ: "id" "kind" "t",
    let: "tp" := GoAlloc time.Time.ty "t" in
    ExternalOp Net.netExt.name "SetDeadline"
      ("id", ("kind", (![go.uint64] (StructFieldRef time.Time.ty go!"wall" "tp"),
        ![go.int64] (StructFieldRef time.Time.ty go!"ext" "tp"))))

/-- `extSetSockopt(id, kind, x)`: the extension's `SetSockopt` of the option kind `kind` (`1`
`TCP_KEEPIDLE` of the duration `x`, `0` the others) at the end `id` (D24). -/
noncomputable def extSetSockopt.impl : val :=
  λ: "id" "kind" "x", ExternalOp Net.netExt.name "SetSockopt" ("id", ("kind", "x"))

/-- `extAnyString()`: an arbitrary string (the extension's `AnyString`). -/
noncomputable def extAnyString.impl : val :=
  λ: <>, ExternalOp Net.netExt.name "AnyString" #()

/-- `extAnyW64()`: an arbitrary word (the extension's `AnyW64`). -/
noncomputable def extAnyW64.impl : val :=
  λ: <>, ExternalOp Net.netExt.name "AnyW64" #()

/-- `extAnyBool()`: an arbitrary boolean (the extension's `AnyBool`). -/
noncomputable def extAnyBool.impl : val :=
  λ: <>, ExternalOp Net.netExt.name "AnyBool" #()

/-- `extAnyErrno()`: an arbitrary nonzero `syscall.Errno` (the extension's `AnyErrno`). -/
noncomputable def extAnyErrno.impl : val :=
  λ: <>, ExternalOp Net.netExt.name "AnyErrno" #()

/-- `closedErr()`: `poll.ErrNetClosing` as an `error`. Its value is `errNetClosing{}`, the only
value of an empty struct (Go reads `poll.ErrNetClosing`; net cannot name `errNetClosing`). -/
noncomputable def closedErr.impl : val :=
  λ: <>, Convert internal.poll.errNetClosing.ty go.error
    (GoZeroVal internal.poll.errNetClosing.ty #())

/-- `stuck()`: no behavior, the shared stuck point (`internal.gomodel.Stuck.impl`), where the
model does not model Go (a network but `"tcp"` and `"tcp4"`, D23). -/
noncomputable def stuck.impl : val := internal.gomodel.Stuck.impl

/-! ## `OpError`'s methods (Lean models, for now) -/

@[reducible] def model.OpError : go.GoType := go.GoType.Named go!"net.OpError" []
@[reducible] def model.timeoutError : go.GoType := go.GoType.Named go!"net.timeoutError" []

/-- `(*OpError).Error() string` (`net.go`): Go's message is `e.Op`, then the network and the
addresses (each after a space or `"->"`), then `": "` and `e.Err`'s message; the model does not
explain the network's, the addresses' and the system error's parts: `e.Op ++ s1 ++ ": " ++ s2`
for arbitrary strings `s1`, `s2` (Go's form, which `TestErrorsAreOpErrors` checks: it starts with
the operation and holds `": "`; so never empty). `"<nil>"` for a `nil` receiver, as Go's.
TRUSTED CHANGE (net-rpc-errors, for review): before, an arbitrary non-empty string. A program may
rely on the form: net/rpc's server answers a request whose body read fails with an error response
of that message (`"read …: …"`), which a service's own error messages can then be told from
(`net.rpc.srvErrMsg`). -/
noncomputable def OpError.Error.impl : val :=
  λ: "e" <>,
    if: "e" =⟨go.PointerType model.OpError⟩ #null then #(go!"<nil>") else
    let: "s1" := ExternalOp Net.netExt.name "AnyString" #() in
    let: "s2" := ExternalOp Net.netExt.name "AnyString" #() in
    ![go.string] (StructFieldRef model.OpError go!"Op" "e") +⟨go.string⟩ "s1" +⟨go.string⟩
      #(go!": ") +⟨go.string⟩ "s2"

/-- `true` for an `Err` of the dynamic type `*poll.DeadlineExceededError` or `*timeoutError`,
`false` for `poll.errNetClosing` (their `Timeout` and `Temporary` methods, constants: `fd.go`,
`net.go`), arbitrary otherwise (an `*os.SyscallError` answers its `Errno`'s, which the model does
not explain; any other `Err` a program stored answers its own methods). -/
noncomputable def model.errFlag : val :=
  λ: "e",
    let: "err" := ![go.error] (StructFieldRef model.OpError go!"Err" "e") in
    if: Snd (TypeAssert2 internal.poll.errNetClosing.ty "err") then #false
    else if: Snd (TypeAssert2 (go.PointerType internal.poll.DeadlineExceededError.ty) "err") then
      #true
    else if: Snd (TypeAssert2 (go.PointerType model.timeoutError) "err") then #true
    else ExternalOp Net.netExt.name "AnyBool" #()

/-- `(*OpError).Timeout() bool` (`net.go`): `e.Err`'s `Timeout()`, through an `*os.SyscallError`
to its `Err` (`model.errFlag`). -/
noncomputable def OpError.Timeout.impl : val :=
  λ: "e" <>, model.errFlag "e"

/-- `(*OpError).Temporary() bool` (`net.go`): `e.Err`'s `Temporary()` (and `true` for an accept's
`ECONNRESET`, `ECONNABORTED`), as `Timeout` (`model.errFlag`). -/
noncomputable def OpError.Temporary.impl : val :=
  λ: "e" <>, model.errFlag "e"


/-! ## The package variables

`errClosed` (`net.go`: `errClosed = poll.ErrNetClosing`) holds that value (an empty struct's only
value, so no read of `poll`'s variable is needed); the translated `ErrClosed` (`ErrClosed error =
errClosed`) and `errTimeout` (`&timeoutError{}`) read and build theirs. The other variables are
skipped (`Net/Code/net.toml`, `[[skip]]`). -/

/-- `errClosed = poll.ErrNetClosing` (of type `poll.errNetClosing`). -/
noncomputable def errClosed.init : val :=
  λ: <>,
    go.GlobalAlloc go!"net.errClosed" internal.poll.errNetClosing.ty #() ;;
    GlobalVarAddr go!"net.errClosed" #() <-[internal.poll.errNetClosing.ty]
      GoZeroVal internal.poll.errNetClosing.ty #()


end code

end net

end Perennial
