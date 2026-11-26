-- The copy for the part `KvRaft/` of `Net/TrustedCode/net.lean` (etc/copy-part.py; rerun it, do not edit).
/-
Trusted code of `net` (namespace of the generated package; project net of `etc/goose.py`,
`Net/Code/net.toml`): the primitive stubs of its Go model (`models/net/model.go`), each one
operation of the net extension `GooseLang.Ext.Net.Impl` (`Net.netExt`), for any program whose
extensions include it; and `errClosed`'s initializer. linux/amd64, Go 1.27.3, the `netgo`
build. The design is
`notes/net-tcp.md` (v3: `notes/net-tcp-v3-plan.md`).

Since the Go-model overlays (S6, 2026-11-24) Go's own code is translated down to the socket: the
types `conn`, `TCPConn`, `TCPListener`, `netFD` and their methods (`ok()`, the `OpError`s Go
builds; `OpError.Error`, `Timeout`, `Temporary`), and the model (Go, translated) replaces only
what is under them: `netFD`'s methods, the
socket options, the listener's `accept`/`close`, `Listen`, `Dial`, `DialTimeout`,
`TCPAddr.String` (`models/net/model.go`'s `MODEL:` comments say why each has every behavior of
Go's). A model `netFD` holds the extension's id of its connection end or listener in Go's own
`pfd.Sysfd`. What is left here has no Go body: the extension's operations (each stub's argument is
the tuple `Impl.lean`'s table names, and its result the operation's), `poll.ErrNetClosing`'s
value (net cannot name its type), and the shared stuck point.

UDP (`notes/net-udp.md`) is `lean`'s trusted UDP, unchanged (etcd-grove#8, coordinator-E's decision
(a), 2026-11-25): the `UDPConn` layout, `UdpFieldAssumptions` and the models of `ListenUDP`,
`WriteToUDP`, `ReadFromUDP` over the UDP extension (`GooseLang.Ext.Udp.Impl`), with the type names
and the two helpers (`model.opError`, `model.einval`) they call; none of it calls the net extension
or the Go model above. A Go model of UDP is etcd-grove#58.
-/
module

public import Perennial.Golang.Defn
public import Perennial.Code.io
public import Perennial.Code.time
public import Perennial.TrustedCode.internal.gomodel
public import Code.os
public import Code.internal.poll
public import GooseLang.Ext.Net.Impl
public import GooseLang.Ext.Udp.Impl

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace net

/-- The model's `UDPConn` (`UDPConn.underlying`): the id of the UDP socket (the UDP extension's,
`GooseLang/Ext/Udp/Impl.lean`), its local address, and its network. -/
structure UDPConn [GooseExts] where
  mk ::
  id' : w64
  laddr' : GoInterface
  net' : GoString

instance UDPConn.zero_val [GooseExts] : ZeroVal UDPConn :=
  ⟨UDPConn.mk zeroValDef zeroValDef zeroValDef⟩


section code
variable [GooseExts] [GoGlobalContext]

/-! The types the UDP models name (as on `lean`, where the old trusted TCP models named them too),
and the two helpers of those models the UDP section calls (`model.opError`, `model.einval`): the
text of `lean`'s `Net/TrustedCode/net.lean`, unchanged. -/

@[reducible] def model.Addr : go.GoType := go.GoType.Named go!"net.Addr" []  -- UDP-only, retired by #58
@[reducible] def model.OpError : go.GoType := go.GoType.Named go!"net.OpError" []  -- UDP-only, retired by #58
@[reducible] def model.IP : go.GoType := go.GoType.Named go!"net.IP" []  -- UDP-only, retired by #58
@[reducible] def model.Errno : go.GoType := go.GoType.Named go!"syscall.Errno" []  -- UDP-only, retired by #58

/-- `UDPConn` (`udpsock.go`: Go's is `struct{ conn }`): the id of the UDP socket, its local address
and its network, in place of the embedded `conn`, whose trusted methods call the TCP extension (the section "UDP"
below). The id field is named `uid`, so that
the layout differs from `conn.underlying`'s and `TCPListener.underlying`'s. -/
@[reducible] def UDPConn.fieldsUnsealed : List go.field_decl :=
  [go.field_decl.FieldDecl go!"uid" go.uint64, go.field_decl.FieldDecl go!"laddr" model.Addr,
    go.field_decl.FieldDecl go!"net" go.string]

/-- The fields, sealed, unfolded by `UDPConn.equals_unfold` in the struct semantics. -/
@[irreducible] def UDPConn.fields : List go.field_decl := UDPConn.fieldsUnsealed

instance UDPConn.equals_unfold : EqualsUnfold UDPConn.fields UDPConn.fieldsUnsealed :=
  ⟨by unfold UDPConn.fields; rfl⟩

@[reducible] def UDPConn.underlying : go.GoType :=
  go.GoType.StructType UDPConn.fields

/-- The struct-field facts of the trusted layout `UDPConn.underlying` (as `FieldAssumptions` for the
TCP layouts; a class of its own, so that the TCP theorems' instance hypotheses are unchanged). Part
of the trust base. -/
class UdpFieldAssumptions [GoLocalContext] [GoSemanticsFunctions] : Prop where
  udp_get_id : ∀ (x : UDPConn), go.IsGoStepPureDetTagged Tag.under
    (StructFieldGet UDPConn.underlying go!"uid") #x (Val #(x.id'))
  udp_set_id : ∀ (x : UDPConn) (y : w64), go.IsGoStepPureDetTagged Tag.under
    (StructFieldSet UDPConn.underlying go!"uid") (PairV #x #y)
    (Val #(({ x with id' := y } : UDPConn)))
  udp_get_laddr : ∀ (x : UDPConn), go.IsGoStepPureDetTagged Tag.under
    (StructFieldGet UDPConn.underlying go!"laddr") #x (Val #(x.laddr'))
  udp_set_laddr : ∀ (x : UDPConn) (y : GoInterface), go.IsGoStepPureDetTagged Tag.under
    (StructFieldSet UDPConn.underlying go!"laddr") (PairV #x #y)
    (Val #(({ x with laddr' := y } : UDPConn)))
  udp_get_net : ∀ (x : UDPConn), go.IsGoStepPureDetTagged Tag.under
    (StructFieldGet UDPConn.underlying go!"net") #x (Val #(x.net'))
  udp_set_net : ∀ (x : UDPConn) (y : GoString), go.IsGoStepPureDetTagged Tag.under
    (StructFieldSet UDPConn.underlying go!"net") (PairV #x #y)
    (Val #(({ x with net' := y } : UDPConn)))

attribute [instance] UdpFieldAssumptions.udp_get_id UdpFieldAssumptions.udp_set_id
  UdpFieldAssumptions.udp_get_laddr UdpFieldAssumptions.udp_set_laddr
  UdpFieldAssumptions.udp_get_net UdpFieldAssumptions.udp_set_net

/-- `&OpError{Op: op, Net: nw, Source: src, Addr: addr, Err: err}` as an `error` (D23: `nw` the
call's, connection's or listener's network). -/
noncomputable def model.opError : val :=  -- UDP-only, retired by #58
  λ: "op" "nw" "src" "addr" "err",
    let: "pe" := GoAlloc model.OpError (GoZeroVal model.OpError #()) in
    StructFieldRef model.OpError go!"Op" "pe" <-[go.string] "op" ;;
    StructFieldRef model.OpError go!"Net" "pe" <-[go.string] "nw" ;;
    StructFieldRef model.OpError go!"Source" "pe" <-[model.Addr] "src" ;;
    StructFieldRef model.OpError go!"Addr" "pe" <-[model.Addr] "addr" ;;
    StructFieldRef model.OpError go!"Err" "pe" <-[go.error] "err" ;;
    Convert (go.PointerType model.OpError) go.error "pe"

/-- `syscall.EINVAL` (`Errno(0x16)`, `zerrors_linux_amd64.go`) as an `error`, bare: what Go's
methods return for a zero-value `TCPConn` or `TCPListener` (`return syscall.EINVAL` when `c.ok()`
or `l.ok()` fails: `net.go`, `tcpsock.go`; `TestZeroValues`). -/
noncomputable def model.einval : val :=  -- UDP-only, retired by #58
  λ: <>, Convert model.Errno go.error #(W64 22)

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

/-- `netClosingErr()`: `poll.ErrNetClosing` as an `error`. Its value is `errNetClosing{}`, the only
value of an empty struct (Go reads `poll.ErrNetClosing`; net cannot name `errNetClosing`). -/
noncomputable def netClosingErr.impl : val :=
  λ: <>, Convert internal.poll.errNetClosing.ty go.error
    (GoZeroVal internal.poll.errNetClosing.ty #())

/-- `stuck()`: no behavior, the shared stuck point (`internal.gomodel.Stuck.impl`), where the
model does not model Go (a network but `"tcp"` and `"tcp4"`, D23). -/
noncomputable def stuck.impl : val := internal.gomodel.Stuck.impl

/-! ## UDP (the UDP extension, `GooseLang/Ext/Udp/Impl.lean`, `notes/net-udp.md`)

Go's `UDPConn` embeds the same `conn` as `TCPConn`; here it has a layout of its own (`UDPConn.
underlying`: `uid`, the UDP extension's socket id; `laddr`; `net`), and its own models of the
methods a program over UDP calls: `ListenUDP`, `WriteToUDP`, `ReadFromUDP`. Its other methods have
no model, so a program calling one is stuck (U12): `ReadFrom`, `WriteTo`, `ReadMsgUDP`, ...; and
`conn`'s methods, promoted to `*UDPConn` (`Close`, `Read`, `Write`, the deadlines, `LocalAddr`,
...): the translation emits no unfold of them for this trusted type (`UDPConn.TypeAssumptions` has
only `ptr_ReadFromUDP_unfold` and `ptr_WriteToUDP_unfold`), so a call of one has no step: an
unprovable path, never TCP's model acting on a UDP socket (`notes/net-udp.md`). A program over UDP keeps its socket until its process ends (U7: the kernel
closes it). Only the network `"udp4"` is modeled (an IPv4 socket, `AF_INET`: Go's
`favoriteAddrFamily` for `"udp4"`); any other panics. Errors (U9) are Go's `*OpError`s, `Net` the
socket's network, `Err` an `*os.SyscallError` with an arbitrary nonzero `Errno` for `sys` (`model.udpSysErr`, the extension's
own `"AnyErrno"`, so that a program over UDP alone needs no TCP extension). -/

@[reducible] def model.UDPConn : go.GoType := go.GoType.Named go!"net.UDPConn" []
@[reducible] def model.UDPAddr : go.GoType := go.GoType.Named go!"net.UDPAddr" []

/-- `&os.SyscallError{Syscall: name, Err: syscall.Errno(n)}` as an `error`, `n` arbitrary and
nonzero (the UDP extension's `"AnyErrno"`). -/
noncomputable def model.udpSysErr : val :=
  λ: "name",
    let: "n" := ExternalOp Udp.udpExt.name "AnyErrno" #() in
    let: "p" := GoAlloc os.SyscallError.ty (GoZeroVal os.SyscallError.ty #()) in
    StructFieldRef os.SyscallError.ty go!"Syscall" "p" <-[go.string] "name" ;;
    StructFieldRef os.SyscallError.ty go!"Err" "p" <-[go.error] Convert model.Errno go.error "n" ;;
    Convert (go.PointerType os.SyscallError.ty) go.error "p"

/-- The `Err` of a UDP failure: the UDP extension's only failure is `sys` (`Net.NetErr.code` 3),
`name` the system call's. -/
noncomputable def model.udpKindErr : val :=
  λ: "code" "name", model.udpSysErr "name"

/-- A new `*UDPAddr` with arbitrary fields. -/
noncomputable def model.anyUDPAddr : val :=
  λ: <>,
    let: "p" := GoAlloc model.UDPAddr (GoZeroVal model.UDPAddr #()) in
    StructFieldRef model.UDPAddr go!"IP" "p" <-[model.IP]
      Convert go.string (go.GoType.SliceType go.byte) (ExternalOp Udp.udpExt.name "AnyString" #()) ;;
    StructFieldRef model.UDPAddr go!"Port" "p" <-[go.int] ExternalOp Udp.udpExt.name "AnyW64" #() ;;
    StructFieldRef model.UDPAddr go!"Zone" "p" <-[go.string]
      ExternalOp Udp.udpExt.name "AnyString" #() ;;
    "p"

/-- The `IP` (as bytes) and `Port` of the `*UDPAddr` `a`, the argument the UDP extension's
`"Listen"` and `"Send"` take (it turns them into the address, U1). -/
noncomputable def model.udpDest : val :=
  λ: "a",
    (Convert (go.GoType.SliceType go.byte) go.string
      (![model.IP] (StructFieldRef model.UDPAddr go!"IP" "a")),
     ![go.int] (StructFieldRef model.UDPAddr go!"Port" "a"))

/-- The socket id of a `*UDPConn`. -/
noncomputable def model.udpId : val :=
  λ: "c", ![go.uint64] (StructFieldRef model.UDPConn go!"uid" "c")

/-- The `*OpError` of the operation `op` on the `*UDPConn` `c` (its network; `Source` its
`laddr`, `Addr` the given one), for a failure of code `code`, `name` the system call's. -/
noncomputable def model.udpErr : val :=
  λ: "op" "c" "addr" "code" "name",
    model.opError "op" (![go.string] (StructFieldRef model.UDPConn go!"net" "c"))
      (![model.Addr] (StructFieldRef model.UDPConn go!"laddr" "c")) "addr"
      (model.udpKindErr "code" "name")

/-- U1. `ListenUDP(network string, laddr *UDPAddr) (*UDPConn, error)` (`udpsock.go`,
`udpsock_posix.go`'s `listenUDP`, `sock_posix.go`'s `socket`): for `"udp4"`, `socket(2)`
(`AF_INET`, `SOCK_DGRAM`) and `bind(2)` to `laddr`: the extension's `"Listen"` of `laddr`'s `IP` and
`Port` (a panic unless they make a valid address, U1). A `*UDPConn` with the socket's id, a new
local address and the network; an error is `&OpError{Op: "listen", Net: network, Source: nil,
Addr: laddr, Err: e}` with a nil `*UDPConn`, `e` the system call's error (an `*os.SyscallError`, the
failing call's name arbitrary: `"socket"`, `"setsockopt"`, `"bind"`), or a bare nonzero
`syscall.Errno`: `listenDatagram` returns `fd.init()`'s error unwrapped (`sock_posix.go`), the
`ENOMEM`/`ENOSPC` of registering the socket with epoll. A `nil` `laddr` (Go: a wildcard address with a
port the kernel picks) and any network but `"udp4"`: a panic of the model (not modeled, U12). -/
noncomputable def ListenUDP.impl : val :=
  λ: "network" "laddr",
    if: "network" =⟨go.string⟩ #(go!"udp4") then
      if: "laddr" =⟨go.PointerType model.UDPAddr⟩ #null then
        Panic "net: ListenUDP of a nil address not modelled"
      else
      let: "r" := ExternalOp Udp.udpExt.name "Listen" (model.udpDest "laddr") in
      if: Snd "r" =⟨go.uint64⟩ #(W64 0) then
        let: "c" := GoAlloc model.UDPConn (GoZeroVal model.UDPConn #()) in
        StructFieldRef model.UDPConn go!"uid" "c" <-[go.uint64] Fst "r" ;;
        StructFieldRef model.UDPConn go!"laddr" "c" <-[model.Addr]
          Convert (go.PointerType model.UDPAddr) model.Addr (model.anyUDPAddr #()) ;;
        StructFieldRef model.UDPConn go!"net" "c" <-[go.string] "network" ;;
        ("c", #GoInterface.nil)
      else (#(null : Loc), model.opError #(go!"listen") "network" #GoInterface.nil
        (Convert (go.PointerType model.UDPAddr) model.Addr "laddr")
        (if: ExternalOp Udp.udpExt.name "AnyBool" #() then
          Convert model.Errno go.error (ExternalOp Udp.udpExt.name "AnyErrno" #())
        else model.udpKindErr (Snd "r") (ExternalOp Udp.udpExt.name "AnyString" #())))
    else Panic "net: ListenUDP of a network but udp4 not modelled"

/-- U2, U3. `(*UDPConn).WriteToUDP(b []byte, addr *UDPAddr) (int, error)` (`udpsock.go`,
`udpsock_posix.go`'s `writeTo`, `poll.FD.WriteToInet4`): one `sendto(2)` of `b` to `addr`, waiting
while the socket's buffer is full: the extension's `"Send"` (a panic unless `addr`'s `IP` and
`Port` make a valid address, U1). `(len(b), nil)`; or `(0, &OpError{Op: "write", Net, Source:
laddr, Addr: addr, Err})`, `Err` the kind's (`"sendto"` for a system call's). A zero `UDPConn`:
`0`, `syscall.EINVAL`, as Go's `c.ok()`. A `nil` `addr` (Go: `errMissingAddress`): a panic of the
model (not modeled). -/
noncomputable def UDPConn.WriteToUDP.impl : val :=
  λ: "c" "b" "addr",
    if: model.udpId "c" =⟨go.uint64⟩ #(W64 0) then (#(W64 0), model.einval #()) else
    if: "addr" =⟨go.PointerType model.UDPAddr⟩ #null then
      Panic "net: WriteToUDP to a nil address not modelled"
    else
    let: "r" := ExternalOp Udp.udpExt.name "Send" (model.udpId "c",
      (Convert (go.GoType.SliceType go.byte) go.string "b", model.udpDest "addr")) in
    if: "r" =⟨go.uint64⟩ #(W64 0) then
      ((FuncResolve go.len [go.GoType.SliceType go.byte]) #() "b", #GoInterface.nil)
    else (#(W64 0), model.udpErr #(go!"write") "c"
      (Convert (go.PointerType model.UDPAddr) model.Addr "addr") "r" #(go!"sendto"))

/-- U4. `(*UDPConn).ReadFromUDP(b []byte) (int, *UDPAddr, error)` (`udpsock.go`'s
`readFromUDP`, `udpsock_posix.go`'s `readFrom`, `poll.FD.ReadFromInet4`): one `recvfrom(2)`,
waiting for a datagram: the extension's `"Recv"` of `len(b)`, the bytes copied into `b`. `(n,
addr, nil)` with `addr` a new `*UDPAddr` (the sender's in Go; arbitrary here, U10); or `(0, nil,
&OpError{Op: "read", Net, Source: laddr, Addr: nil, Err})`, the `*UDPAddr` nil (Go's `readFrom`
sets `addr = nil` on an error, `udpsock_posix.go`), `Err` the kind's (`"recvfrom"` for a system call's). A zero `UDPConn`:
`0`, `nil`, `syscall.EINVAL`. -/
noncomputable def UDPConn.ReadFromUDP.impl : val :=
  λ: "c" "b",
    if: model.udpId "c" =⟨go.uint64⟩ #(W64 0) then
      (#(W64 0), #(null : Loc), model.einval #()) else
    let: "r" := ExternalOp Udp.udpExt.name "Recv"
      (model.udpId "c", (FuncResolve go.len [go.GoType.SliceType go.byte]) #() "b") in
    if: Snd "r" =⟨go.uint64⟩ #(W64 0) then
      ((FuncResolve go.copy [go.GoType.SliceType go.byte]) #() "b"
        (Convert go.string (go.GoType.SliceType go.byte) (Fst "r")), model.anyUDPAddr #(),
        #GoInterface.nil)
    else (#(W64 0), #(null : Loc),
      model.udpErr #(go!"read") "c" #GoInterface.nil (Snd "r") #(go!"recvfrom"))

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
