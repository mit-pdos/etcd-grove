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

<<<<<<< ours
||||||| base
/-- The model's `conn` (`conn.underlying`): the id of the connection end, its addresses, and its
network (D23). -/
structure conn [GooseExts] where
  mk ::
  id' : w64
  laddr' : GoInterface
  raddr' : GoInterface
  net' : GoString

instance conn.zero_val [GooseExts] : ZeroVal conn :=
  ⟨conn.mk zeroValDef zeroValDef zeroValDef zeroValDef⟩

/-- `TCPConn` (`struct{ conn }`, as Go's). -/
structure TCPConn [GooseExts] where
  mk ::
  conn' : conn

instance TCPConn.zero_val [GooseExts] : ZeroVal TCPConn := ⟨TCPConn.mk zeroValDef⟩

/-- The model's `TCPListener` (`TCPListener.underlying`): the id of the listener, its address, and
its network (D23). -/
structure TCPListener [GooseExts] where
  mk ::
  id' : w64
  addr' : GoInterface
  net' : GoString

instance TCPListener.zero_val [GooseExts] : ZeroVal TCPListener :=
  ⟨TCPListener.mk zeroValDef zeroValDef zeroValDef⟩

=======
/-- The model's `conn` (`conn.underlying`): the id of the connection end, its addresses, and its
network (D23). -/
structure conn [GooseExts] where
  mk ::
  id' : w64
  laddr' : GoInterface
  raddr' : GoInterface
  net' : GoString

instance conn.zero_val [GooseExts] : ZeroVal conn :=
  ⟨conn.mk zeroValDef zeroValDef zeroValDef zeroValDef⟩

/-- `TCPConn` (`struct{ conn }`, as Go's). -/
structure TCPConn [GooseExts] where
  mk ::
  conn' : conn

instance TCPConn.zero_val [GooseExts] : ZeroVal TCPConn := ⟨TCPConn.mk zeroValDef⟩

/-- The model's `TCPListener` (`TCPListener.underlying`): the id of the listener, its address, and
its network (D23). -/
structure TCPListener [GooseExts] where
  mk ::
  id' : w64
  addr' : GoInterface
  net' : GoString

instance TCPListener.zero_val [GooseExts] : ZeroVal TCPListener :=
  ⟨TCPListener.mk zeroValDef zeroValDef zeroValDef⟩

/-- The model's `UDPConn` (`UDPConn.underlying`): the id of the UDP socket (the UDP extension's,
`GooseLang/Ext/Udp/Impl.lean`), its local address, and its network. -/
structure UDPConn [GooseExts] where
  mk ::
  id' : w64
  laddr' : GoInterface
  net' : GoString

instance UDPConn.zero_val [GooseExts] : ZeroVal UDPConn :=
  ⟨UDPConn.mk zeroValDef zeroValDef zeroValDef⟩

>>>>>>> theirs
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

<<<<<<< ours
/-- `extLisClose(id)`: the extension's `LisClose` of the listener `id` (D9). -/
noncomputable def extLisClose.impl : val :=
  λ: "id", ExternalOp Net.netExt.name "LisClose" "id"
||||||| base
/-- The struct-field facts goose emits for every translated struct, stated by hand for the trusted
layouts `conn.underlying`, `TCPConn.underlying` and `TCPListener.underlying`, of which goose emits
none (as `os.file.FieldAssumptions`). Specs that need them take them as an instance hypothesis.
Part of the trust base. -/
class FieldAssumptions [GoLocalContext] [GoSemanticsFunctions] : Prop where
  conn_get_id : ∀ (x : conn), go.IsGoStepPureDetTagged Tag.under
    (StructFieldGet conn.underlying go!"id") #x (Val #(x.id'))
  conn_set_id : ∀ (x : conn) (y : w64), go.IsGoStepPureDetTagged Tag.under
    (StructFieldSet conn.underlying go!"id") (PairV #x #y) (Val #(({ x with id' := y } : conn)))
  conn_get_laddr : ∀ (x : conn), go.IsGoStepPureDetTagged Tag.under
    (StructFieldGet conn.underlying go!"laddr") #x (Val #(x.laddr'))
  conn_set_laddr : ∀ (x : conn) (y : GoInterface), go.IsGoStepPureDetTagged Tag.under
    (StructFieldSet conn.underlying go!"laddr") (PairV #x #y)
    (Val #(({ x with laddr' := y } : conn)))
  conn_get_raddr : ∀ (x : conn), go.IsGoStepPureDetTagged Tag.under
    (StructFieldGet conn.underlying go!"raddr") #x (Val #(x.raddr'))
  conn_set_raddr : ∀ (x : conn) (y : GoInterface), go.IsGoStepPureDetTagged Tag.under
    (StructFieldSet conn.underlying go!"raddr") (PairV #x #y)
    (Val #(({ x with raddr' := y } : conn)))
  conn_get_net : ∀ (x : conn), go.IsGoStepPureDetTagged Tag.under
    (StructFieldGet conn.underlying go!"net") #x (Val #(x.net'))
  conn_set_net : ∀ (x : conn) (y : GoString), go.IsGoStepPureDetTagged Tag.under
    (StructFieldSet conn.underlying go!"net") (PairV #x #y)
    (Val #(({ x with net' := y } : conn)))
  net_get_conn : ∀ (x : TCPConn), go.IsGoStepPureDetTagged Tag.under
    (StructFieldGet TCPConn.underlying go!"conn") #x (Val #(x.conn'))
  net_set_conn : ∀ (x : TCPConn) (y : conn), go.IsGoStepPureDetTagged Tag.under
    (StructFieldSet TCPConn.underlying go!"conn") (PairV #x #y)
    (Val #(({ x with conn' := y } : TCPConn)))
  lis_get_id : ∀ (x : TCPListener), go.IsGoStepPureDetTagged Tag.under
    (StructFieldGet TCPListener.underlying go!"lid") #x (Val #(x.id'))
  lis_set_id : ∀ (x : TCPListener) (y : w64), go.IsGoStepPureDetTagged Tag.under
    (StructFieldSet TCPListener.underlying go!"lid") (PairV #x #y)
    (Val #(({ x with id' := y } : TCPListener)))
  lis_get_addr : ∀ (x : TCPListener), go.IsGoStepPureDetTagged Tag.under
    (StructFieldGet TCPListener.underlying go!"addr") #x (Val #(x.addr'))
  lis_set_addr : ∀ (x : TCPListener) (y : GoInterface), go.IsGoStepPureDetTagged Tag.under
    (StructFieldSet TCPListener.underlying go!"addr") (PairV #x #y)
    (Val #(({ x with addr' := y } : TCPListener)))
  lis_get_net : ∀ (x : TCPListener), go.IsGoStepPureDetTagged Tag.under
    (StructFieldGet TCPListener.underlying go!"net") #x (Val #(x.net'))
  lis_set_net : ∀ (x : TCPListener) (y : GoString), go.IsGoStepPureDetTagged Tag.under
    (StructFieldSet TCPListener.underlying go!"net") (PairV #x #y)
    (Val #(({ x with net' := y } : TCPListener)))
=======
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

/-- The struct-field facts goose emits for every translated struct, stated by hand for the trusted
layouts `conn.underlying`, `TCPConn.underlying` and `TCPListener.underlying`, of which goose emits
none (as `os.file.FieldAssumptions`). Specs that need them take them as an instance hypothesis.
Part of the trust base. -/
class FieldAssumptions [GoLocalContext] [GoSemanticsFunctions] : Prop where
  conn_get_id : ∀ (x : conn), go.IsGoStepPureDetTagged Tag.under
    (StructFieldGet conn.underlying go!"id") #x (Val #(x.id'))
  conn_set_id : ∀ (x : conn) (y : w64), go.IsGoStepPureDetTagged Tag.under
    (StructFieldSet conn.underlying go!"id") (PairV #x #y) (Val #(({ x with id' := y } : conn)))
  conn_get_laddr : ∀ (x : conn), go.IsGoStepPureDetTagged Tag.under
    (StructFieldGet conn.underlying go!"laddr") #x (Val #(x.laddr'))
  conn_set_laddr : ∀ (x : conn) (y : GoInterface), go.IsGoStepPureDetTagged Tag.under
    (StructFieldSet conn.underlying go!"laddr") (PairV #x #y)
    (Val #(({ x with laddr' := y } : conn)))
  conn_get_raddr : ∀ (x : conn), go.IsGoStepPureDetTagged Tag.under
    (StructFieldGet conn.underlying go!"raddr") #x (Val #(x.raddr'))
  conn_set_raddr : ∀ (x : conn) (y : GoInterface), go.IsGoStepPureDetTagged Tag.under
    (StructFieldSet conn.underlying go!"raddr") (PairV #x #y)
    (Val #(({ x with raddr' := y } : conn)))
  conn_get_net : ∀ (x : conn), go.IsGoStepPureDetTagged Tag.under
    (StructFieldGet conn.underlying go!"net") #x (Val #(x.net'))
  conn_set_net : ∀ (x : conn) (y : GoString), go.IsGoStepPureDetTagged Tag.under
    (StructFieldSet conn.underlying go!"net") (PairV #x #y)
    (Val #(({ x with net' := y } : conn)))
  net_get_conn : ∀ (x : TCPConn), go.IsGoStepPureDetTagged Tag.under
    (StructFieldGet TCPConn.underlying go!"conn") #x (Val #(x.conn'))
  net_set_conn : ∀ (x : TCPConn) (y : conn), go.IsGoStepPureDetTagged Tag.under
    (StructFieldSet TCPConn.underlying go!"conn") (PairV #x #y)
    (Val #(({ x with conn' := y } : TCPConn)))
  lis_get_id : ∀ (x : TCPListener), go.IsGoStepPureDetTagged Tag.under
    (StructFieldGet TCPListener.underlying go!"lid") #x (Val #(x.id'))
  lis_set_id : ∀ (x : TCPListener) (y : w64), go.IsGoStepPureDetTagged Tag.under
    (StructFieldSet TCPListener.underlying go!"lid") (PairV #x #y)
    (Val #(({ x with id' := y } : TCPListener)))
  lis_get_addr : ∀ (x : TCPListener), go.IsGoStepPureDetTagged Tag.under
    (StructFieldGet TCPListener.underlying go!"addr") #x (Val #(x.addr'))
  lis_set_addr : ∀ (x : TCPListener) (y : GoInterface), go.IsGoStepPureDetTagged Tag.under
    (StructFieldSet TCPListener.underlying go!"addr") (PairV #x #y)
    (Val #(({ x with addr' := y } : TCPListener)))
  lis_get_net : ∀ (x : TCPListener), go.IsGoStepPureDetTagged Tag.under
    (StructFieldGet TCPListener.underlying go!"net") #x (Val #(x.net'))
  lis_set_net : ∀ (x : TCPListener) (y : GoString), go.IsGoStepPureDetTagged Tag.under
    (StructFieldSet TCPListener.underlying go!"net") (PairV #x #y)
    (Val #(({ x with net' := y } : TCPListener)))
>>>>>>> theirs

/-- `extCloseWrite(id)`: the extension's `CloseWrite` of the end `id` (D4). -/
noncomputable def extCloseWrite.impl : val :=
  λ: "id", ExternalOp Net.netExt.name "CloseWrite" "id"

<<<<<<< ours
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
||||||| base
/-! The types as goose names them (their `.ty` is in `Code.net`, which imports this file), and
helpers of the models (not Go functions). -/

@[reducible] def model.conn : go.GoType := go.GoType.Named go!"net.conn" []
@[reducible] def model.TCPConn : go.GoType := go.GoType.Named go!"net.TCPConn" []
@[reducible] def model.TCPListener : go.GoType := go.GoType.Named go!"net.TCPListener" []
@[reducible] def model.OpError : go.GoType := go.GoType.Named go!"net.OpError" []
@[reducible] def model.Conn : go.GoType := go.GoType.Named go!"net.Conn" []
@[reducible] def model.Listener : go.GoType := go.GoType.Named go!"net.Listener" []
@[reducible] def model.TCPAddr : go.GoType := go.GoType.Named go!"net.TCPAddr" []
@[reducible] def model.IP : go.GoType := go.GoType.Named go!"net.IP" []
@[reducible] def model.timeoutError : go.GoType := go.GoType.Named go!"net.timeoutError" []
@[reducible] def model.Errno : go.GoType := go.GoType.Named go!"syscall.Errno" []

/-- `&OpError{Op: op, Net: nw, Source: src, Addr: addr, Err: err}` as an `error` (D23: `nw` the
call's, connection's or listener's network). -/
noncomputable def model.opError : val :=
  λ: "op" "nw" "src" "addr" "err",
    let: "pe" := GoAlloc model.OpError (GoZeroVal model.OpError #()) in
    StructFieldRef model.OpError go!"Op" "pe" <-[go.string] "op" ;;
    StructFieldRef model.OpError go!"Net" "pe" <-[go.string] "nw" ;;
    StructFieldRef model.OpError go!"Source" "pe" <-[model.Addr] "src" ;;
    StructFieldRef model.OpError go!"Addr" "pe" <-[model.Addr] "addr" ;;
    StructFieldRef model.OpError go!"Err" "pe" <-[go.error] "err" ;;
    Convert (go.PointerType model.OpError) go.error "pe"

/-- `poll.ErrNetClosing` as an `error`: `errNetClosing{}`, the only value of an empty struct. -/
noncomputable def model.closedErr : val :=
=======
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

/-! The types as goose names them (their `.ty` is in `Code.net`, which imports this file), and
helpers of the models (not Go functions). -/

@[reducible] def model.conn : go.GoType := go.GoType.Named go!"net.conn" []
@[reducible] def model.TCPConn : go.GoType := go.GoType.Named go!"net.TCPConn" []
@[reducible] def model.TCPListener : go.GoType := go.GoType.Named go!"net.TCPListener" []
@[reducible] def model.OpError : go.GoType := go.GoType.Named go!"net.OpError" []
@[reducible] def model.Conn : go.GoType := go.GoType.Named go!"net.Conn" []
@[reducible] def model.Listener : go.GoType := go.GoType.Named go!"net.Listener" []
@[reducible] def model.TCPAddr : go.GoType := go.GoType.Named go!"net.TCPAddr" []
@[reducible] def model.IP : go.GoType := go.GoType.Named go!"net.IP" []
@[reducible] def model.timeoutError : go.GoType := go.GoType.Named go!"net.timeoutError" []
@[reducible] def model.Errno : go.GoType := go.GoType.Named go!"syscall.Errno" []

/-- `&OpError{Op: op, Net: nw, Source: src, Addr: addr, Err: err}` as an `error` (D23: `nw` the
call's, connection's or listener's network). -/
noncomputable def model.opError : val :=
  λ: "op" "nw" "src" "addr" "err",
    let: "pe" := GoAlloc model.OpError (GoZeroVal model.OpError #()) in
    StructFieldRef model.OpError go!"Op" "pe" <-[go.string] "op" ;;
    StructFieldRef model.OpError go!"Net" "pe" <-[go.string] "nw" ;;
    StructFieldRef model.OpError go!"Source" "pe" <-[model.Addr] "src" ;;
    StructFieldRef model.OpError go!"Addr" "pe" <-[model.Addr] "addr" ;;
    StructFieldRef model.OpError go!"Err" "pe" <-[go.error] "err" ;;
    Convert (go.PointerType model.OpError) go.error "pe"

/-- `poll.ErrNetClosing` as an `error`: `errNetClosing{}`, the only value of an empty struct. -/
noncomputable def model.closedErr : val :=
>>>>>>> theirs
  λ: <>, Convert internal.poll.errNetClosing.ty go.error
    (GoZeroVal internal.poll.errNetClosing.ty #())

<<<<<<< ours
/-- `stuck()`: no behavior, the shared stuck point (`internal.gomodel.Stuck.impl`), where the
model does not model Go (a network but `"tcp"` and `"tcp4"`, D23). -/
noncomputable def stuck.impl : val := internal.gomodel.Stuck.impl
||||||| base
/-- The value of `poll.ErrDeadlineExceeded`. -/
noncomputable def model.deadlineErr : val :=
  λ: <>, ![go.error] (GlobalVarAddr internal.poll.ErrDeadlineExceeded #())

/-- `&os.SyscallError{Syscall: name, Err: syscall.Errno(n)}` as an `error`, `n` arbitrary and
nonzero. -/
noncomputable def model.sysErr : val :=
  λ: "name",
    let: "n" := ExternalOp Net.netExt.name "AnyErrno" #() in
    let: "p" := GoAlloc os.SyscallError.ty (GoZeroVal os.SyscallError.ty #()) in
    StructFieldRef os.SyscallError.ty go!"Syscall" "p" <-[go.string] "name" ;;
    StructFieldRef os.SyscallError.ty go!"Err" "p" <-[go.error] Convert model.Errno go.error "n" ;;
    Convert (go.PointerType os.SyscallError.ty) go.error "p"

/-- `syscall.EINVAL` (`Errno(0x16)`, `zerrors_linux_amd64.go`) as an `error`, bare: what Go's
methods return for a zero-value `TCPConn` or `TCPListener` (`return syscall.EINVAL` when `c.ok()`
or `l.ok()` fails: `net.go`, `tcpsock.go`; `TestZeroValues`). -/
noncomputable def model.einval : val :=
  λ: <>, Convert model.Errno go.error #(W64 22)

/-- The `Err` of a failure of the kind with code `code` (`Net.NetErr.code`), `name` the system
call's for a `sys` failure. -/
noncomputable def model.kindErr : val :=
  λ: "code" "name",
    if: "code" =⟨go.uint64⟩ #(W64 1) then model.closedErr #()
    else if: "code" =⟨go.uint64⟩ #(W64 2) then model.deadlineErr #()
    else model.sysErr "name"

/-- A new `*TCPAddr` with arbitrary fields, as an `Addr`. -/
noncomputable def model.anyTCPAddr : val :=
  λ: <>,
    let: "p" := GoAlloc model.TCPAddr (GoZeroVal model.TCPAddr #()) in
    StructFieldRef model.TCPAddr go!"IP" "p" <-[model.IP]
      Convert go.string (go.GoType.SliceType go.byte) (ExternalOp Net.netExt.name "AnyString" #()) ;;
    StructFieldRef model.TCPAddr go!"Port" "p" <-[go.int] ExternalOp Net.netExt.name "AnyW64" #() ;;
    StructFieldRef model.TCPAddr go!"Zone" "p" <-[go.string]
      ExternalOp Net.netExt.name "AnyString" #() ;;
    Convert (go.PointerType model.TCPAddr) model.Addr "p"

/-- The id of the connection end of a `*conn`. -/
noncomputable def model.connId : val :=
  λ: "c", ![go.uint64] (StructFieldRef model.conn go!"id" "c")

/-- The network of the `*conn` `c` (D23). -/
noncomputable def model.connNet : val :=
  λ: "c", ![go.string] (StructFieldRef model.conn go!"net" "c")

/-- The `*OpError` of the operation `op` on the `*conn` `c` (its network; `Source` its `laddr`,
`Addr` its `raddr`), for a failure of code `code`, `name` the system call's. -/
noncomputable def model.connErr : val :=
  λ: "op" "c" "code" "name",
    model.opError "op" (model.connNet "c") (![model.Addr] (StructFieldRef model.conn go!"laddr" "c"))
      (![model.Addr] (StructFieldRef model.conn go!"raddr" "c")) (model.kindErr "code" "name")

/-- A new `*TCPConn` for the connection end `id` on the network `nw`, with new addresses, as a
`Conn`. -/
noncomputable def model.newConn : val :=
  λ: "id" "nw",
    let: "t" := GoAlloc model.TCPConn (GoZeroVal model.TCPConn #()) in
    StructFieldRef model.conn go!"id" (StructFieldRef model.TCPConn go!"conn" "t") <-[go.uint64]
      "id" ;;
    StructFieldRef model.conn go!"net" (StructFieldRef model.TCPConn go!"conn" "t") <-[go.string]
      "nw" ;;
    StructFieldRef model.conn go!"laddr" (StructFieldRef model.TCPConn go!"conn" "t") <-[model.Addr]
      model.anyTCPAddr #() ;;
    StructFieldRef model.conn go!"raddr" (StructFieldRef model.TCPConn go!"conn" "t") <-[model.Addr]
      model.anyTCPAddr #() ;;
    Convert (go.PointerType model.TCPConn) model.Conn "t"

/-- D23. The networks modeled: `"tcp"` and `"tcp4"` (the valid addresses are IPv4: `"tcp4"`
behaves as `"tcp"` on them, `TestTcp4`). -/
noncomputable def model.netOk : val :=
  λ: "nw", if: "nw" =⟨go.string⟩ #(go!"tcp") then #true else "nw" =⟨go.string⟩ #(go!"tcp4")

/-- `Listen(network, address string) (Listener, error)` (`dial.go`): `ListenConfig.Listen` with
the zero `ListenConfig`, which for `"tcp"` resolves the address, then `socket(2)`, `setsockopt`
(`SO_REUSEADDR`), `bind(2)` and `listen(2)`: the extension's `Listen` of the address (a panic unless
it is valid, `addrOk`, or a wildcard of D21, `listenOk`). A
`*TCPListener` with a new address and the network (`"tcp"` or `"tcp4"`, D23) as a `Listener`; an
error is `&OpError{Op: "listen", Net: network, Addr: <the resolved address>, ...}` with a nil
`Listener`. -/
noncomputable def Listen.impl : val :=
  λ: "network" "address",
    if: model.netOk "network" then
      let: "r" := ExternalOp Net.netExt.name "Listen" "address" in
      if: Snd "r" =⟨go.uint64⟩ #(W64 0) then
        let: "l" := GoAlloc model.TCPListener (GoZeroVal model.TCPListener #()) in
        StructFieldRef model.TCPListener go!"lid" "l" <-[go.uint64] Fst "r" ;;
        StructFieldRef model.TCPListener go!"addr" "l" <-[model.Addr] model.anyTCPAddr #() ;;
        StructFieldRef model.TCPListener go!"net" "l" <-[go.string] "network" ;;
        (Convert (go.PointerType model.TCPListener) model.Listener "l", #GoInterface.nil)
      else (GoZeroVal model.Listener #(), model.opError #(go!"listen") "network" #GoInterface.nil
        (model.anyTCPAddr #())
        (model.kindErr (Snd "r") (ExternalOp Net.netExt.name "AnyString" #())))
    else Panic "net: Listen of a network but tcp and tcp4 not modelled"

/-- `Dial(network, address string) (Conn, error)` (`dial.go`): `Dialer.Dial` with the zero
`Dialer`, which for `"tcp"` resolves the address, then `socket(2)` and `connect(2)` (waiting for
the handshake): the extension's `Dial` (a panic unless the address is valid, `addrOk`). A `*TCPConn`
with new addresses and the network (`"tcp"` or `"tcp4"`, D23) as a `Conn`; an error is
`&OpError{Op: "dial", Net: network, Addr: <the resolved address>, ...}` (`dialSingle`) with a nil
`Conn`. -/
noncomputable def Dial.impl : val :=
  λ: "network" "address",
    if: model.netOk "network" then
      let: "r" := ExternalOp Net.netExt.name "Dial" "address" in
      if: Snd "r" =⟨go.uint64⟩ #(W64 0) then (model.newConn (Fst "r") "network", #GoInterface.nil)
      else (GoZeroVal model.Conn #(), model.opError #(go!"dial") "network" #GoInterface.nil
        (model.anyTCPAddr #())
        (model.kindErr (Snd "r") (ExternalOp Net.netExt.name "AnyString" #())))
    else Panic "net: Dial of a network but tcp and tcp4 not modelled"

/-- D19. `DialTimeout(network, address string, timeout time.Duration) (Conn, error)` (`dial.go`):
`Dialer{Timeout: timeout}.Dial`, the extension's `Dial` as `Dial.impl`; a failure's `Err` is the
system's error, or a timeout: `net`'s `errTimeout` (`mapErr(ctx.Err())` once the dial's context
expired: `dialSerial`, `partialDeadline`, `netFD.connect`) or `poll.ErrDeadlineExceeded`
(`netFD.connect`'s `WaitWrite` under the write deadline it sets to the dial's deadline, returned
as it is when the context's timer has not fired yet). The timeout's value is not modeled (any
timeout may expire, as the deadlines of D5); the dial's connection may be left, abandoned (D16). -/
noncomputable def DialTimeout.impl : val :=
  λ: "network" "address" "timeout",
    if: model.netOk "network" then
      let: "r" := ExternalOp Net.netExt.name "Dial" "address" in
      if: Snd "r" =⟨go.uint64⟩ #(W64 0) then (model.newConn (Fst "r") "network", #GoInterface.nil)
      else (GoZeroVal model.Conn #(), model.opError #(go!"dial") "network" #GoInterface.nil
        (model.anyTCPAddr #())
        (if: ExternalOp Net.netExt.name "AnyBool" #() then
          model.kindErr (Snd "r") (ExternalOp Net.netExt.name "AnyString" #())
         else if: ExternalOp Net.netExt.name "AnyBool" #() then
          ![go.error] (GlobalVarAddr go!"net.errTimeout" #())
         else model.deadlineErr #()))
    else Panic "net: DialTimeout of a network but tcp and tcp4 not modelled"

/-- `(*TCPListener).Accept() (Conn, error)` (`tcpsock.go`, `tcpsock_posix.go`'s `accept`):
`accept4(2)` through the poller (waiting for a connection; `ECONNABORTED` retried): the extension's
`Accept`. A `*TCPConn` with new addresses as a `Conn`; an error is
`&OpError{Op: "accept", Addr: l.addr, ...}`. A zero `TCPListener` (`lid` 0): `nil`,
`syscall.EINVAL`. -/
noncomputable def TCPListener.Accept.impl : val :=
  λ: "l" <>,
    if: ![go.uint64] (StructFieldRef model.TCPListener go!"lid" "l") =⟨go.uint64⟩ #(W64 0) then
      (GoZeroVal model.Conn #(), model.einval #())
    else
    let: "r" := ExternalOp Net.netExt.name "Accept"
      (![go.uint64] (StructFieldRef model.TCPListener go!"lid" "l")) in
    if: Snd "r" =⟨go.uint64⟩ #(W64 0) then
      (model.newConn (Fst "r") (![go.string] (StructFieldRef model.TCPListener go!"net" "l")),
        #GoInterface.nil)
    else (GoZeroVal model.Conn #(), model.opError #(go!"accept")
      (![go.string] (StructFieldRef model.TCPListener go!"net" "l")) #GoInterface.nil
      (![model.Addr] (StructFieldRef model.TCPListener go!"addr" "l"))
      (model.kindErr (Snd "r") #(go!"accept4")))

/-- `(*TCPListener).Close() error` (`tcpsock.go`): `close(2)` of the listening socket (a second
close is `ErrNetClosing`): the extension's `LisClose`; an error is
`&OpError{Op: "close", Addr: l.addr, ...}`. A zero `TCPListener`: `syscall.EINVAL`. -/
noncomputable def TCPListener.Close.impl : val :=
  λ: "l" <>,
    if: ![go.uint64] (StructFieldRef model.TCPListener go!"lid" "l") =⟨go.uint64⟩ #(W64 0) then
      model.einval #()
    else
    let: "r" := ExternalOp Net.netExt.name "LisClose"
      (![go.uint64] (StructFieldRef model.TCPListener go!"lid" "l")) in
    if: "r" =⟨go.uint64⟩ #(W64 0) then #GoInterface.nil
    else model.opError #(go!"close") (![go.string] (StructFieldRef model.TCPListener go!"net" "l"))
      #GoInterface.nil (![model.Addr] (StructFieldRef model.TCPListener go!"addr" "l"))
      (model.kindErr "r" #(go!"close"))

/-- `(*TCPListener).Addr() Addr` (`tcpsock.go`): `l.fd.laddr`, the stored address; a panic for a
zero `TCPListener` (`lid` 0), whose `fd` is nil in Go (a nil dereference). -/
noncomputable def TCPListener.Addr.impl : val :=
  λ: "l" <>,
    if: ![go.uint64] (StructFieldRef model.TCPListener go!"lid" "l") =⟨go.uint64⟩ #(W64 0) then
      Panic "net: Addr of a zero TCPListener"
    else ![model.Addr] (StructFieldRef model.TCPListener go!"addr" "l")

/-- `(*conn).Read(b []byte) (int, error)` (`net.go`, `fd_posix.go`, `poll.FD.Read`): `read(2)`
through the poller, which waits for bytes; an empty `b` returns `0, nil` at once; `0` bytes read
from a non-empty `b` is `io.EOF`: the extension's `Read` of `len(b)`, the bytes copied into `b`. An
error is `&OpError{Op: "read", ...}` with `0` bytes. A zero `TCPConn` (`id` 0): `0`,
`syscall.EINVAL`, before anything else (an empty `b` too). -/
noncomputable def conn.Read.impl : val :=
  λ: "c" "b",
    if: model.connId "c" =⟨go.uint64⟩ #(W64 0) then (#(W64 0), model.einval #()) else
    let: "r" := ExternalOp Net.netExt.name "Read"
      (model.connId "c", (FuncResolve go.len [go.GoType.SliceType go.byte]) #() "b") in
    if: Snd "r" =⟨go.uint64⟩ #(W64 0) then
      ((FuncResolve go.copy [go.GoType.SliceType go.byte]) #() "b"
        (Convert go.string (go.GoType.SliceType go.byte) (Fst "r")), #GoInterface.nil)
    else if: Snd "r" =⟨go.uint64⟩ #(W64 4) then (#(W64 0), ![go.error] (GlobalVarAddr io.EOF #()))
    else (#(W64 0), model.connErr #(go!"read") "c" (Snd "r") #(go!"read"))

/-- Go's loop in `(*poll.FD).Write` (`internal/poll/fd_unix.go`; `Impl.lean`, D2), from `nn` bytes
of `b` written, for the `*conn` `c`: a `write(2)` of `b[nn:]` with its wait, the extension's `Write`
of those bytes (one step: the count it adds and its result's code), until a step fails or `nn` is
`len(b)`: `(nn, nil)` then, else `(nn, err)` with `err` the `&OpError{Op: "write", ...}` of the
failing step's kind. (Go tests `nn == len(p)` before the error, returning `nn, err` there: `err` is
nil but for an empty `b`, whose one step's error both return.) `b`'s bytes are read at each step,
as `write(2)` reads them; Go's `maxRW` chunks (1 GiB) are among a step's outcomes (any prefix).
D25: each step says whether it is the `Write`'s first (`nn = 0`: a later step has counted at least
one byte, since a step that does not fail and does not end the loop counts one), which takes the
end's write lock (Go's `fd.writeLock()` before the loop), released by the loop's last step (its
`defer fd.writeUnlock()`). -/
noncomputable def model.writeLoop : val :=
  rec: "write" "c" "b" "nn" :=
    let: "len" := (FuncResolve go.len [go.GoType.SliceType go.byte]) #() "b" in
    let: "r" := ExternalOp Net.netExt.name "Write" (model.connId "c",
      (Convert (go.GoType.SliceType go.byte) go.string
        (Slice (go.GoType.SliceType go.byte) ("b", "nn", "len")), "nn" =⟨go.int⟩ #(W64 0))) in
    let: "nn" := "nn" +⟨go.int⟩ Fst "r" in
    if: Snd "r" ≠⟨go.uint64⟩ #(W64 0) then
      ("nn", model.connErr #(go!"write") "c" (Snd "r") #(go!"write"))
    else if: "nn" =⟨go.int⟩ "len" then ("nn", #GoInterface.nil)
    else "write" "c" "b" "nn"

/-- `(*conn).Write(b []byte) (int, error)` (`net.go`, `fd_posix.go`, `poll.FD.Write`): Go's loop
from nothing written (`model.writeLoop`). A zero `TCPConn`: `0`, `syscall.EINVAL`. -/
noncomputable def conn.Write.impl : val :=
  λ: "c" "b",
    if: model.connId "c" =⟨go.uint64⟩ #(W64 0) then (#(W64 0), model.einval #())
    else model.writeLoop "c" "b" #(W64 0)

/-- `(*conn).Close() error` (`net.go`, `fd_posix.go`): `close(2)` of the socket (a second close
is `ErrNetClosing`): the extension's `Close`. A zero `TCPConn`: `syscall.EINVAL`. -/
noncomputable def conn.Close.impl : val :=
  λ: "c" <>,
    if: model.connId "c" =⟨go.uint64⟩ #(W64 0) then model.einval #() else
    let: "r" := ExternalOp Net.netExt.name "Close" (model.connId "c") in
    if: "r" =⟨go.uint64⟩ #(W64 0) then #GoInterface.nil
    else model.connErr #(go!"close") "c" "r" #(go!"close")

/-- `(*TCPConn).CloseWrite() error` (`tcpsock.go`): `shutdown(2)` with `SHUT_WR`: the
extension's `CloseWrite`. A zero `TCPConn`: `syscall.EINVAL`. -/
noncomputable def TCPConn.CloseWrite.impl : val :=
  λ: "c" <>,
    if: model.connId (StructFieldRef model.TCPConn go!"conn" "c") =⟨go.uint64⟩ #(W64 0) then
      model.einval #() else
    let: "r" := ExternalOp Net.netExt.name "CloseWrite"
      (model.connId (StructFieldRef model.TCPConn go!"conn" "c")) in
    if: "r" =⟨go.uint64⟩ #(W64 0) then #GoInterface.nil
    else model.connErr #(go!"close") (StructFieldRef model.TCPConn go!"conn" "c") "r"
      #(go!"shutdown")

/-- The extension's `SetDeadline` of the deadlines of kind `kind` (`0` both, `1` read, `2` write)
of the end of `c` to the time `t`: `t`'s two words (`wall`, `ext`; the extension decides whether it
is Go's zero time, `Net.timeIsZero`), read through a copy of `t` (the cell is the model's, never
seen by the program). An error is `&OpError{Op: "set", Source: nil, Addr: c.laddr, ...}`. A zero
`TCPConn`: `syscall.EINVAL`. -/
noncomputable def model.setDeadline (kind : w64) : val :=
  λ: "c" "t",
    if: model.connId "c" =⟨go.uint64⟩ #(W64 0) then model.einval #() else
    let: "tp" := GoAlloc time.Time.ty "t" in
    let: "r" := ExternalOp Net.netExt.name "SetDeadline"
        (model.connId "c", (#kind, (![go.uint64] (StructFieldRef time.Time.ty go!"wall" "tp"),
          ![go.int64] (StructFieldRef time.Time.ty go!"ext" "tp")))) in
    if: "r" =⟨go.uint64⟩ #(W64 0) then #GoInterface.nil
    else model.opError #(go!"set") (model.connNet "c") #GoInterface.nil
      (![model.Addr] (StructFieldRef model.conn go!"laddr" "c")) (model.kindErr "r" #(go!"set"))

/-- `(*conn).SetDeadline(t time.Time) error` (`net.go`, `poll.FD.SetDeadline`): sets the read and
the write deadline with the poller, or clears them for the zero time (`ErrNetClosing` on a closed
socket): the extension's `SetDeadline` of both. -/
noncomputable def conn.SetDeadline.impl : val := model.setDeadline (W64 0)

/-- `(*conn).SetReadDeadline(t time.Time) error`: the read deadline only. -/
noncomputable def conn.SetReadDeadline.impl : val := model.setDeadline (W64 1)

/-- `(*conn).SetWriteDeadline(t time.Time) error`: the write deadline only. -/
noncomputable def conn.SetWriteDeadline.impl : val := model.setDeadline (W64 2)

/-- D24. A socket option of the kind `kind` (`Net.sockOptValid`: `1` `TCP_KEEPIDLE`, `0` the
others) with the value `x`, set on the end of the `*conn` `c`: the extension's `SetSockopt`; an error
is `&OpError{Op: "set", Net: <c's network>, Source, Addr, ...}`, `Source` and `Addr` `c`'s `laddr` and
`raddr` for `TCPConn`'s methods (`tcpsock.go`, `errf` = `model.sockOptErrTCP`), `nil` and `laddr`
for `conn`'s (`net.go`'s `SetReadBuffer`, `SetWriteBuffer`: `model.sockOptErrConn`), `Err` `ErrNetClosing` or an `*os.SyscallError{"setsockopt"}`
(`wrapSyscallError`). A zero `TCPConn`: `syscall.EINVAL`, before anything else. -/
noncomputable def model.sockOpt (errf : val) (kind : w64) : val :=
  λ: "c" "x",
    if: model.connId "c" =⟨go.uint64⟩ #(W64 0) then model.einval #() else
    let: "r" := ExternalOp Net.netExt.name "SetSockopt" (model.connId "c", (#kind, "x")) in
    if: "r" =⟨go.uint64⟩ #(W64 0) then #GoInterface.nil
    else errf "c" "r"

/-- D24. The error of a socket option of `TCPConn`'s, of code `code`, on the `*conn` `c`. -/
noncomputable def model.sockOptErrTCP : val :=
  λ: "c" "code", model.connErr #(go!"set") "c" "code" #(go!"setsockopt")

/-- D24. The error of a socket option of `conn`'s (`Source` nil, `Addr` `laddr`). -/
noncomputable def model.sockOptErrConn : val :=
  λ: "c" "code",
    model.opError #(go!"set") (model.connNet "c") #GoInterface.nil
      (![model.Addr] (StructFieldRef model.conn go!"laddr" "c"))
      (model.kindErr "code" #(go!"setsockopt"))

/-- D24. `(*TCPConn).SetKeepAlive(keepalive bool) error` (`tcpsock.go`): `SO_KEEPALIVE`
(`sockopt_posix.go`'s `setKeepAlive`), whatever the value. -/
noncomputable def TCPConn.SetKeepAlive.impl : val :=
  λ: "c" "b", model.sockOpt model.sockOptErrTCP (W64 0) (StructFieldRef model.TCPConn go!"conn" "c") #(W64 0)

/-- D24. `(*TCPConn).SetKeepAlivePeriod(d time.Duration) error` (`tcpsock.go`): `setKeepAliveIdle`
(`tcpsockopt_unix.go`) of `d`, whose arithmetic (`d = 0` the default, `d < 0` no system call, the
count of seconds) the extension's `keepIdleValid` transcribes. -/
noncomputable def TCPConn.SetKeepAlivePeriod.impl : val :=
  λ: "c" "d", model.sockOpt model.sockOptErrTCP (W64 1) (StructFieldRef model.TCPConn go!"conn" "c") "d"

/-- D24. `(*TCPConn).SetNoDelay(noDelay bool) error` (`tcpsock.go`): `TCP_NODELAY`. -/
noncomputable def TCPConn.SetNoDelay.impl : val :=
  λ: "c" "b", model.sockOpt model.sockOptErrTCP (W64 0) (StructFieldRef model.TCPConn go!"conn" "c") #(W64 0)

/-- D24. `(*TCPConn).SetLinger(sec int) error` (`tcpsock.go`): `SO_LINGER`, whatever the value
(what a linger changes, a `Close` that resets, is a cut: D1). -/
noncomputable def TCPConn.SetLinger.impl : val :=
  λ: "c" "sec", model.sockOpt model.sockOptErrTCP (W64 0) (StructFieldRef model.TCPConn go!"conn" "c") #(W64 0)

/-- D24. `(*conn).SetReadBuffer(bytes int) error` (`net.go`): `SO_RCVBUF`, whatever the value
(Linux clamps it). -/
noncomputable def conn.SetReadBuffer.impl : val :=
  λ: "c" "n", model.sockOpt model.sockOptErrConn (W64 0) "c" #(W64 0)

/-- D24. `(*conn).SetWriteBuffer(bytes int) error` (`net.go`): `SO_SNDBUF`, as `SetReadBuffer`. -/
noncomputable def conn.SetWriteBuffer.impl : val :=
  λ: "c" "n", model.sockOpt model.sockOptErrConn (W64 0) "c" #(W64 0)

/-- D18. `(*conn).LocalAddr() Addr` (`net.go`): `c.fd.laddr`, the stored address (`nil` for a zero
`TCPConn`, as Go's `c.ok()` check gives). -/
noncomputable def conn.LocalAddr.impl : val :=
  λ: "c" <>, ![model.Addr] (StructFieldRef model.conn go!"laddr" "c")

/-- D18. `(*conn).RemoteAddr() Addr` (`net.go`): `c.fd.raddr`, as `LocalAddr`. -/
noncomputable def conn.RemoteAddr.impl : val :=
  λ: "c" <>, ![model.Addr] (StructFieldRef model.conn go!"raddr" "c")

/-- `(*TCPAddr).String() string` (`tcpsock.go`): made of the address's fields, which the model does
not explain: an arbitrary string. -/
noncomputable def TCPAddr.String.impl : val :=
  λ: "a" <>, ExternalOp Net.netExt.name "AnyString" #()

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


/-- No type of `net` is named `_`: goose takes every trusted name for a possible type too, and the
blank variables' name `_` is trusted (below), so it asks for an underlying type, which nothing
uses. -/
@[reducible] def «_».underlying : go.GoType := go.GoType.StructType []
=======
/-- The value of `poll.ErrDeadlineExceeded`. -/
noncomputable def model.deadlineErr : val :=
  λ: <>, ![go.error] (GlobalVarAddr internal.poll.ErrDeadlineExceeded #())

/-- `&os.SyscallError{Syscall: name, Err: syscall.Errno(n)}` as an `error`, `n` arbitrary and
nonzero. -/
noncomputable def model.sysErr : val :=
  λ: "name",
    let: "n" := ExternalOp Net.netExt.name "AnyErrno" #() in
    let: "p" := GoAlloc os.SyscallError.ty (GoZeroVal os.SyscallError.ty #()) in
    StructFieldRef os.SyscallError.ty go!"Syscall" "p" <-[go.string] "name" ;;
    StructFieldRef os.SyscallError.ty go!"Err" "p" <-[go.error] Convert model.Errno go.error "n" ;;
    Convert (go.PointerType os.SyscallError.ty) go.error "p"

/-- `syscall.EINVAL` (`Errno(0x16)`, `zerrors_linux_amd64.go`) as an `error`, bare: what Go's
methods return for a zero-value `TCPConn` or `TCPListener` (`return syscall.EINVAL` when `c.ok()`
or `l.ok()` fails: `net.go`, `tcpsock.go`; `TestZeroValues`). -/
noncomputable def model.einval : val :=
  λ: <>, Convert model.Errno go.error #(W64 22)

/-- The `Err` of a failure of the kind with code `code` (`Net.NetErr.code`), `name` the system
call's for a `sys` failure. -/
noncomputable def model.kindErr : val :=
  λ: "code" "name",
    if: "code" =⟨go.uint64⟩ #(W64 1) then model.closedErr #()
    else if: "code" =⟨go.uint64⟩ #(W64 2) then model.deadlineErr #()
    else model.sysErr "name"

/-- A new `*TCPAddr` with arbitrary fields, as an `Addr`. -/
noncomputable def model.anyTCPAddr : val :=
  λ: <>,
    let: "p" := GoAlloc model.TCPAddr (GoZeroVal model.TCPAddr #()) in
    StructFieldRef model.TCPAddr go!"IP" "p" <-[model.IP]
      Convert go.string (go.GoType.SliceType go.byte) (ExternalOp Net.netExt.name "AnyString" #()) ;;
    StructFieldRef model.TCPAddr go!"Port" "p" <-[go.int] ExternalOp Net.netExt.name "AnyW64" #() ;;
    StructFieldRef model.TCPAddr go!"Zone" "p" <-[go.string]
      ExternalOp Net.netExt.name "AnyString" #() ;;
    Convert (go.PointerType model.TCPAddr) model.Addr "p"

/-- The id of the connection end of a `*conn`. -/
noncomputable def model.connId : val :=
  λ: "c", ![go.uint64] (StructFieldRef model.conn go!"id" "c")

/-- The network of the `*conn` `c` (D23). -/
noncomputable def model.connNet : val :=
  λ: "c", ![go.string] (StructFieldRef model.conn go!"net" "c")

/-- The `*OpError` of the operation `op` on the `*conn` `c` (its network; `Source` its `laddr`,
`Addr` its `raddr`), for a failure of code `code`, `name` the system call's. -/
noncomputable def model.connErr : val :=
  λ: "op" "c" "code" "name",
    model.opError "op" (model.connNet "c") (![model.Addr] (StructFieldRef model.conn go!"laddr" "c"))
      (![model.Addr] (StructFieldRef model.conn go!"raddr" "c")) (model.kindErr "code" "name")

/-- A new `*TCPConn` for the connection end `id` on the network `nw`, with new addresses, as a
`Conn`. -/
noncomputable def model.newConn : val :=
  λ: "id" "nw",
    let: "t" := GoAlloc model.TCPConn (GoZeroVal model.TCPConn #()) in
    StructFieldRef model.conn go!"id" (StructFieldRef model.TCPConn go!"conn" "t") <-[go.uint64]
      "id" ;;
    StructFieldRef model.conn go!"net" (StructFieldRef model.TCPConn go!"conn" "t") <-[go.string]
      "nw" ;;
    StructFieldRef model.conn go!"laddr" (StructFieldRef model.TCPConn go!"conn" "t") <-[model.Addr]
      model.anyTCPAddr #() ;;
    StructFieldRef model.conn go!"raddr" (StructFieldRef model.TCPConn go!"conn" "t") <-[model.Addr]
      model.anyTCPAddr #() ;;
    Convert (go.PointerType model.TCPConn) model.Conn "t"

/-- D23. The networks modeled: `"tcp"` and `"tcp4"` (the valid addresses are IPv4: `"tcp4"`
behaves as `"tcp"` on them, `TestTcp4`). -/
noncomputable def model.netOk : val :=
  λ: "nw", if: "nw" =⟨go.string⟩ #(go!"tcp") then #true else "nw" =⟨go.string⟩ #(go!"tcp4")

/-- `Listen(network, address string) (Listener, error)` (`dial.go`): `ListenConfig.Listen` with
the zero `ListenConfig`, which for `"tcp"` resolves the address, then `socket(2)`, `setsockopt`
(`SO_REUSEADDR`), `bind(2)` and `listen(2)`: the extension's `Listen` of the address (a panic unless
it is valid, `addrOk`, or a wildcard of D21, `listenOk`). A
`*TCPListener` with a new address and the network (`"tcp"` or `"tcp4"`, D23) as a `Listener`; an
error is `&OpError{Op: "listen", Net: network, Addr: <the resolved address>, ...}` with a nil
`Listener`. -/
noncomputable def Listen.impl : val :=
  λ: "network" "address",
    if: model.netOk "network" then
      let: "r" := ExternalOp Net.netExt.name "Listen" "address" in
      if: Snd "r" =⟨go.uint64⟩ #(W64 0) then
        let: "l" := GoAlloc model.TCPListener (GoZeroVal model.TCPListener #()) in
        StructFieldRef model.TCPListener go!"lid" "l" <-[go.uint64] Fst "r" ;;
        StructFieldRef model.TCPListener go!"addr" "l" <-[model.Addr] model.anyTCPAddr #() ;;
        StructFieldRef model.TCPListener go!"net" "l" <-[go.string] "network" ;;
        (Convert (go.PointerType model.TCPListener) model.Listener "l", #GoInterface.nil)
      else (GoZeroVal model.Listener #(), model.opError #(go!"listen") "network" #GoInterface.nil
        (model.anyTCPAddr #())
        (model.kindErr (Snd "r") (ExternalOp Net.netExt.name "AnyString" #())))
    else Panic "net: Listen of a network but tcp and tcp4 not modelled"

/-- `Dial(network, address string) (Conn, error)` (`dial.go`): `Dialer.Dial` with the zero
`Dialer`, which for `"tcp"` resolves the address, then `socket(2)` and `connect(2)` (waiting for
the handshake): the extension's `Dial` (a panic unless the address is valid, `addrOk`). A `*TCPConn`
with new addresses and the network (`"tcp"` or `"tcp4"`, D23) as a `Conn`; an error is
`&OpError{Op: "dial", Net: network, Addr: <the resolved address>, ...}` (`dialSingle`) with a nil
`Conn`. -/
noncomputable def Dial.impl : val :=
  λ: "network" "address",
    if: model.netOk "network" then
      let: "r" := ExternalOp Net.netExt.name "Dial" "address" in
      if: Snd "r" =⟨go.uint64⟩ #(W64 0) then (model.newConn (Fst "r") "network", #GoInterface.nil)
      else (GoZeroVal model.Conn #(), model.opError #(go!"dial") "network" #GoInterface.nil
        (model.anyTCPAddr #())
        (model.kindErr (Snd "r") (ExternalOp Net.netExt.name "AnyString" #())))
    else Panic "net: Dial of a network but tcp and tcp4 not modelled"

/-- D19. `DialTimeout(network, address string, timeout time.Duration) (Conn, error)` (`dial.go`):
`Dialer{Timeout: timeout}.Dial`, the extension's `Dial` as `Dial.impl`; a failure's `Err` is the
system's error, or a timeout: `net`'s `errTimeout` (`mapErr(ctx.Err())` once the dial's context
expired: `dialSerial`, `partialDeadline`, `netFD.connect`) or `poll.ErrDeadlineExceeded`
(`netFD.connect`'s `WaitWrite` under the write deadline it sets to the dial's deadline, returned
as it is when the context's timer has not fired yet). The timeout's value is not modeled (any
timeout may expire, as the deadlines of D5); the dial's connection may be left, abandoned (D16). -/
noncomputable def DialTimeout.impl : val :=
  λ: "network" "address" "timeout",
    if: model.netOk "network" then
      let: "r" := ExternalOp Net.netExt.name "Dial" "address" in
      if: Snd "r" =⟨go.uint64⟩ #(W64 0) then (model.newConn (Fst "r") "network", #GoInterface.nil)
      else (GoZeroVal model.Conn #(), model.opError #(go!"dial") "network" #GoInterface.nil
        (model.anyTCPAddr #())
        (if: ExternalOp Net.netExt.name "AnyBool" #() then
          model.kindErr (Snd "r") (ExternalOp Net.netExt.name "AnyString" #())
         else if: ExternalOp Net.netExt.name "AnyBool" #() then
          ![go.error] (GlobalVarAddr go!"net.errTimeout" #())
         else model.deadlineErr #()))
    else Panic "net: DialTimeout of a network but tcp and tcp4 not modelled"

/-- `(*TCPListener).Accept() (Conn, error)` (`tcpsock.go`, `tcpsock_posix.go`'s `accept`):
`accept4(2)` through the poller (waiting for a connection; `ECONNABORTED` retried): the extension's
`Accept`. A `*TCPConn` with new addresses as a `Conn`; an error is
`&OpError{Op: "accept", Addr: l.addr, ...}`. A zero `TCPListener` (`lid` 0): `nil`,
`syscall.EINVAL`. -/
noncomputable def TCPListener.Accept.impl : val :=
  λ: "l" <>,
    if: ![go.uint64] (StructFieldRef model.TCPListener go!"lid" "l") =⟨go.uint64⟩ #(W64 0) then
      (GoZeroVal model.Conn #(), model.einval #())
    else
    let: "r" := ExternalOp Net.netExt.name "Accept"
      (![go.uint64] (StructFieldRef model.TCPListener go!"lid" "l")) in
    if: Snd "r" =⟨go.uint64⟩ #(W64 0) then
      (model.newConn (Fst "r") (![go.string] (StructFieldRef model.TCPListener go!"net" "l")),
        #GoInterface.nil)
    else (GoZeroVal model.Conn #(), model.opError #(go!"accept")
      (![go.string] (StructFieldRef model.TCPListener go!"net" "l")) #GoInterface.nil
      (![model.Addr] (StructFieldRef model.TCPListener go!"addr" "l"))
      (model.kindErr (Snd "r") #(go!"accept4")))

/-- `(*TCPListener).Close() error` (`tcpsock.go`): `close(2)` of the listening socket (a second
close is `ErrNetClosing`): the extension's `LisClose`; an error is
`&OpError{Op: "close", Addr: l.addr, ...}`. A zero `TCPListener`: `syscall.EINVAL`. -/
noncomputable def TCPListener.Close.impl : val :=
  λ: "l" <>,
    if: ![go.uint64] (StructFieldRef model.TCPListener go!"lid" "l") =⟨go.uint64⟩ #(W64 0) then
      model.einval #()
    else
    let: "r" := ExternalOp Net.netExt.name "LisClose"
      (![go.uint64] (StructFieldRef model.TCPListener go!"lid" "l")) in
    if: "r" =⟨go.uint64⟩ #(W64 0) then #GoInterface.nil
    else model.opError #(go!"close") (![go.string] (StructFieldRef model.TCPListener go!"net" "l"))
      #GoInterface.nil (![model.Addr] (StructFieldRef model.TCPListener go!"addr" "l"))
      (model.kindErr "r" #(go!"close"))

/-- `(*TCPListener).Addr() Addr` (`tcpsock.go`): `l.fd.laddr`, the stored address; a panic for a
zero `TCPListener` (`lid` 0), whose `fd` is nil in Go (a nil dereference). -/
noncomputable def TCPListener.Addr.impl : val :=
  λ: "l" <>,
    if: ![go.uint64] (StructFieldRef model.TCPListener go!"lid" "l") =⟨go.uint64⟩ #(W64 0) then
      Panic "net: Addr of a zero TCPListener"
    else ![model.Addr] (StructFieldRef model.TCPListener go!"addr" "l")

/-- `(*conn).Read(b []byte) (int, error)` (`net.go`, `fd_posix.go`, `poll.FD.Read`): `read(2)`
through the poller, which waits for bytes; an empty `b` returns `0, nil` at once; `0` bytes read
from a non-empty `b` is `io.EOF`: the extension's `Read` of `len(b)`, the bytes copied into `b`. An
error is `&OpError{Op: "read", ...}` with `0` bytes. A zero `TCPConn` (`id` 0): `0`,
`syscall.EINVAL`, before anything else (an empty `b` too). -/
noncomputable def conn.Read.impl : val :=
  λ: "c" "b",
    if: model.connId "c" =⟨go.uint64⟩ #(W64 0) then (#(W64 0), model.einval #()) else
    let: "r" := ExternalOp Net.netExt.name "Read"
      (model.connId "c", (FuncResolve go.len [go.GoType.SliceType go.byte]) #() "b") in
    if: Snd "r" =⟨go.uint64⟩ #(W64 0) then
      ((FuncResolve go.copy [go.GoType.SliceType go.byte]) #() "b"
        (Convert go.string (go.GoType.SliceType go.byte) (Fst "r")), #GoInterface.nil)
    else if: Snd "r" =⟨go.uint64⟩ #(W64 4) then (#(W64 0), ![go.error] (GlobalVarAddr io.EOF #()))
    else (#(W64 0), model.connErr #(go!"read") "c" (Snd "r") #(go!"read"))

/-- Go's loop in `(*poll.FD).Write` (`internal/poll/fd_unix.go`; `Impl.lean`, D2), from `nn` bytes
of `b` written, for the `*conn` `c`: a `write(2)` of `b[nn:]` with its wait, the extension's `Write`
of those bytes (one step: the count it adds and its result's code), until a step fails or `nn` is
`len(b)`: `(nn, nil)` then, else `(nn, err)` with `err` the `&OpError{Op: "write", ...}` of the
failing step's kind. (Go tests `nn == len(p)` before the error, returning `nn, err` there: `err` is
nil but for an empty `b`, whose one step's error both return.) `b`'s bytes are read at each step,
as `write(2)` reads them; Go's `maxRW` chunks (1 GiB) are among a step's outcomes (any prefix).
D25: each step says whether it is the `Write`'s first (`nn = 0`: a later step has counted at least
one byte, since a step that does not fail and does not end the loop counts one), which takes the
end's write lock (Go's `fd.writeLock()` before the loop), released by the loop's last step (its
`defer fd.writeUnlock()`). -/
noncomputable def model.writeLoop : val :=
  rec: "write" "c" "b" "nn" :=
    let: "len" := (FuncResolve go.len [go.GoType.SliceType go.byte]) #() "b" in
    let: "r" := ExternalOp Net.netExt.name "Write" (model.connId "c",
      (Convert (go.GoType.SliceType go.byte) go.string
        (Slice (go.GoType.SliceType go.byte) ("b", "nn", "len")), "nn" =⟨go.int⟩ #(W64 0))) in
    let: "nn" := "nn" +⟨go.int⟩ Fst "r" in
    if: Snd "r" ≠⟨go.uint64⟩ #(W64 0) then
      ("nn", model.connErr #(go!"write") "c" (Snd "r") #(go!"write"))
    else if: "nn" =⟨go.int⟩ "len" then ("nn", #GoInterface.nil)
    else "write" "c" "b" "nn"

/-- `(*conn).Write(b []byte) (int, error)` (`net.go`, `fd_posix.go`, `poll.FD.Write`): Go's loop
from nothing written (`model.writeLoop`). A zero `TCPConn`: `0`, `syscall.EINVAL`. -/
noncomputable def conn.Write.impl : val :=
  λ: "c" "b",
    if: model.connId "c" =⟨go.uint64⟩ #(W64 0) then (#(W64 0), model.einval #())
    else model.writeLoop "c" "b" #(W64 0)

/-- `(*conn).Close() error` (`net.go`, `fd_posix.go`): `close(2)` of the socket (a second close
is `ErrNetClosing`): the extension's `Close`. A zero `TCPConn`: `syscall.EINVAL`. -/
noncomputable def conn.Close.impl : val :=
  λ: "c" <>,
    if: model.connId "c" =⟨go.uint64⟩ #(W64 0) then model.einval #() else
    let: "r" := ExternalOp Net.netExt.name "Close" (model.connId "c") in
    if: "r" =⟨go.uint64⟩ #(W64 0) then #GoInterface.nil
    else model.connErr #(go!"close") "c" "r" #(go!"close")

/-- `(*TCPConn).CloseWrite() error` (`tcpsock.go`): `shutdown(2)` with `SHUT_WR`: the
extension's `CloseWrite`. A zero `TCPConn`: `syscall.EINVAL`. -/
noncomputable def TCPConn.CloseWrite.impl : val :=
  λ: "c" <>,
    if: model.connId (StructFieldRef model.TCPConn go!"conn" "c") =⟨go.uint64⟩ #(W64 0) then
      model.einval #() else
    let: "r" := ExternalOp Net.netExt.name "CloseWrite"
      (model.connId (StructFieldRef model.TCPConn go!"conn" "c")) in
    if: "r" =⟨go.uint64⟩ #(W64 0) then #GoInterface.nil
    else model.connErr #(go!"close") (StructFieldRef model.TCPConn go!"conn" "c") "r"
      #(go!"shutdown")

/-- The extension's `SetDeadline` of the deadlines of kind `kind` (`0` both, `1` read, `2` write)
of the end of `c` to the time `t`: `t`'s two words (`wall`, `ext`; the extension decides whether it
is Go's zero time, `Net.timeIsZero`), read through a copy of `t` (the cell is the model's, never
seen by the program). An error is `&OpError{Op: "set", Source: nil, Addr: c.laddr, ...}`. A zero
`TCPConn`: `syscall.EINVAL`. -/
noncomputable def model.setDeadline (kind : w64) : val :=
  λ: "c" "t",
    if: model.connId "c" =⟨go.uint64⟩ #(W64 0) then model.einval #() else
    let: "tp" := GoAlloc time.Time.ty "t" in
    let: "r" := ExternalOp Net.netExt.name "SetDeadline"
        (model.connId "c", (#kind, (![go.uint64] (StructFieldRef time.Time.ty go!"wall" "tp"),
          ![go.int64] (StructFieldRef time.Time.ty go!"ext" "tp")))) in
    if: "r" =⟨go.uint64⟩ #(W64 0) then #GoInterface.nil
    else model.opError #(go!"set") (model.connNet "c") #GoInterface.nil
      (![model.Addr] (StructFieldRef model.conn go!"laddr" "c")) (model.kindErr "r" #(go!"set"))

/-- `(*conn).SetDeadline(t time.Time) error` (`net.go`, `poll.FD.SetDeadline`): sets the read and
the write deadline with the poller, or clears them for the zero time (`ErrNetClosing` on a closed
socket): the extension's `SetDeadline` of both. -/
noncomputable def conn.SetDeadline.impl : val := model.setDeadline (W64 0)

/-- `(*conn).SetReadDeadline(t time.Time) error`: the read deadline only. -/
noncomputable def conn.SetReadDeadline.impl : val := model.setDeadline (W64 1)

/-- `(*conn).SetWriteDeadline(t time.Time) error`: the write deadline only. -/
noncomputable def conn.SetWriteDeadline.impl : val := model.setDeadline (W64 2)

/-- D24. A socket option of the kind `kind` (`Net.sockOptValid`: `1` `TCP_KEEPIDLE`, `0` the
others) with the value `x`, set on the end of the `*conn` `c`: the extension's `SetSockopt`; an error
is `&OpError{Op: "set", Net: <c's network>, Source, Addr, ...}`, `Source` and `Addr` `c`'s `laddr` and
`raddr` for `TCPConn`'s methods (`tcpsock.go`, `errf` = `model.sockOptErrTCP`), `nil` and `laddr`
for `conn`'s (`net.go`'s `SetReadBuffer`, `SetWriteBuffer`: `model.sockOptErrConn`), `Err` `ErrNetClosing` or an `*os.SyscallError{"setsockopt"}`
(`wrapSyscallError`). A zero `TCPConn`: `syscall.EINVAL`, before anything else. -/
noncomputable def model.sockOpt (errf : val) (kind : w64) : val :=
  λ: "c" "x",
    if: model.connId "c" =⟨go.uint64⟩ #(W64 0) then model.einval #() else
    let: "r" := ExternalOp Net.netExt.name "SetSockopt" (model.connId "c", (#kind, "x")) in
    if: "r" =⟨go.uint64⟩ #(W64 0) then #GoInterface.nil
    else errf "c" "r"

/-- D24. The error of a socket option of `TCPConn`'s, of code `code`, on the `*conn` `c`. -/
noncomputable def model.sockOptErrTCP : val :=
  λ: "c" "code", model.connErr #(go!"set") "c" "code" #(go!"setsockopt")

/-- D24. The error of a socket option of `conn`'s (`Source` nil, `Addr` `laddr`). -/
noncomputable def model.sockOptErrConn : val :=
  λ: "c" "code",
    model.opError #(go!"set") (model.connNet "c") #GoInterface.nil
      (![model.Addr] (StructFieldRef model.conn go!"laddr" "c"))
      (model.kindErr "code" #(go!"setsockopt"))

/-- D24. `(*TCPConn).SetKeepAlive(keepalive bool) error` (`tcpsock.go`): `SO_KEEPALIVE`
(`sockopt_posix.go`'s `setKeepAlive`), whatever the value. -/
noncomputable def TCPConn.SetKeepAlive.impl : val :=
  λ: "c" "b", model.sockOpt model.sockOptErrTCP (W64 0) (StructFieldRef model.TCPConn go!"conn" "c") #(W64 0)

/-- D24. `(*TCPConn).SetKeepAlivePeriod(d time.Duration) error` (`tcpsock.go`): `setKeepAliveIdle`
(`tcpsockopt_unix.go`) of `d`, whose arithmetic (`d = 0` the default, `d < 0` no system call, the
count of seconds) the extension's `keepIdleValid` transcribes. -/
noncomputable def TCPConn.SetKeepAlivePeriod.impl : val :=
  λ: "c" "d", model.sockOpt model.sockOptErrTCP (W64 1) (StructFieldRef model.TCPConn go!"conn" "c") "d"

/-- D24. `(*TCPConn).SetNoDelay(noDelay bool) error` (`tcpsock.go`): `TCP_NODELAY`. -/
noncomputable def TCPConn.SetNoDelay.impl : val :=
  λ: "c" "b", model.sockOpt model.sockOptErrTCP (W64 0) (StructFieldRef model.TCPConn go!"conn" "c") #(W64 0)

/-- D24. `(*TCPConn).SetLinger(sec int) error` (`tcpsock.go`): `SO_LINGER`, whatever the value
(what a linger changes, a `Close` that resets, is a cut: D1). -/
noncomputable def TCPConn.SetLinger.impl : val :=
  λ: "c" "sec", model.sockOpt model.sockOptErrTCP (W64 0) (StructFieldRef model.TCPConn go!"conn" "c") #(W64 0)

/-- D24. `(*conn).SetReadBuffer(bytes int) error` (`net.go`): `SO_RCVBUF`, whatever the value
(Linux clamps it). -/
noncomputable def conn.SetReadBuffer.impl : val :=
  λ: "c" "n", model.sockOpt model.sockOptErrConn (W64 0) "c" #(W64 0)

/-- D24. `(*conn).SetWriteBuffer(bytes int) error` (`net.go`): `SO_SNDBUF`, as `SetReadBuffer`. -/
noncomputable def conn.SetWriteBuffer.impl : val :=
  λ: "c" "n", model.sockOpt model.sockOptErrConn (W64 0) "c" #(W64 0)

/-- D18. `(*conn).LocalAddr() Addr` (`net.go`): `c.fd.laddr`, the stored address (`nil` for a zero
`TCPConn`, as Go's `c.ok()` check gives). -/
noncomputable def conn.LocalAddr.impl : val :=
  λ: "c" <>, ![model.Addr] (StructFieldRef model.conn go!"laddr" "c")

/-- D18. `(*conn).RemoteAddr() Addr` (`net.go`): `c.fd.raddr`, as `LocalAddr`. -/
noncomputable def conn.RemoteAddr.impl : val :=
  λ: "c" <>, ![model.Addr] (StructFieldRef model.conn go!"raddr" "c")

/-- `(*TCPAddr).String() string` (`tcpsock.go`): made of the address's fields, which the model does
not explain: an arbitrary string. -/
noncomputable def TCPAddr.String.impl : val :=
  λ: "a" <>, ExternalOp Net.netExt.name "AnyString" #()

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

/-- No type of `net` is named `_`: goose takes every trusted name for a possible type too, and the
blank variables' name `_` is trusted (below), so it asks for an underlying type, which nothing
uses. -/
@[reducible] def «_».underlying : go.GoType := go.GoType.StructType []
>>>>>>> theirs

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
