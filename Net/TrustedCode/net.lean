/-
Trusted Go model of `net` (namespace of the generated package; project net of `etc/goose.py`,
`Net/Code/net.toml`), in terms of the net extension of `GooseLang.Ext.Net.Impl` (`Net.netExt`,
`ExternalOp Net.netExt.name "Read"`, ...), for any program whose extensions include it. linux/amd64,
Go 1.27.3 (`etc/goose.py`'s `GO_TOOLCHAIN`; the Go code cited is `$GOROOT/src/net` and
`internal/poll` of that release). The main tree's `net` (`Code.net`, names only) must not be in the
same import closure. The design is `notes/net-tcp.md` (v3: `notes/net-tcp-v3-plan.md`).

**Connections.** Go's `TCPConn` is `struct{ conn }` (`tcpsock.go`), translated as it is, so that
`*TCPConn`'s method set is Go's (`conn`'s methods promoted); `conn` (`net.go`) holds `fd *netFD`,
the socket. `conn` is trusted, with the layout `struct{ id uint64; laddr Addr; raddr Addr; net
string }` (`conn.underlying`): `id` is the extension's id of the connection end the socket is,
`laddr` and `raddr` its `netFD`'s addresses (`fd.laddr`, `fd.raddr`), `net` its network (`fd.net`:
`"tcp"` or `"tcp4"`, D23, the `Net` of its errors). The other fields of Go's `netFD` (the poller)
are not observable to code outside `net`. A `*TCPConn` is made only by
`Dial.impl`, `DialTimeout.impl` and `TCPListener.Accept.impl`, so its `id` is an id the extension
returned, except in a zero-value `TCPConn` (`var c net.TCPConn`, which Go code outside `net` can
make): its `id` is 0, which names no connection end (`Impl.lean`, "Handles"), and each method checks
for it first, as Go's check `c.ok()` (`c.fd != nil`: `net.go`, `tcpsock.go`), and returns what Go's
does: the bare `syscall.EINVAL` (`model.einval`; `TestZeroValues`), or `nil` for `LocalAddr` and
`RemoteAddr`.

**Listeners.** `TCPListener` (`struct{ fd *netFD; lc ListenConfig }` in Go) is trusted, with the
layout `struct{ lid uint64; addr Addr; net string }`, the extension's id of the listener on this
node, its `netFD`'s `laddr` and its network (`fd.net`, which the connections it accepts get: Go's
`netFD.accept`, `newFD(..., fd.net)`). A zero-value `TCPListener`'s `lid` is 0, which names no listener: `Accept` and
`Close` check for it, as Go's `l.ok()`, and return `syscall.EINVAL` (`TestZeroValues`); `Addr`
panics, as Go's (a nil dereference).

**Addresses (D18).** A connection's two addresses and a listener's address are non-nil `*TCPAddr`s
made when it is (`model.anyTCPAddr`: a new `TCPAddr` whose `IP`, `Port` and `Zone` are arbitrary)
and returned as they are by `LocalAddr`, `RemoteAddr`, `Addr`: Go's `netFD.setAddr` stores them
once (`fd_unix.go`'s `dial` and `accept`: `laddr` from `getsockname`, `raddr` from `getpeername`
or the dialed address, each a new `*TCPAddr` from `sockaddrToTCP`, non-nil for an IPv4 socket:
Linux's `inet_getname` does not fail on a connected or bound socket; Go's comment in
`tcpsock_posix.go` that a socket may come with a `nil` `raddr` "under certain unknown conditions"
concerns `sockaddrToTCP` of an unknown family, not an IPv4 socket), and the getters return the
stored values (`net.go`, `tcpsock.go`). Their values are not modeled: arbitrary. `TCPAddr.String`
is arbitrary too (`AnyString`).

**Errors (D14).** Go's errors here are `*OpError{Op, Net, Source, Addr, Err}` (translated, with
`Unwrap`), and `io.EOF` unwrapped for a read at the end. `Op` and the addresses are Go's for each
operation (`net.go`, `tcpsock.go`, `dial.go`: the end's `laddr` and `raddr` for `Read`, `Write`,
`Close`, `CloseWrite`; `nil` and `laddr` for the deadlines; `nil` and the listener's `laddr` for
`Accept` and the listener's `Close`; `nil` and the resolved address, a `*TCPAddr` the model makes
arbitrary, for `Dial` and `Listen`); `Net` is the network (D23: the call's for `Dial` and `Listen`,
the connection's or listener's `net` otherwise). `Err` is the extension's kind's
(`model.kindErr`): `closed` gives `poll.ErrNetClosing` (`errNetClosing{}`, an empty struct, so its
value is that of its only value: `model.closedErr`), which `poll.FD` returns for an operation on a
closing fd (`errClosing`) and `net.ErrClosed` is (`errClosed = poll.ErrNetClosing`); `timeout`
gives the value of `poll.ErrDeadlineExceeded` (`&DeadlineExceededError{}`, read from its variable:
`os.ErrDeadlineExceeded` is the same pointer), which `poll.FD` returns for an expired deadline;
`sys` gives `&os.SyscallError{Syscall: name, Err: syscall.Errno(n)}` with `n` an arbitrary nonzero
word (`model.sysErr`), the system call's error as `wrapSyscallError` and `os.NewSyscallError` wrap
it (`error_posix.go`, `fd_unix.go`): `name` is Go's, `"read"`, `"write"` (`readSyscallName`,
`writeSyscallName`), `"shutdown"` (`CloseWrite`), `"accept4"` (`poll.FD.Accept`'s `errcall`), and
arbitrary for `Dial` and `Listen` (`"connect"`, `"getsockopt"`, `"socket"`, `"bind"`, `"listen"`,
`"setsockopt"`: whichever call failed). `Error()` is `Op`, then an arbitrary string, `": "` and
another (`AnyString`: Go's message is made of the network's, the addresses' and the system error's
strings); `Timeout()` and `Temporary()` are `false` for
`errNetClosing` (its methods), `true` for `*DeadlineExceededError` and `*timeoutError` (theirs),
and arbitrary otherwise: an `Errno`'s are `true` for `ETIMEDOUT`, `EAGAIN` (and `Temporary` for
`EINTR`, `EMFILE`, `ENFILE`, and in `Accept` `ECONNRESET`, `ECONNABORTED`: `isConnError`), which a
`sys` error may be (`syscall_unix.go`, `net.go`). The bare `Errno` that `Accept` and `Dial` return
when registering a new socket with the poller fails (`ENOMEM`, `ENOSPC` of `epoll_ctl`) is not
modeled (D12).

**Faithfulness.** Each model is the Go function with its system calls replaced by the extension's
operations (`Impl.lean` says why each operation's outcomes are those of Linux). Go's `Read` loops
over `read(2)` (`poll.FD`, `EINTR` and `EAGAIN` handled by the poller) and returns once at least one
byte has arrived, as the extension's `Read` does; Go's `Write` loops over `write(2)` until every
byte is in the kernel or an error, and so does its model (`conn.Write.impl`, `model.writeLoop`),
each `write(2)` with its wait one step of the extension (D2). Less defined than Go (a panic, or
stuck, which a proof must rule out): a network other than `"tcp"` and `"tcp4"` (D23); a nil receiver (stuck: a nil
dereference; Go panics too for a nil `*TCPConn`, and returns `EINVAL` for a nil `*TCPListener`:
v3.2 review, N1); a call of the extension with an argument it cannot use
(`Impl.lean`, D22: a `Listen` or `Dial` of an invalid address, D13, D20).
-/
module

public import Perennial.Golang.Defn
public import Perennial.Code.io
public import Perennial.Code.time
public import Code.os
public import Code.internal.poll
public import GooseLang.Ext.Net.Impl
public import GooseLang.Ext.Udp.Impl

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace net

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

section code
variable [GooseExts] [GoGlobalContext]

@[reducible] def model.Addr : go.GoType := go.GoType.Named go!"net.Addr" []

/-- `conn` (`net.go`): the id of the socket's connection end, its addresses and its network, in
place of `fd *netFD` (the module docstring says why the other fields of `netFD` are not needed). -/
@[reducible] def conn.fieldsUnsealed : List go.field_decl :=
  [go.field_decl.FieldDecl go!"id" go.uint64, go.field_decl.FieldDecl go!"laddr" model.Addr,
    go.field_decl.FieldDecl go!"raddr" model.Addr, go.field_decl.FieldDecl go!"net" go.string]

/-- The fields, sealed (as goose seals a translated struct's), unfolded by `conn.equals_unfold`
in the struct semantics. -/
@[irreducible] def conn.fields : List go.field_decl := conn.fieldsUnsealed

instance conn.equals_unfold : EqualsUnfold conn.fields conn.fieldsUnsealed :=
  ⟨by unfold conn.fields; rfl⟩

@[reducible] def conn.underlying : go.GoType :=
  go.GoType.StructType conn.fields

/-- `TCPConn` (`tcpsock.go`): Go's `struct{ conn }`, the embedded `conn` (whose methods it
promotes). Trusted only so that its instances are stated with the trusted `conn`'s
(`Net/ManualProof/net.lean`). -/
@[reducible] def TCPConn.fieldsUnsealed : List go.field_decl :=
  [go.field_decl.EmbeddedField go!"conn" (go.GoType.Named go!"net.conn" [])]

/-- The fields, sealed (as goose seals a translated struct's), unfolded by `TCPConn.equals_unfold`
in the struct semantics. -/
@[irreducible] def TCPConn.fields : List go.field_decl := TCPConn.fieldsUnsealed

instance TCPConn.equals_unfold : EqualsUnfold TCPConn.fields TCPConn.fieldsUnsealed :=
  ⟨by unfold TCPConn.fields; rfl⟩

@[reducible] def TCPConn.underlying : go.GoType :=
  go.GoType.StructType TCPConn.fields

/-- `TCPListener` (`tcpsock.go`): the id of the listener, its address and its network, in place of
`fd *netFD` and `lc` (the field named `lid`, not `id`: a layout like `conn.underlying` would make
the two structs' type representations ambiguous). -/
@[reducible] def TCPListener.fieldsUnsealed : List go.field_decl :=
  [go.field_decl.FieldDecl go!"lid" go.uint64, go.field_decl.FieldDecl go!"addr" model.Addr,
    go.field_decl.FieldDecl go!"net" go.string]

/-- The fields, sealed (as goose seals a translated struct's), unfolded by `TCPListener.equals_unfold`
in the struct semantics. -/
@[irreducible] def TCPListener.fields : List go.field_decl := TCPListener.fieldsUnsealed

instance TCPListener.equals_unfold : EqualsUnfold TCPListener.fields TCPListener.fieldsUnsealed :=
  ⟨by unfold TCPListener.fields; rfl⟩

@[reducible] def TCPListener.underlying : go.GoType :=
  go.GoType.StructType TCPListener.fields

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

attribute [instance] FieldAssumptions.conn_get_id FieldAssumptions.conn_set_id
  FieldAssumptions.conn_get_laddr FieldAssumptions.conn_set_laddr
  FieldAssumptions.conn_get_raddr FieldAssumptions.conn_set_raddr
  FieldAssumptions.conn_get_net FieldAssumptions.conn_set_net
  FieldAssumptions.net_get_conn FieldAssumptions.net_set_conn
  FieldAssumptions.lis_get_id FieldAssumptions.lis_set_id
  FieldAssumptions.lis_get_addr FieldAssumptions.lis_set_addr
  FieldAssumptions.lis_get_net FieldAssumptions.lis_set_net

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
  λ: <>, Convert internal.poll.errNetClosing.ty go.error
    (GoZeroVal internal.poll.errNetClosing.ty #())

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
...), which goose resolves through the embedded field `conn` (`UDPConn.TypeAssumptions.
ptr_Close_unfold`) that this layout does not have. A program over UDP keeps its socket until its
process ends (U7: the kernel closes it). Only the network `"udp4"` is modeled (an IPv4 socket, `AF_INET`: Go's
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
Addr: laddr, Err: <the system call's error>}` with a nil `*UDPConn` (the failing call's name
arbitrary: `"socket"`, `"setsockopt"`, `"bind"`). A `nil` `laddr` (Go: a wildcard address with a
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
        (model.udpKindErr (Snd "r") (ExternalOp Udp.udpExt.name "AnyString" #())))
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
addr, nil)` with `addr` a new `*UDPAddr` (the sender's in Go; arbitrary here, U10); or `(0, addr,
&OpError{Op: "read", Net, Source: laddr, Addr: nil, Err})` (Go returns its non-nil, zero `addr`
then: arbitrary here too), `Err` the kind's (`"recvfrom"` for a system call's). A zero `UDPConn`:
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
    else (#(W64 0), model.anyUDPAddr #(),
      model.udpErr #(go!"read") "c" #GoInterface.nil (Snd "r") #(go!"recvfrom"))

/-- No type of `net` is named `_`: goose takes every trusted name for a possible type too, and the
blank variables' name `_` is trusted (below), so it asks for an underlying type, which nothing
uses. -/
@[reducible] def «_».underlying : go.GoType := go.GoType.StructType []

/-! ## The package variables

`net`'s variables (the DNS configuration, the error values, the test hooks, the cgo
functions, ...) are trusted, each initializer a model that does nothing: the variable is not
allocated, so code that loads it is stuck (has no proof), where Go reads its value. The models
give a proof less than Go does, never more. But `errClosed` (`net.go`: `errClosed =
poll.ErrNetClosing`), which holds that value (an empty struct's only value, so no read of `poll`'s
variable is needed), and the translated `ErrClosed` (`ErrClosed error = errClosed`) and
`errTimeout` (`&timeoutError{}`). -/

/-- `errClosed = poll.ErrNetClosing` (of type `poll.errNetClosing`). -/
noncomputable def errClosed.init : val :=
  λ: <>,
    go.GlobalAlloc go!"net.errClosed" internal.poll.errNetClosing.ty #() ;;
    GlobalVarAddr go!"net.errClosed" #() <-[internal.poll.errNetClosing.ty]
      GoZeroVal internal.poll.errNetClosing.ty #()

def rfc6724policyTable.init : val := λ: <>, #()
def confVal.init : val := λ: <>, #()
def netdns.init : val := λ: <>, #()
def multipathtcp.init : val := λ: <>, #()
def errLameReferral.init : val := λ: <>, #()
def errCannotUnmarshalDNSMessage.init : val := λ: <>, #()
def errCannotMarshalDNSMessage.init : val := λ: <>, #()
def errServerMisbehaving.init : val := λ: <>, #()
def errInvalidDNSResponse.init : val := λ: <>, #()
def errNoAnswerFromDNSServer.init : val := λ: <>, #()
def errServerTemporarilyMisbehaving.init : val := λ: <>, #()
def netedns0.init : val := λ: <>, #()
def distantFuture.init : val := λ: <>, #()
def lookupOrderName.init : val := λ: <>, #()
def defaultNS.init : val := λ: <>, #()
def getHostname.init : val := λ: <>, #()
def testHookLookupIP.init : val := λ: <>, #()
def testPreHookSetKeepAlive.init : val := λ: <>, #()
def testHookSetKeepAlive.init : val := λ: <>, #()
def testHookStepTime.init : val := λ: <>, #()
def testHookCanceledDial.init : val := λ: <>, #()
def hostsFilePath.init : val := λ: <>, #()
def socketFunc.init : val := λ: <>, #()
def connectFunc.init : val := λ: <>, #()
def listenFunc.init : val := λ: <>, #()
def getsockoptIntFunc.init : val := λ: <>, #()
def errInvalidInterface.init : val := λ: <>, #()
def errInvalidInterfaceIndex.init : val := λ: <>, #()
def errInvalidInterfaceName.init : val := λ: <>, #()
def errNoSuchInterface.init : val := λ: <>, #()
def errNoSuchMulticastInterface.init : val := λ: <>, #()
def flagNames.init : val := λ: <>, #()
def zoneCache.init : val := λ: <>, #()
def v4InV6Prefix.init : val := λ: <>, #()
def IPv4bcast.init : val := λ: <>, #()
def IPv4allsys.init : val := λ: <>, #()
def IPv4allrouter.init : val := λ: <>, #()
def IPv4zero.init : val := λ: <>, #()
def IPv6zero.init : val := λ: <>, #()
def IPv6unspecified.init : val := λ: <>, #()
def IPv6loopback.init : val := λ: <>, #()
def IPv6interfacelocalallnodes.init : val := λ: <>, #()
def IPv6linklocalallnodes.init : val := λ: <>, #()
def IPv6linklocalallrouters.init : val := λ: <>, #()
def classAMask.init : val := λ: <>, #()
def classBMask.init : val := λ: <>, #()
def classCMask.init : val := λ: <>, #()
def protocols.init : val := λ: <>, #()
def services.init : val := λ: <>, #()
def DefaultResolver.init : val := λ: <>, #()
def «_».init : val := λ: <>, #()
def errMalformedDNSRecordsDetail.init : val := λ: <>, #()
def readProtocolsOnce.init : val := λ: <>, #()
def errNoSuitableAddress.init : val := λ: <>, #()
def errMissingAddress.init : val := λ: <>, #()
def errCanceled.init : val := λ: <>, #()
def ErrWriteToConnected.init : val := λ: <>, #()
def aLongTimeAgo.init : val := λ: <>, #()
def noDeadline.init : val := λ: <>, #()
def noCancel.init : val := λ: <>, #()
def errNoSuchHost.init : val := λ: <>, #()
def errUnknownPort.init : val := λ: <>, #()
def pollSplice.init : val := λ: <>, #()
def _cgo_77133bf98b3a_C2func_getaddrinfo.init : val := λ: <>, #()
def _cgo_77133bf98b3a_C2func_getnameinfo.init : val := λ: <>, #()
def _cgo_77133bf98b3a_Cfunc_free.init : val := λ: <>, #()
def _cgo_77133bf98b3a_Cfunc_freeaddrinfo.init : val := λ: <>, #()
def _cgo_77133bf98b3a_Cfunc_gai_strerror.init : val := λ: <>, #()
def _cgo_77133bf98b3a_Cfunc_getaddrinfo.init : val := λ: <>, #()
def _cgo_77133bf98b3a_Cfunc_getnameinfo.init : val := λ: <>, #()
def _cgo_77133bf98b3a_Cfunc_res_search.init : val := λ: <>, #()
def _cgo_77133bf98b3a_Cfunc__Cmalloc.init : val := λ: <>, #()

end code

end net

end Perennial
