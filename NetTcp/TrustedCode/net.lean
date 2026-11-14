/-
Trusted Go model of `net` (namespace of the generated package; project nettcp of `etc/goose.py`,
`NetTcp/Code/net.toml`), in terms of the TCP extension of `GooseLang.Ext.Tcp.Impl` (`Tcp.tcpExt`,
`ExternalOp Tcp.tcpExt.name "Read"`, ...), for any program whose extensions include it. linux/amd64,
Go 1.27.3 (`etc/goose.py`'s `GO_TOOLCHAIN`). The main tree's `net` (`Code.net`, names only) must not
be in the same import closure. The design is `notes/net-tcp.md`.

**Connections.** Go's `TCPConn` is `struct{ conn }` (`tcpsock.go`), translated as it is, so that
`*TCPConn`'s method set is Go's (`conn`'s methods promoted); `conn` (`net.go`) holds `fd *netFD`,
the socket. `conn` is trusted, with the layout `struct{ id uint64 }` (`conn.underlying`): `id` is
the extension's id of the connection end the socket is. The other fields of Go's `netFD` (the
network name, the addresses, the poller) are not observable to code outside `net` but through
`LocalAddr`, `RemoteAddr` and the errors' fields, which are not modeled (below). A `*TCPConn` is
made only by `Dial.impl` and `TCPListener.Accept.impl`, so its `id` is an id the extension returned,
except in a zero-value `TCPConn` (`var c net.TCPConn`, which Go code outside `net` can make): its
`id` is 0, which names no connection end (`Impl.lean`, "Handles"), so its methods are stuck.

**Listeners.** `TCPListener` (`struct{ fd *netFD; lc ListenConfig }` in Go) is trusted, with the
layout `struct{ lid uint64 }`, the extension's id of the listener on this node.

**Errors.** Go's errors here are `*OpError{Op, Net, Source, Addr, Err}`, `Err` the system's error
(an `*os.SyscallError` around an `Errno`, `poll.ErrNetClosing`, `os.ErrDeadlineExceeded`, ...), and
`io.EOF` unwrapped for a read at the end. The model returns `io.EOF` as Go does, and for any other
failure an `*OpError` whose layout is trusted as `struct{ Op string; Net string }`: `Op` is Go's
(`"read"`, `"write"`, `"close"`, `"dial"`, `"listen"`, `"accept"`, `"set"`) and `Net` is `"tcp"`.
`Source`, `Addr` and `Err` are not modeled: a program that reads them is stuck (no such field), and
so is one that calls `Unwrap` (not modeled), so `errors.Is(err, net.ErrClosed)` is stuck. `Error`,
`Timeout` and `Temporary` return arbitrary values (the extension's `AnyString`, `AnyBool`): Go's
depend on the system's error, which the model does not explain, and any of them is possible for
some failure.

**Faithfulness.** Each model is the Go function with its system calls replaced by the extension's
operations (`Impl.lean` says why each operation's outcomes are those of Linux). Go's `Read` and
`Write` loop over `read(2)`/`write(2)` (`poll.FD`, `EINTR` and `EAGAIN` handled by the poller): a
`Read` returns once at least one byte has arrived, a `Write` once every byte is in the kernel or on
an error, as the extension's operations do. Less defined than Go (a panic, which a proof must rule
out): a network other than `"tcp"`; a nil receiver (a nil dereference, where Go returns `EINVAL`).
-/
module

public import Perennial.Golang.Defn
public import Perennial.Code.io
public import Perennial.Code.time
public import GooseLang.Ext.Tcp.Impl

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace net

/-- The model's `conn` (`conn.underlying`): the id of the connection end. -/
structure conn where
  mk ::
  id' : w64

instance conn.zero_val : ZeroVal conn := ⟨conn.mk zeroValDef⟩

/-- `TCPConn` (`struct{ conn }`, as Go's). -/
structure TCPConn where
  mk ::
  conn' : conn

instance TCPConn.zero_val : ZeroVal TCPConn := ⟨TCPConn.mk zeroValDef⟩

/-- The model's `TCPListener` (`TCPListener.underlying`): the id of the listener. -/
structure TCPListener where
  mk ::
  id' : w64

instance TCPListener.zero_val : ZeroVal TCPListener := ⟨TCPListener.mk zeroValDef⟩

/-- The model's `OpError` (`OpError.underlying`): the operation and the network. -/
structure OpError where
  mk ::
  Op' : GoString
  Net' : GoString

instance OpError.zero_val : ZeroVal OpError := ⟨OpError.mk zeroValDef zeroValDef⟩

section code
variable [GooseExts] [GoGlobalContext]

/-- `conn` (`net.go`): the id of the socket's connection end, in place of `fd *netFD` (the module
docstring says why the other fields of `netFD` are not needed). -/
@[reducible] def conn.fieldsUnsealed : List go.field_decl :=
  [go.field_decl.FieldDecl go!"id" go.uint64]

/-- The fields, sealed (as goose seals a translated struct's), unfolded by `conn.equals_unfold`
in the struct semantics. -/
@[irreducible] def conn.fields : List go.field_decl := conn.fieldsUnsealed

instance conn.equals_unfold : EqualsUnfold conn.fields conn.fieldsUnsealed :=
  ⟨by unfold conn.fields; rfl⟩

@[reducible] def conn.underlying : go.GoType :=
  go.GoType.StructType conn.fields

/-- `TCPConn` (`tcpsock.go`): Go's `struct{ conn }`, the embedded `conn` (whose methods it
promotes). Trusted only so that its instances are stated with the trusted `conn`'s
(`NetTcp/ManualProof/net.lean`). -/
@[reducible] def TCPConn.fieldsUnsealed : List go.field_decl :=
  [go.field_decl.EmbeddedField go!"conn" (go.GoType.Named go!"net.conn" [])]

/-- The fields, sealed (as goose seals a translated struct's), unfolded by `TCPConn.equals_unfold`
in the struct semantics. -/
@[irreducible] def TCPConn.fields : List go.field_decl := TCPConn.fieldsUnsealed

instance TCPConn.equals_unfold : EqualsUnfold TCPConn.fields TCPConn.fieldsUnsealed :=
  ⟨by unfold TCPConn.fields; rfl⟩

@[reducible] def TCPConn.underlying : go.GoType :=
  go.GoType.StructType TCPConn.fields

/-- `TCPListener` (`tcpsock.go`): the id of the listener, in place of `fd *netFD` and `lc` (the field
named `lid`, not `id`: a layout equal to `conn.underlying` would make the two structs' type
representations ambiguous). -/
@[reducible] def TCPListener.fieldsUnsealed : List go.field_decl :=
  [go.field_decl.FieldDecl go!"lid" go.uint64]

/-- The fields, sealed (as goose seals a translated struct's), unfolded by `TCPListener.equals_unfold`
in the struct semantics. -/
@[irreducible] def TCPListener.fields : List go.field_decl := TCPListener.fieldsUnsealed

instance TCPListener.equals_unfold : EqualsUnfold TCPListener.fields TCPListener.fieldsUnsealed :=
  ⟨by unfold TCPListener.fields; rfl⟩

@[reducible] def TCPListener.underlying : go.GoType :=
  go.GoType.StructType TCPListener.fields

/-- `OpError` (`net.go`): `Op` and `Net` only (the module docstring says why). -/
@[reducible] def OpError.fieldsUnsealed : List go.field_decl :=
  [go.field_decl.FieldDecl go!"Op" go.string,
    go.field_decl.FieldDecl go!"Net" go.string]

/-- The fields, sealed (as goose seals a translated struct's), unfolded by `OpError.equals_unfold`
in the struct semantics. -/
@[irreducible] def OpError.fields : List go.field_decl := OpError.fieldsUnsealed

instance OpError.equals_unfold : EqualsUnfold OpError.fields OpError.fieldsUnsealed :=
  ⟨by unfold OpError.fields; rfl⟩

@[reducible] def OpError.underlying : go.GoType :=
  go.GoType.StructType OpError.fields

/-- The struct-field facts goose emits for every translated struct, stated by hand for the trusted
layouts `conn.underlying`, `TCPConn.underlying`, `TCPListener.underlying` and
`OpError.underlying`, of which goose emits
none (as `os.file.FieldAssumptions`). Specs that need them take them as an instance hypothesis.
Part of the trust base. -/
class FieldAssumptions [GoLocalContext] [GoSemanticsFunctions] : Prop where
  conn_get_id : ∀ (x : conn), go.IsGoStepPureDetTagged Tag.under
    (StructFieldGet conn.underlying go!"id") #x (Val #(x.id'))
  conn_set_id : ∀ (x : conn) (y : w64), go.IsGoStepPureDetTagged Tag.under
    (StructFieldSet conn.underlying go!"id") (PairV #x #y) (Val #(({ x with id' := y } : conn)))
  tcp_get_conn : ∀ (x : TCPConn), go.IsGoStepPureDetTagged Tag.under
    (StructFieldGet TCPConn.underlying go!"conn") #x (Val #(x.conn'))
  tcp_set_conn : ∀ (x : TCPConn) (y : conn), go.IsGoStepPureDetTagged Tag.under
    (StructFieldSet TCPConn.underlying go!"conn") (PairV #x #y)
    (Val #(({ x with conn' := y } : TCPConn)))
  lis_get_id : ∀ (x : TCPListener), go.IsGoStepPureDetTagged Tag.under
    (StructFieldGet TCPListener.underlying go!"lid") #x (Val #(x.id'))
  lis_set_id : ∀ (x : TCPListener) (y : w64), go.IsGoStepPureDetTagged Tag.under
    (StructFieldSet TCPListener.underlying go!"lid") (PairV #x #y)
    (Val #(({ x with id' := y } : TCPListener)))
  op_get_Op : ∀ (x : OpError), go.IsGoStepPureDetTagged Tag.under
    (StructFieldGet OpError.underlying go!"Op") #x (Val #(x.Op'))
  op_set_Op : ∀ (x : OpError) (y : GoString), go.IsGoStepPureDetTagged Tag.under
    (StructFieldSet OpError.underlying go!"Op") (PairV #x #y)
    (Val #(({ x with Op' := y } : OpError)))
  op_get_Net : ∀ (x : OpError), go.IsGoStepPureDetTagged Tag.under
    (StructFieldGet OpError.underlying go!"Net") #x (Val #(x.Net'))
  op_set_Net : ∀ (x : OpError) (y : GoString), go.IsGoStepPureDetTagged Tag.under
    (StructFieldSet OpError.underlying go!"Net") (PairV #x #y)
    (Val #(({ x with Net' := y } : OpError)))

attribute [instance] FieldAssumptions.conn_get_id FieldAssumptions.conn_set_id
  FieldAssumptions.tcp_get_conn FieldAssumptions.tcp_set_conn
  FieldAssumptions.lis_get_id FieldAssumptions.lis_set_id
  FieldAssumptions.op_get_Op FieldAssumptions.op_set_Op
  FieldAssumptions.op_get_Net FieldAssumptions.op_set_Net

/-! The types as goose names them (their `.ty` is in `Code.net`, which imports this file), and
helpers of the models (not Go functions). -/

@[reducible] def model.conn : go.GoType := go.GoType.Named go!"net.conn" []
@[reducible] def model.TCPConn : go.GoType := go.GoType.Named go!"net.TCPConn" []
@[reducible] def model.TCPListener : go.GoType := go.GoType.Named go!"net.TCPListener" []
@[reducible] def model.OpError : go.GoType := go.GoType.Named go!"net.OpError" []
@[reducible] def model.Conn : go.GoType := go.GoType.Named go!"net.Conn" []
@[reducible] def model.Listener : go.GoType := go.GoType.Named go!"net.Listener" []

/-- `&OpError{Op: op, Net: "tcp"}` as an `error`. -/
noncomputable def model.opError : val :=
  λ: "op",
    let: "pe" := GoAlloc model.OpError (GoZeroVal model.OpError #()) in
    StructFieldRef model.OpError go!"Op" "pe" <-[go.string] "op" ;;
    StructFieldRef model.OpError go!"Net" "pe" <-[go.string] #(go!"tcp") ;;
    Convert (go.PointerType model.OpError) go.error "pe"

/-- The id of the connection end of a `*conn`. -/
noncomputable def model.connId : val :=
  λ: "c", ![go.uint64] (StructFieldRef model.conn go!"id" "c")

/-- A new `*TCPConn` for the connection end `id`, as a `Conn`. -/
noncomputable def model.newConn : val :=
  λ: "id",
    let: "t" := GoAlloc model.TCPConn (GoZeroVal model.TCPConn #()) in
    StructFieldRef model.conn go!"id" (StructFieldRef model.TCPConn go!"conn" "t") <-[go.uint64]
      "id" ;;
    Convert (go.PointerType model.TCPConn) model.Conn "t"

/-- `Listen(network, address string) (Listener, error)` (`dial.go`): `ListenConfig.Listen` with
the zero `ListenConfig`, which for `"tcp"` resolves the address, then `socket(2)`, `setsockopt`
(`SO_REUSEADDR`), `bind(2)` and `listen(2)`: the extension's `Listen` of the address (stuck unless it
is one of the plan's, at this node's host: the model's resolution). A `*TCPListener` as a
`Listener`; an error is `&OpError{Op: "listen", ...}` with a nil `Listener`. -/
noncomputable def Listen.impl : val :=
  λ: "network" "address",
    if: "network" ≠⟨go.string⟩ #(go!"tcp") then Panic "net: Listen of a network but tcp not modelled"
    else
      let: "r" := ExternalOp Tcp.tcpExt.name "Listen" "address" in
      if: Snd "r" then
        let: "l" := GoAlloc model.TCPListener (GoZeroVal model.TCPListener #()) in
        StructFieldRef model.TCPListener go!"lid" "l" <-[go.uint64] Fst "r" ;;
        (Convert (go.PointerType model.TCPListener) model.Listener "l", #GoInterface.nil)
      else (GoZeroVal model.Listener #(), model.opError #(go!"listen"))

/-- `Dial(network, address string) (Conn, error)` (`dial.go`): `Dialer.Dial` with the zero
`Dialer`, which for `"tcp"` resolves the address, then `socket(2)` and `connect(2)` (waiting for
the handshake): the extension's `Dial` (stuck unless the address is one of the plan's). A `*TCPConn`
as a `Conn`; an error is `&OpError{Op: "dial", ...}` with a nil `Conn`. -/
noncomputable def Dial.impl : val :=
  λ: "network" "address",
    if: "network" ≠⟨go.string⟩ #(go!"tcp") then Panic "net: Dial of a network but tcp not modelled"
    else
      let: "r" := ExternalOp Tcp.tcpExt.name "Dial" "address" in
      if: Snd "r" then (model.newConn (Fst "r"), #GoInterface.nil)
      else (GoZeroVal model.Conn #(), model.opError #(go!"dial"))

/-- `(*TCPListener).Accept() (Conn, error)` (`tcpsock.go`, `tcpsock_posix.go`'s `accept`):
`accept4(2)` through the poller (waiting for a connection; `ECONNABORTED` retried): the extension's
`Accept`. A `*TCPConn` as a `Conn`; an error is `&OpError{Op: "accept", ...}`. -/
noncomputable def TCPListener.Accept.impl : val :=
  λ: "l" <>,
    let: "r" := ExternalOp Tcp.tcpExt.name "Accept"
      (![go.uint64] (StructFieldRef model.TCPListener go!"lid" "l")) in
    if: Snd "r" then (model.newConn (Fst "r"), #GoInterface.nil)
    else (GoZeroVal model.Conn #(), model.opError #(go!"accept"))

/-- `(*TCPListener).Close() error` (`tcpsock.go`): `close(2)` of the listening socket (a second
close is `ErrNetClosing`): the extension's `LisClose`. -/
noncomputable def TCPListener.Close.impl : val :=
  λ: "l" <>,
    if: ExternalOp Tcp.tcpExt.name "LisClose"
        (![go.uint64] (StructFieldRef model.TCPListener go!"lid" "l")) then #GoInterface.nil
    else model.opError #(go!"close")

/-- `(*conn).Read(b []byte) (int, error)` (`net.go`, `fd_posix.go`, `poll.FD.Read`): `read(2)`
through the poller, which waits for bytes; an empty `b` returns `0, nil` at once; `0` bytes read
from a non-empty `b` is `io.EOF`: the extension's `Read` of `len(b)`, the bytes copied into `b`. An
error is `&OpError{Op: "read", ...}` with `0` bytes. -/
noncomputable def conn.Read.impl : val :=
  λ: "c" "b",
    let: "r" := ExternalOp Tcp.tcpExt.name "Read"
      (model.connId "c", (FuncResolve go.len [go.GoType.SliceType go.byte]) #() "b") in
    if: Snd "r" =⟨go.uint64⟩ #(W64 0) then
      ((FuncResolve go.copy [go.GoType.SliceType go.byte]) #() "b"
        (Convert go.string (go.GoType.SliceType go.byte) (Fst "r")), #GoInterface.nil)
    else if: Snd "r" =⟨go.uint64⟩ #(W64 1) then (#(W64 0), ![go.error] (GlobalVarAddr io.EOF #()))
    else (#(W64 0), model.opError #(go!"read"))

/-- `(*conn).Write(b []byte) (int, error)` (`net.go`, `poll.FD.Write`): `write(2)` through the
poller, looping until every byte is written or an error: the extension's `Write` of `b`'s bytes.
An error is `&OpError{Op: "write", ...}` with the count written. -/
noncomputable def conn.Write.impl : val :=
  λ: "c" "b",
    let: "r" := ExternalOp Tcp.tcpExt.name "Write"
      (model.connId "c", Convert (go.GoType.SliceType go.byte) go.string "b") in
    if: Snd "r" then (Fst "r", #GoInterface.nil)
    else (Fst "r", model.opError #(go!"write"))

/-- `(*conn).Close() error` (`net.go`, `fd_posix.go`): `close(2)` of the socket (a second close
is `ErrNetClosing`): the extension's `Close`. -/
noncomputable def conn.Close.impl : val :=
  λ: "c" <>,
    if: ExternalOp Tcp.tcpExt.name "Close" (model.connId "c") then #GoInterface.nil
    else model.opError #(go!"close")

/-- `(*TCPConn).CloseWrite() error` (`tcpsock.go`): `shutdown(2)` with `SHUT_WR`: the
extension's `CloseWrite`. -/
noncomputable def TCPConn.CloseWrite.impl : val :=
  λ: "c" <>,
    if: ExternalOp Tcp.tcpExt.name "CloseWrite"
        (model.connId (StructFieldRef model.TCPConn go!"conn" "c")) then #GoInterface.nil
    else model.opError #(go!"close")

/-- The extension's `SetDeadline` of the deadlines of kind `kind` (`0` both, `1` read, `2` write)
of the end of `c` to the time `t`: `t`'s two words (`wall`, `ext`; the extension decides whether it
is Go's zero time, `Tcp.timeIsZero`), read through a copy of `t` (the cell is the model's, never
seen by the program). -/
noncomputable def model.setDeadline (kind : w64) : val :=
  λ: "c" "t",
    let: "tp" := GoAlloc time.Time.ty "t" in
    if: ExternalOp Tcp.tcpExt.name "SetDeadline"
        (model.connId "c", (#kind, (![go.uint64] (StructFieldRef time.Time.ty go!"wall" "tp"),
          ![go.int64] (StructFieldRef time.Time.ty go!"ext" "tp")))) then #GoInterface.nil
    else model.opError #(go!"set")

/-- `(*conn).SetDeadline(t time.Time) error` (`net.go`, `poll.FD.SetDeadline`): sets the read and
the write deadline with the poller, or clears them for the zero time (`ErrNetClosing` on a closed
socket): the extension's `SetDeadline` of both. -/
noncomputable def conn.SetDeadline.impl : val := model.setDeadline (W64 0)

/-- `(*conn).SetReadDeadline(t time.Time) error`: the read deadline only. -/
noncomputable def conn.SetReadDeadline.impl : val := model.setDeadline (W64 1)

/-- `(*conn).SetWriteDeadline(t time.Time) error`: the write deadline only. -/
noncomputable def conn.SetWriteDeadline.impl : val := model.setDeadline (W64 2)

/-- `(*OpError).Error() string` (`net.go`): Go's message names the operation, the addresses and
the system's error, which the model does not explain: an arbitrary string. -/
noncomputable def OpError.Error.impl : val :=
  λ: "e" <>, ExternalOp Tcp.tcpExt.name "AnyString" #()

/-- `(*OpError).Timeout() bool` (`net.go`): whether the system's error is a timeout, which the
model does not explain: an arbitrary answer. -/
noncomputable def OpError.Timeout.impl : val :=
  λ: "e" <>, ExternalOp Tcp.tcpExt.name "AnyBool" #()

/-- `(*OpError).Temporary() bool` (`net.go`): as `Timeout`. -/
noncomputable def OpError.Temporary.impl : val :=
  λ: "e" <>, ExternalOp Tcp.tcpExt.name "AnyBool" #()


/-- No type of `net` is named `_`: goose takes every trusted name for a possible type too, and the
blank variables' name `_` is trusted (below), so it asks for an underlying type, which nothing
uses. -/
@[reducible] def «_».underlying : go.GoType := go.GoType.StructType []

/-! ## The package variables

`net`'s variables (the DNS configuration, the error values, the test hooks, the cgo
functions, ...) are trusted, each initializer a model that does nothing: the variable is not
allocated, so code that loads it is stuck (has no proof), where Go reads its value. Neither the
models above nor the examples read any (`NetTcp/Code/net.toml`). The models give a proof less
than Go does, never more. -/

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
def errTimeout.init : val := λ: <>, #()
def errNoSuchHost.init : val := λ: <>, #()
def errUnknownPort.init : val := λ: <>, #()
def errClosed.init : val := λ: <>, #()
def ErrClosed.init : val := λ: <>, #()
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
