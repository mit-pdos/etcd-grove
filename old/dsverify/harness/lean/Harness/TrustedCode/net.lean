/-
Trusted Go model of `net` (namespace of the generated package `Harness.Code.net`, translated
with `Harness/Code/net.toml`), in terms of the TCP extension `netConnExt`
(`Harness/GooseLang/Ext/NetConn/Impl.lean`; `ExternalOp netConnExt.name "Read" ...`), for any
program whose extensions include it. Go 1.27.3, linux/amd64, `CGO_ENABLED=0`. Part of the trust
base; reviewed with the extension (`notes/harness-m2a.md`).

**Types.** Go's `TCPConn` is `struct{ conn }` and `conn` is `struct{ fd *netFD }`; both are
translated as they are, so a `net.Conn` from `Dial` or `Accept` is a `*TCPConn` in an interface,
as in Go, and the `*TCPConn` methods are goose's promotions to `*conn`'s. `netFD` and
`TCPListener` are trusted, with the layouts below: `netFD`'s `pfd poll.FD` (the socket) becomes
the extension's ids (`id`, `side`); `laddr` and `raddr` keep Go's names and roles (the
addresses `LocalAddr`/`RemoteAddr` return, the same values on every call, as Go's fields). Go's
other `netFD` fields (`family`, `sotype`, `isConnected`, `net`) are unexported and constant for
a TCP socket (`net` is `"tcp"`). `TCPListener`'s `lc ListenConfig` is dropped (unexported, used
only by `File` and `SyscallConn`, not modeled).

**Faithfulness.** Each model is Go's method (cited by file) with the `poll.FD` call replaced by
the extension's operation, and with Go's error values reproduced as follows.
* `io.EOF` is returned unwrapped, as Go does (`net.go`, `conn.Read`: `err != io.EOF`).
* Every other error is `&OpError{Op, Net: "tcp", Source, Addr, Err}` with Go's `Op` (`"read"`,
  `"write"`, `"close"`, `"set"`, `"accept"`, `"listen"`, `"dial"`) and Go's `Source`/`Addr`
  (the end's `laddr`/`raddr` for connection operations, `nil` and the listener's address for
  `Accept` and `Close` of a listener, `nil` and an arbitrary address or `nil` for `Listen` and
  `Dial`).
* `Err` is a value of the model-only type `net#model.connError` (`model.connError`); for a closed
  end it is the one pointer `net.ErrClosed` is set to (`ErrClosed.init`), so
  `errors.Is(err, net.ErrClosed)` matches Go. Go's are
  `os.ErrDeadlineExceeded` (a timeout), `net.ErrClosed` (a closed end), an `*os.SyscallError`
  around an `Errno` (a break or a failure). The model's `Timeout()`/`Temporary()` agree with
  Go's: true/true for a timeout, false/false for a closed end, arbitrary for a break or a
  failure (`ETIMEDOUT` is a timeout, `ECONNRESET` is not). What differs is only the dynamic
  type, observable only through `os`, `syscall` or `internal/poll` values, which the lab cannot
  prove code against (their initializers are axiomatized), and `Error()`, which is an arbitrary
  string (over-approximating Go's message).
* `OpError.Timeout`/`Temporary` are Go's bodies without the `*os.SyscallError` unwrapping (no
  model error is one); `OpError.Error` and `TCPAddr.String` return arbitrary strings.
* Addresses are arbitrary `*TCPAddr`s (any IP bytes, port and zone), fixed per socket. A
  connection's (from `Dial` or `Accept`) local and remote ones are never `nil` (a claim): Go's
  remote one is the peer address of `accept` or `connect`, else `getpeername`'s, else the dialed
  `*TCPAddr` (`fd_unix.go`, `sock_posix.go`), never `nil`; its local one is `getsockname`'s, whose
  error Go ignores (a `nil` `Addr`), but which Linux's `inet_getname` (`peer = 0`) does not fail
  for an open TCP socket (only a security module's `socket_getsockname` hook could).
  A listener's (from `Listen`, the address `Addr` returns) is never `nil` either (a claim):
  Go's `listenStream` sets it to `getsockname`'s after `listen` (`sock_posix.go`, error
  ignored), and the same Linux argument applies to a bound socket. Its value is left arbitrary,
  not tied to the listened-on address: Go reports the kernel's bound address, which for a
  wildcard is not the node's IP (measured, Go 1.27.3, private netns: `":p"`, `"0.0.0.0:p"` and
  `"[::]:p"` all report `"[::]:p"`, with or without IPv6 enabled; `"tcp4"` would report
  `"0.0.0.0:p"`), and for a named host or port `0` is not the spelled string (`"localhost:0"`
  reports `"127.0.0.1:<chosen port>"`).
**Socket options** (`SetReadBuffer`, `SetWriteBuffer`, `SetKeepAlive`, `SetKeepAlivePeriod`;
kits/rabia-net): `nil` or an `*OpError` of `"set"` with Go's `Source` and `Addr`, whose `Err` is
the closed-end error or another failure, on any end and at any time (`model.setSockopt`). Go's
`setsockopt` fails for a closed end and otherwise only rarely (a security module's hook); the
model lets every call fail, an over-approximation. No state changes: buffer sizes and keep-alive
change nothing the model observes (time is not modeled).
**`"tcp4"`.** `Listen`, `Dial` and `DialTimeout` treat the network `"tcp4"` as `"tcp"`
(`model.tcpNetwork`): on the configured addresses, which are IPv4 literals (`"IP:port"`, the
statement's `NetConfig`), Go's `"tcp4"` and `"tcp"` sockets behave alike (both are `AF_INET`
sockets for an IPv4 literal; `"tcp4"` only rules out IPv6 addresses, which the configuration has
none of). What differs is the `Net` field of the model's `*OpError`s, `"tcp"` where Go's is
`"tcp4"` (visible only through the error's fields or `Error()`, which is arbitrary anyway).

The model is less defined than Go (stuck, `model.unsupported`) for a network other than `"tcp"`
and `"tcp4"`;
a `nil` receiver panics where Go returns `EINVAL`, a safe direction (the model has more panics).

**Package variables.** Every package-level variable of `net` but `ErrClosed` has a trusted
initializer that does nothing (`X.init`, below): the variable is never allocated, so any use of
it is stuck. In Go these initializers allocate error values, tables and hooks, none of which the
subset's methods use, and none of which can panic. A program that uses one of them
(`net.IPv4zero`) is not provable until that variable is translated. `ErrClosed` is modeled
(`ErrClosed.init`): servers stop an accept loop on `errors.Is(err, net.ErrClosed)`.
-/
module

public import Perennial.Golang.Defn
public import Perennial.Code.io
public import Perennial.TrustedCode.fmt
public import Harness.GooseLang.Ext.NetConn.Impl

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace net

open NetConn

/-- The model's `netFD` (`netFD.underlying`): the extension's ids of the socket (a connection id
and its end, or a listener id with `side` false), and the addresses. -/
structure netFD [GooseExts] where
  mk ::
  id' : w64
  side' : Bool
  laddr' : GoInterface
  raddr' : GoInterface

instance netFD.zero_val [GooseExts] : ZeroVal netFD :=
  ⟨netFD.mk zeroValDef zeroValDef zeroValDef zeroValDef⟩

/-- The model's `TCPListener` (`TCPListener.underlying`): its `netFD`. -/
structure TCPListener where
  mk ::
  fd' : Loc

instance TCPListener.zero_val : ZeroVal TCPListener := ⟨TCPListener.mk zeroValDef⟩

namespace model

/-- The model-only error type (`net#model.connError`; `#` cannot occur in a Go package path,
so no Go type has this name): the `Err` of every `OpError` the model returns. -/
structure connError where
  mk ::
  timeout' : Bool
  temporary' : Bool

instance connError.zero_val : ZeroVal connError := ⟨connError.mk zeroValDef zeroValDef⟩

end model

section code
variable [GooseExts] [GoGlobalContext]

/-! ### Types, as goose names them (their `.ty` is in `Harness.Code.net`, which imports this
file) -/

namespace model
@[reducible] def netFDTy : go.GoType := go.GoType.Named go!"net.netFD" []
@[reducible] def connTy : go.GoType := go.GoType.Named go!"net.conn" []
@[reducible] def TCPConnTy : go.GoType := go.GoType.Named go!"net.TCPConn" []
@[reducible] def TCPListenerTy : go.GoType := go.GoType.Named go!"net.TCPListener" []
@[reducible] def ConnTy : go.GoType := go.GoType.Named go!"net.Conn" []
@[reducible] def ListenerTy : go.GoType := go.GoType.Named go!"net.Listener" []
@[reducible] def AddrTy : go.GoType := go.GoType.Named go!"net.Addr" []
@[reducible] def TCPAddrTy : go.GoType := go.GoType.Named go!"net.TCPAddr" []
@[reducible] def IPTy : go.GoType := go.GoType.Named go!"net.IP" []
@[reducible] def OpErrorTy : go.GoType := go.GoType.Named go!"net.OpError" []
@[reducible] def timeoutTy : go.GoType := go.GoType.Named go!"net.timeout" []
@[reducible] def temporaryTy : go.GoType := go.GoType.Named go!"net.temporary" []
@[reducible] def timeTy : go.GoType := go.GoType.Named go!"time.Time" []
/-- The model-only error type's name (see `connError`). -/
@[reducible] def connErrorTy : go.GoType := go.GoType.Named go!"net#model.connError" []
end model

/-- `netFD` (`fd_posix.go`) as the model lays it out (see the module docstring). -/
@[reducible] def netFD.underlying : go.GoType :=
  go.GoType.StructType [go.field_decl.FieldDecl go!"id" go.uint64,
    go.field_decl.FieldDecl go!"side" go.bool,
    go.field_decl.FieldDecl go!"laddr" model.AddrTy,
    go.field_decl.FieldDecl go!"raddr" model.AddrTy]

/-- `TCPListener` (`tcpsock.go`) as the model lays it out: `struct{ fd *netFD }`. -/
@[reducible] def TCPListener.underlying : go.GoType :=
  go.GoType.StructType [go.field_decl.FieldDecl go!"fd" (go.GoType.PointerType model.netFDTy)]

namespace model

/-- The layout of `connError`. -/
@[reducible] def connError.underlying : go.GoType :=
  go.GoType.StructType [go.field_decl.FieldDecl go!"timeout" go.bool,
    go.field_decl.FieldDecl go!"temporary" go.bool]

/-! ### Helpers of the models (not Go functions) -/

/-- No step: the extension has no operation of this name. Where Go would do something the model
does not cover (another network than `"tcp"`), the model is stuck, so no program that gets there
is proved safe. -/
noncomputable def unsupported : val :=
  λ: <>, ExternalOp netConnExt.name "Unsupported" #()

/-- The network a `Listen` or `Dial` uses: `"tcp4"` is treated as `"tcp"` (see the module
docstring); any other string is returned as it is. -/
noncomputable def tcpNetwork : val :=
  λ: "network", if: "network" =⟨go.string⟩ #"tcp4" then #"tcp" else "network"

/-- An arbitrary boolean. -/
noncomputable def arbitraryBool : val :=
  λ: <>, ArbitraryInt =⟨go.uint64⟩ #(W64 0)

/-- A fresh `*TCPAddr` with an arbitrary IP (any bytes), port and zone, as a `net.Addr`. -/
noncomputable def arbitraryAddr : val :=
  λ: <>,
    Convert (go.GoType.PointerType TCPAddrTy) AddrTy
      (CompositeLiteral (go.GoType.PointerType TCPAddrTy) (LiteralValue [
        KeyedElement (some (KeyField go!"IP")) (ElementExpression IPTy
          (Convert (go.GoType.SliceType go.byte) IPTy
            (Convert go.string (go.GoType.SliceType go.byte) (fmt.arbitraryString #())))),
        KeyedElement (some (KeyField go!"Port")) (ElementExpression go.int ArbitraryInt),
        KeyedElement (some (KeyField go!"Zone")) (ElementExpression go.string
          (fmt.arbitraryString #()))]))

/-- `nil` or an arbitrary address (the `Addr` of a failed `Listen` or `Dial`: Go's resolved
address, or `nil` if resolution failed). -/
noncomputable def maybeAddr : val :=
  λ: <>, if: arbitraryBool #() then #GoInterface.nil else arbitraryAddr #()

/-- `&connError{timeout, temporary}` as an `error`. -/
noncomputable def connErr : val :=
  λ: "timeout" "temporary",
    Convert (go.GoType.PointerType connErrorTy) go.error
      (CompositeLiteral (go.GoType.PointerType connErrorTy) (LiteralValue [
        KeyedElement (some (KeyField go!"timeout")) (ElementExpression go.bool "timeout"),
        KeyedElement (some (KeyField go!"temporary")) (ElementExpression go.bool "temporary")]))

/-- The `Err` of a result code other than success and `io.EOF` (see the module docstring); for a
closed end, the model's `poll.ErrNetClosing` (`ErrClosed.init`), as Go's `poll.FD` returns
`ErrNetClosing`, which `net.ErrClosed` is set to. -/
noncomputable def codeErr : val :=
  λ: "code",
    if: "code" =⟨go.uint64⟩ #errTimeout then connErr #true #true
    else if: "code" =⟨go.uint64⟩ #errClosed then
      ![go.error] (GlobalVarAddr go!"net#model.errNetClosing" #())
    else connErr (arbitraryBool #()) (arbitraryBool #())

/-- `&OpError{Op: op, Net: "tcp", Source: src, Addr: addr, Err: err}` as an `error`. -/
noncomputable def opError : val :=
  λ: "op" "src" "addr" "err",
    Convert (go.GoType.PointerType OpErrorTy) go.error
      (CompositeLiteral (go.GoType.PointerType OpErrorTy) (LiteralValue [
        KeyedElement (some (KeyField go!"Op")) (ElementExpression go.string "op"),
        KeyedElement (some (KeyField go!"Net")) (ElementExpression go.string #"tcp"),
        KeyedElement (some (KeyField go!"Source")) (ElementExpression AddrTy "src"),
        KeyedElement (some (KeyField go!"Addr")) (ElementExpression AddrTy "addr"),
        KeyedElement (some (KeyField go!"Err")) (ElementExpression go.error "err")]))

/-- `&netFD{id, side, laddr, raddr}`. -/
noncomputable def newFD : val :=
  λ: "id" "side" "laddr" "raddr",
    CompositeLiteral (go.GoType.PointerType netFDTy) (LiteralValue [
      KeyedElement (some (KeyField go!"id")) (ElementExpression go.uint64 "id"),
      KeyedElement (some (KeyField go!"side")) (ElementExpression go.bool "side"),
      KeyedElement (some (KeyField go!"laddr")) (ElementExpression AddrTy "laddr"),
      KeyedElement (some (KeyField go!"raddr")) (ElementExpression AddrTy "raddr")])

/-- `&TCPConn{conn{fd}}` as a `net.Conn` (`newTCPConn`, `tcpsock_posix.go`, without its
`setNoDelay` and keep-alive calls, which do not change what the subset observes). -/
noncomputable def newConn : val :=
  λ: "fd",
    Convert (go.GoType.PointerType TCPConnTy) ConnTy
      (CompositeLiteral (go.GoType.PointerType TCPConnTy) (LiteralValue [
        KeyedElement (some (KeyField go!"conn")) (ElementExpression connTy
          (CompositeLiteral connTy (LiteralValue [
            KeyedElement (some (KeyField go!"fd"))
              (ElementExpression (go.GoType.PointerType netFDTy) "fd")])))]))

/-- `c.fd`, for a `*conn` `c`. -/
noncomputable def fdOf : val :=
  λ: "c", ![go.GoType.PointerType netFDTy] (StructFieldRef connTy go!"fd" "c")

/-- The id and side of a `*netFD`, as the extension takes them: `(id, side)`. -/
noncomputable def idSide : val :=
  λ: "fd", (![go.uint64] (StructFieldRef netFDTy go!"id" "fd"),
            ![go.bool] (StructFieldRef netFDTy go!"side" "fd"))

/-- The `error` of a connection operation `op` on `fd` with result `code`: `nil`, `io.EOF`, or
`&OpError{op, "tcp", fd.laddr, fd.raddr, codeErr code}`. -/
noncomputable def connResult : val :=
  λ: "fd" "op" "code",
    if: "code" =⟨go.uint64⟩ #errNone then #GoInterface.nil
    else if: "code" =⟨go.uint64⟩ #errEOF then ![go.error] (GlobalVarAddr io.EOF #())
    else opError "op" (![AddrTy] (StructFieldRef netFDTy go!"laddr" "fd"))
      (![AddrTy] (StructFieldRef netFDTy go!"raddr" "fd")) (codeErr "code")

/-- `c.fd.setDeadline(t, mode)` with `which` (0 both, 1 read, 2 write) as the extension takes
it; `t`'s deadline is set unless `t` is the zero `time.Time` (Go's `IsZero` is true for every
`Time` equal to it; a `Time` with the zero instant but another location counts as set here,
which only allows more timeouts). Go: `&OpError{Op: "set", ...}` on error (`net.go`). -/
noncomputable def setDeadline : val :=
  λ: "c" "which" "t",
    let: "fd" := fdOf "c" in
    let: "set" := (if: "t" =⟨timeTy⟩ GoZeroVal timeTy #() then #false else #true) in
    let: "code" := ExternalOp netConnExt.name "SetDeadline"
      (Fst (idSide "fd"), (Snd (idSide "fd"), ("which", "set"))) in
    connResult "fd" #"set" "code"

/-- A socket option set on the end `fd` (`SetReadBuffer`, `SetWriteBuffer`, `SetKeepAlive`,
`SetKeepAlivePeriod`): `nil`, or `&OpError{Op: "set", Net: "tcp", Source: src, Addr: addr, Err}`
whose `Err` is the closed-end error or any other failure. Go's `setsockopt` on Linux fails for a
closed end (`net.ErrClosed`, as here) and otherwise only in rare cases (a security module's hook,
memory); the model lets every call fail, on any end, which covers both (an over-approximation, the
safe direction). It changes no state: an option does not touch the streams, and nothing the
model observes depends on buffer sizes or keep-alive (time is not modeled). -/
noncomputable def setSockopt : val :=
  λ: "src" "addr",
    if: arbitraryBool #() then #GoInterface.nil
    else opError #"set" "src" "addr"
      (codeErr (if: arbitraryBool #() then #errClosed else #errFail))

/-- `(*connError).Error`: an arbitrary string. -/
noncomputable def connError.Error.impl : val := λ: "e" <>, fmt.arbitraryString #()
/-- `(*connError).Timeout`. -/
noncomputable def connError.Timeout.impl : val :=
  λ: "e" <>, ![go.bool] (StructFieldRef connErrorTy go!"timeout" "e")
/-- `(*connError).Temporary`. -/
noncomputable def connError.Temporary.impl : val :=
  λ: "e" <>, ![go.bool] (StructFieldRef connErrorTy go!"temporary" "e")

end model

/-! ### Functions -/

/-- `Listen(network, address string) (Listener, error)` (`dial.go`, `tcpsock_posix.go`): the
extension's `Listen`; a `*TCPListener` whose `netFD` has the listener id and an arbitrary local
address. -/
noncomputable def Listen.impl : val :=
  λ: "network" "address",
    let: "network" := model.tcpNetwork "network" in
    if: "network" ≠⟨go.string⟩ #"tcp" then model.unsupported #() else
    let: "r" := ExternalOp netConnExt.name "Listen" "address" in
    if: Snd "r" =⟨go.uint64⟩ #errNone then
      (let: "fd" := model.newFD (Fst "r") #false (model.arbitraryAddr #()) #GoInterface.nil in
       (Convert (go.GoType.PointerType model.TCPListenerTy) model.ListenerTy
          (CompositeLiteral (go.GoType.PointerType model.TCPListenerTy) (LiteralValue [
            KeyedElement (some (KeyField go!"fd"))
              (ElementExpression (go.GoType.PointerType model.netFDTy) "fd")])),
        #GoInterface.nil))
    else (#GoInterface.nil,
      model.opError #"listen" #GoInterface.nil (model.maybeAddr #()) (model.codeErr (Snd "r")))

/-- `Dial(network, address string) (Conn, error)` (`dial.go`): the extension's `Dial`; the
dialer's end, as a `*TCPConn`, with arbitrary local and remote addresses. -/
noncomputable def Dial.impl : val :=
  λ: "network" "address",
    let: "network" := model.tcpNetwork "network" in
    if: "network" ≠⟨go.string⟩ #"tcp" then model.unsupported #() else
    let: "r" := ExternalOp netConnExt.name "Dial" "address" in
    if: Snd "r" =⟨go.uint64⟩ #errNone then
      (model.newConn (model.newFD (Fst "r") #false (model.arbitraryAddr #())
        (model.arbitraryAddr #())), #GoInterface.nil)
    else (#GoInterface.nil,
      model.opError #"dial" #GoInterface.nil (model.maybeAddr #()) (model.codeErr (Snd "r")))

/-- `DialTimeout(network, address string, timeout time.Duration) (Conn, error)`: `Dial`; the
timeout is one more reason a dial may fail, which `Dial` already allows, including a failure
after the handshake finished, which leaves a connection for the listener's `Accept`
(`Conn.abandoned`) [netsem: DialTimeoutAccepted]. -/
noncomputable def DialTimeout.impl : val :=
  λ: "network" "address" "timeout", Dial.impl "network" "address"

/-! ### `*TCPListener` -/

/-- `(*TCPListener).Accept() (Conn, error)` (`tcpsock.go`): the extension's `Accept`; the
acceptor's end, as a `*TCPConn`; an error is `&OpError{"accept", "tcp", nil, l.fd.laddr, _}`. -/
noncomputable def TCPListener.Accept.impl : val :=
  λ: "l" <>,
    let: "fd" := ![go.GoType.PointerType model.netFDTy]
      (StructFieldRef model.TCPListenerTy go!"fd" "l") in
    let: "r" := ExternalOp netConnExt.name "Accept"
      (![go.uint64] (StructFieldRef model.netFDTy go!"id" "fd")) in
    if: Snd "r" =⟨go.uint64⟩ #errNone then
      (model.newConn (model.newFD (Fst "r") #true (model.arbitraryAddr #())
        (model.arbitraryAddr #())), #GoInterface.nil)
    else (#GoInterface.nil, model.opError #"accept" #GoInterface.nil
      (![model.AddrTy] (StructFieldRef model.netFDTy go!"laddr" "fd")) (model.codeErr (Snd "r")))

/-- `(*TCPListener).Close() error`: the extension's `CloseListener`. -/
noncomputable def TCPListener.Close.impl : val :=
  λ: "l" <>,
    let: "fd" := ![go.GoType.PointerType model.netFDTy]
      (StructFieldRef model.TCPListenerTy go!"fd" "l") in
    let: "code" := ExternalOp netConnExt.name "CloseListener"
      (![go.uint64] (StructFieldRef model.netFDTy go!"id" "fd")) in
    if: "code" =⟨go.uint64⟩ #errNone then #GoInterface.nil
    else model.opError #"close" #GoInterface.nil
      (![model.AddrTy] (StructFieldRef model.netFDTy go!"laddr" "fd")) (model.codeErr "code")

/-- `(*TCPListener).Addr() Addr`: `l.fd.laddr`. -/
noncomputable def TCPListener.Addr.impl : val :=
  λ: "l" <>,
    ![model.AddrTy] (StructFieldRef model.netFDTy go!"laddr"
      (![go.GoType.PointerType model.netFDTy] (StructFieldRef model.TCPListenerTy go!"fd" "l")))

/-! ### `*conn` (promoted to `*TCPConn`) -/

/-- `(*conn).Read(b []byte) (int, error)` (`net.go`; `poll.FD.Read`): the extension's `Read`
of at most `len(b)` bytes, copied into `b`. -/
noncomputable def conn.Read.impl : val :=
  λ: "c" "b",
    let: "fd" := model.fdOf "c" in
    let: "r" := ExternalOp netConnExt.name "Read"
      (Fst (model.idSide "fd"), (Snd (model.idSide "fd"),
        Convert go.int go.uint64 ((FuncResolve go.len [go.GoType.SliceType go.byte]) #() "b"))) in
    let: "n" := (FuncResolve go.copy [go.GoType.SliceType go.byte]) #() "b"
      (Convert go.string (go.GoType.SliceType go.byte) (Fst "r")) in
    ("n", model.connResult "fd" #"read" (Snd "r"))

/-- `(*conn).Write(b []byte) (int, error)` (`net.go`; `poll.FD.Write`): the extension's `Write`
of `b`'s bytes (as a string). The count is what the kernel took, also with an error (a
timeout, the end closed by another goroutine meanwhile, a break): `WriteOutcome`. -/
noncomputable def conn.Write.impl : val :=
  λ: "c" "b",
    let: "fd" := model.fdOf "c" in
    let: "r" := ExternalOp netConnExt.name "Write"
      (Fst (model.idSide "fd"), (Snd (model.idSide "fd"),
        Convert (go.GoType.SliceType go.byte) go.string "b")) in
    (Convert go.uint64 go.int (Fst "r"), model.connResult "fd" #"write" (Snd "r"))

/-- `(*conn).Close() error` (`net.go`): the extension's `Close`. -/
noncomputable def conn.Close.impl : val :=
  λ: "c" <>,
    let: "fd" := model.fdOf "c" in
    model.connResult "fd" #"close" (ExternalOp netConnExt.name "Close" (model.idSide "fd"))

/-- `(*conn).LocalAddr() Addr`: `c.fd.laddr`. -/
noncomputable def conn.LocalAddr.impl : val :=
  λ: "c" <>, ![model.AddrTy] (StructFieldRef model.netFDTy go!"laddr" (model.fdOf "c"))

/-- `(*conn).RemoteAddr() Addr`: `c.fd.raddr`. -/
noncomputable def conn.RemoteAddr.impl : val :=
  λ: "c" <>, ![model.AddrTy] (StructFieldRef model.netFDTy go!"raddr" (model.fdOf "c"))

/-- `(*conn).SetDeadline(t time.Time) error`. -/
noncomputable def conn.SetDeadline.impl : val :=
  λ: "c" "t", model.setDeadline "c" #(W64 0) "t"
/-- `(*conn).SetReadDeadline(t time.Time) error`. -/
noncomputable def conn.SetReadDeadline.impl : val :=
  λ: "c" "t", model.setDeadline "c" #(W64 1) "t"
/-- `(*conn).SetWriteDeadline(t time.Time) error`. -/
noncomputable def conn.SetWriteDeadline.impl : val :=
  λ: "c" "t", model.setDeadline "c" #(W64 2) "t"

/-- `(*conn).SetReadBuffer(bytes int) error` (`net.go`): `setSockopt` with Go's error fields,
`Source: nil, Addr: c.fd.laddr`. -/
noncomputable def conn.SetReadBuffer.impl : val :=
  λ: "c" "bytes", model.setSockopt #GoInterface.nil
    (![model.AddrTy] (StructFieldRef model.netFDTy go!"laddr" (model.fdOf "c")))
/-- `(*conn).SetWriteBuffer(bytes int) error` (`net.go`): as `SetReadBuffer`. -/
noncomputable def conn.SetWriteBuffer.impl : val :=
  λ: "c" "bytes", model.setSockopt #GoInterface.nil
    (![model.AddrTy] (StructFieldRef model.netFDTy go!"laddr" (model.fdOf "c")))

/-! ### `*TCPConn` -/

/-- `(*TCPConn).SetKeepAlive(keepalive bool) error` (`tcpsock.go`): `setSockopt` with Go's error
fields, `Source: c.fd.laddr, Addr: c.fd.raddr`. -/
noncomputable def TCPConn.SetKeepAlive.impl : val :=
  λ: "c" "keepalive",
    let: "fd" := model.fdOf (StructFieldRef model.TCPConnTy go!"conn" "c") in
    model.setSockopt (![model.AddrTy] (StructFieldRef model.netFDTy go!"laddr" "fd"))
      (![model.AddrTy] (StructFieldRef model.netFDTy go!"raddr" "fd"))
/-- `(*TCPConn).SetKeepAlivePeriod(d time.Duration) error` (`tcpsock.go`): as `SetKeepAlive` (Go
returns `nil` at once for `d < 0`, which the model's `nil` outcome covers). -/
noncomputable def TCPConn.SetKeepAlivePeriod.impl : val :=
  λ: "c" "d",
    let: "fd" := model.fdOf (StructFieldRef model.TCPConnTy go!"conn" "c") in
    model.setSockopt (![model.AddrTy] (StructFieldRef model.netFDTy go!"laddr" "fd"))
      (![model.AddrTy] (StructFieldRef model.netFDTy go!"raddr" "fd"))

/-! ### Errors and addresses -/

/-- `(*OpError).Error() string`: an arbitrary string (Go formats the fields). -/
noncomputable def OpError.Error.impl : val := λ: "e" <>, fmt.arbitraryString #()

/-- `(*OpError).Timeout() bool` (`net.go`): `e.Err`'s `Timeout()` if it has one. Go first
unwraps an `*os.SyscallError`; no error the model makes is one. -/
noncomputable def OpError.Timeout.impl : val :=
  λ: "e" <>,
    let: "p" := TypeAssert2 model.timeoutTy
      (![go.error] (StructFieldRef model.OpErrorTy go!"Err" "e")) in
    if: Snd "p" then MethodResolve model.timeoutTy go!"Timeout" (Fst "p") #() else #false

/-- `(*OpError).Temporary() bool` (`net.go`): `e.Err`'s `Temporary()` if it has one. Go first
treats `ECONNRESET`/`ECONNABORTED` from `accept` as temporary and unwraps an
`*os.SyscallError`; the model's failures have an arbitrary `Temporary()`, which covers both. -/
noncomputable def OpError.Temporary.impl : val :=
  λ: "e" <>,
    let: "p" := TypeAssert2 model.temporaryTy
      (![go.error] (StructFieldRef model.OpErrorTy go!"Err" "e")) in
    if: Snd "p" then MethodResolve model.temporaryTy go!"Temporary" (Fst "p") #() else #false

/-- `(*TCPAddr).String() string` (`tcpsock.go`): an arbitrary string. The claim: Go's returns
(no panic, no loop) for every receiver: `"<nil>"` for a `nil` one, else
`JoinHostPort(ipEmptyString(a.IP)[+"%"+a.Zone], strconv.Itoa(a.Port))`, where `IP.String` handles
every length (`"?"` + hex for one other than 4 or 16 bytes). Not translated: `IP.String` goes
through `IP.appendTo` and `net/netip`, `hexString` reads the package table `hexDigit` (whose
initializer the model does not run), `JoinHostPort` calls `internal/bytealg` (assembly), and
`strconv` is names-only. -/
noncomputable def TCPAddr.String.impl : val := λ: "a" <>, fmt.arbitraryString #()

/-! ### Package variables: trusted initializers that do nothing (module docstring) -/

noncomputable def DefaultResolver.init : val := λ: <>, #()
/-- `net.ErrClosed`: Go sets it to `poll.ErrNetClosing`, a value of the unexported type
`poll.errNetClosing` (`Timeout()` and `Temporary()` false), and `poll.FD` returns
`ErrNetClosing` for a closed end. The model allocates one model-only error,
`&connError{false, false}`, keeps it in a model-only variable `net#model.errNetClosing` (the
model's `poll.ErrNetClosing`; `#` cannot occur in a Go name), and sets `net.ErrClosed` to it.
`codeErr` returns it for a closed end, so `errors.Is(err, net.ErrClosed)` holds for the errors
of Go's closed-end cases and no other, as in Go (`harness/netsem/err_closed.go`): `errors.Is`
compares the pointers and unwraps the `*OpError` through its translated `Unwrap`. A program
that assigns `net.ErrClosed` changes the variable only, as in Go. -/
noncomputable def ErrClosed.init : val :=
  λ: <>,
    go.GlobalAlloc go!"net#model.errNetClosing" go.error #() ;;
    GlobalVarAddr go!"net#model.errNetClosing" #() <-[go.error] model.connErr #false #false ;;
    go.GlobalAlloc go!"net.ErrClosed" go.error #() ;;
    GlobalVarAddr go!"net.ErrClosed" #() <-[go.error]
      ![go.error] (GlobalVarAddr go!"net#model.errNetClosing" #())
noncomputable def ErrWriteToConnected.init : val := λ: <>, #()
noncomputable def IPv4allrouter.init : val := λ: <>, #()
noncomputable def IPv4allsys.init : val := λ: <>, #()
noncomputable def IPv4bcast.init : val := λ: <>, #()
noncomputable def IPv4zero.init : val := λ: <>, #()
noncomputable def IPv6interfacelocalallnodes.init : val := λ: <>, #()
noncomputable def IPv6linklocalallnodes.init : val := λ: <>, #()
noncomputable def IPv6linklocalallrouters.init : val := λ: <>, #()
noncomputable def IPv6loopback.init : val := λ: <>, #()
noncomputable def IPv6unspecified.init : val := λ: <>, #()
noncomputable def IPv6zero.init : val := λ: <>, #()
noncomputable def aLongTimeAgo.init : val := λ: <>, #()
noncomputable def classAMask.init : val := λ: <>, #()
noncomputable def classBMask.init : val := λ: <>, #()
noncomputable def classCMask.init : val := λ: <>, #()
noncomputable def confVal.init : val := λ: <>, #()
noncomputable def connectFunc.init : val := λ: <>, #()
noncomputable def defaultNS.init : val := λ: <>, #()
noncomputable def distantFuture.init : val := λ: <>, #()
noncomputable def errCanceled.init : val := λ: <>, #()
noncomputable def errCannotMarshalDNSMessage.init : val := λ: <>, #()
noncomputable def errCannotUnmarshalDNSMessage.init : val := λ: <>, #()
noncomputable def errClosed.init : val := λ: <>, #()
noncomputable def errInvalidDNSResponse.init : val := λ: <>, #()
noncomputable def errInvalidInterface.init : val := λ: <>, #()
noncomputable def errInvalidInterfaceIndex.init : val := λ: <>, #()
noncomputable def errInvalidInterfaceName.init : val := λ: <>, #()
noncomputable def errLameReferral.init : val := λ: <>, #()
noncomputable def errMalformedDNSRecordsDetail.init : val := λ: <>, #()
noncomputable def errMissingAddress.init : val := λ: <>, #()
noncomputable def errNoAnswerFromDNSServer.init : val := λ: <>, #()
noncomputable def errNoSuchHost.init : val := λ: <>, #()
noncomputable def errNoSuchInterface.init : val := λ: <>, #()
noncomputable def errNoSuchMulticastInterface.init : val := λ: <>, #()
noncomputable def errNoSuitableAddress.init : val := λ: <>, #()
noncomputable def errServerMisbehaving.init : val := λ: <>, #()
noncomputable def errServerTemporarilyMisbehaving.init : val := λ: <>, #()
noncomputable def errTimeout.init : val := λ: <>, #()
noncomputable def errUnknownPort.init : val := λ: <>, #()
noncomputable def flagNames.init : val := λ: <>, #()
noncomputable def getHostname.init : val := λ: <>, #()
noncomputable def getsockoptIntFunc.init : val := λ: <>, #()
noncomputable def hostsFilePath.init : val := λ: <>, #()
noncomputable def listenFunc.init : val := λ: <>, #()
noncomputable def lookupOrderName.init : val := λ: <>, #()
noncomputable def multipathtcp.init : val := λ: <>, #()
noncomputable def netdns.init : val := λ: <>, #()
noncomputable def netedns0.init : val := λ: <>, #()
noncomputable def noCancel.init : val := λ: <>, #()
noncomputable def noDeadline.init : val := λ: <>, #()
noncomputable def pollSplice.init : val := λ: <>, #()
noncomputable def protocols.init : val := λ: <>, #()
noncomputable def readProtocolsOnce.init : val := λ: <>, #()
noncomputable def rfc6724policyTable.init : val := λ: <>, #()
noncomputable def services.init : val := λ: <>, #()
noncomputable def socketFunc.init : val := λ: <>, #()
noncomputable def testHookCanceledDial.init : val := λ: <>, #()
noncomputable def testHookLookupIP.init : val := λ: <>, #()
noncomputable def testHookSetKeepAlive.init : val := λ: <>, #()
noncomputable def testHookStepTime.init : val := λ: <>, #()
noncomputable def testPreHookSetKeepAlive.init : val := λ: <>, #()
noncomputable def v4InV6Prefix.init : val := λ: <>, #()
noncomputable def zoneCache.init : val := λ: <>, #()
/-- The blank variables (`var _ Interface = ...`): nothing to allocate. -/
noncomputable def «_».init : val := λ: <>, #()

/-! ### What goose would emit for the trusted layouts and the model-only type

As `TypeAssumptions` for a translated type, stated by hand (goose cannot see the trusted layouts
or the model-only type). Part of the trust base. A program's statement takes `model.Assumptions`
beside its package's generated `Assumptions` (`Harness.SafeDist`'s nodes do). -/

/-- The struct-field facts of the trusted layouts, and the model-only error type's type and
methods. -/
class model.Assumptions [GoLocalContext] [GoSemanticsFunctions] : Prop where
  netFD_get_id : ∀ (x : netFD), go.IsGoStepPureDetTagged Tag.under
    (StructFieldGet netFD.underlying go!"id") #x (Val #(x.id'))
  netFD_get_side : ∀ (x : netFD), go.IsGoStepPureDetTagged Tag.under
    (StructFieldGet netFD.underlying go!"side") #x (Val #(x.side'))
  netFD_get_laddr : ∀ (x : netFD), go.IsGoStepPureDetTagged Tag.under
    (StructFieldGet netFD.underlying go!"laddr") #x (Val #(x.laddr'))
  netFD_get_raddr : ∀ (x : netFD), go.IsGoStepPureDetTagged Tag.under
    (StructFieldGet netFD.underlying go!"raddr") #x (Val #(x.raddr'))
  netFD_set_id : ∀ (x : netFD) (y : w64), go.IsGoStepPureDetTagged Tag.under
    (StructFieldSet netFD.underlying go!"id") (PairV #x #y) (Val #(({ x with id' := y } : netFD)))
  netFD_set_side : ∀ (x : netFD) (y : Bool), go.IsGoStepPureDetTagged Tag.under
    (StructFieldSet netFD.underlying go!"side") (PairV #x #y)
    (Val #(({ x with side' := y } : netFD)))
  netFD_set_laddr : ∀ (x : netFD) (y : GoInterface), go.IsGoStepPureDetTagged Tag.under
    (StructFieldSet netFD.underlying go!"laddr") (PairV #x #y)
    (Val #(({ x with laddr' := y } : netFD)))
  netFD_set_raddr : ∀ (x : netFD) (y : GoInterface), go.IsGoStepPureDetTagged Tag.under
    (StructFieldSet netFD.underlying go!"raddr") (PairV #x #y)
    (Val #(({ x with raddr' := y } : netFD)))
  TCPListener_get_fd : ∀ (x : TCPListener), go.IsGoStepPureDetTagged Tag.under
    (StructFieldGet TCPListener.underlying go!"fd") #x (Val #(x.fd'))
  TCPListener_set_fd : ∀ (x : TCPListener) (y : Loc), go.IsGoStepPureDetTagged Tag.under
    (StructFieldSet TCPListener.underlying go!"fd") (PairV #x #y)
    (Val #(({ x with fd' := y } : TCPListener)))
  connError_type_repr : go.TypeReprUnderlying model.connError.underlying model.connError
  connError_underlying : go.UnderlyingDirectedEq model.connErrorTy model.connError.underlying
  connError_get_timeout : ∀ (x : model.connError), go.IsGoStepPureDetTagged Tag.under
    (StructFieldGet model.connError.underlying go!"timeout") #x (Val #(x.timeout'))
  connError_get_temporary : ∀ (x : model.connError), go.IsGoStepPureDetTagged Tag.under
    (StructFieldGet model.connError.underlying go!"temporary") #x (Val #(x.temporary'))
  connError_set_timeout : ∀ (x : model.connError) (y : Bool), go.IsGoStepPureDetTagged Tag.under
    (StructFieldSet model.connError.underlying go!"timeout") (PairV #x #y)
    (Val #(({ x with timeout' := y } : model.connError)))
  connError_set_temporary : ∀ (x : model.connError) (y : Bool),
    go.IsGoStepPureDetTagged Tag.under
    (StructFieldSet model.connError.underlying go!"temporary") (PairV #x #y)
    (Val #(({ x with temporary' := y } : model.connError)))
  connError_method_set : go.MethodSetIs model.connErrorTy []
  connError_ptr_method_set : go.MethodSetIs (go.GoType.PointerType model.connErrorTy)
    [(go!"Error", some (go.signature.Signature [] false [go.string])),
     (go!"Temporary", some (go.signature.Signature [] false [go.bool])),
     (go!"Timeout", some (go.signature.Signature [] false [go.bool]))]
  connError_ptr_Error_unfold : MethodUnfold (go.GoType.PointerType model.connErrorTy) go!"Error"
    model.connError.Error.impl
  connError_ptr_Timeout_unfold : MethodUnfold (go.GoType.PointerType model.connErrorTy)
    go!"Timeout" model.connError.Timeout.impl
  connError_ptr_Temporary_unfold : MethodUnfold (go.GoType.PointerType model.connErrorTy)
    go!"Temporary" model.connError.Temporary.impl

end code

end net

end Perennial
