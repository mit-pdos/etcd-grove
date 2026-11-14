/-
The TCP extension of GooseLang [Trusted definitions!]: the semantics of Go's `net` package's TCP
connections, between the nodes of a distributed system (Perennial's `DistLang.lean`). Its
operations are the socket layer under `net`'s exported API; the trusted models of `net`'s
functions and methods (`NetTcp/TrustedCode/net.lean`) call them. Each decision below has a Go
example measured on Linux in `examples/net/semantics/` (its `doc.go` indexes them by the numbers
`D1`...), and an `example` of `GooseLang/Ext/Tcp/Tests.lean` (outside the trust base) that the
relations allow or exclude what the Go example shows; `notes/net-tcp.md` gives the reasons
(`notes/net-tcp-v3-plan.md` for v3, D14-D21).

**State: only what a program can observe.** The global state (`TcpGlobal`) is the deployment's
plan (each address the program may use, and the host that may listen at it) and the connections.
A connection (`TcpConn`) has the address it was dialed to, whether it has been accepted, two ends
(the dialer's `false`, the acceptor's `true`) and two directions. A direction (`TcpDir`, from one
end to the other) is the bytes written and not yet read, oldest first, and its status: `open` (the
writer may write more), `fin` (the writer shut its write side, by `Close` or `CloseWrite`) or
`cut` (the connection broke: a reset, a kernel timeout, the death of the peer's process or
machine). An end (`TcpEnd`) is whether `Close` was called on it, and whether a read deadline and a
write deadline are set. A node's local state (`TcpLocal`) is its host and its listeners (each an
address and whether it is open). Nothing records past operations.

**Handles.** A connection end is named by a 64-bit id, `2 c + s` for the connection `c` and the
side `s` (0 the dialer, 1 the acceptor); a listener by a 64-bit id of its node. An operation on an
id that names nothing is stuck. The trusted models pass the ids the extension returned, which a Go
program cannot forge (they are inside `net`'s unexported structs, and the heap does not survive a
crash), or the id 0 of a zero-value `TCPConn` or `TCPListener` (`var c net.TCPConn`), which names
nothing: no connection is numbered 0 and no listener has id 0 (`DialStep`, `ListenStep`), so a
program using a zero value is stuck, never proved (Go's methods return `EINVAL` there:
`TestZeroValues`).

**Each operation's outcome is a pure relation** on one end's state and one direction
(`ReadOutcome`, `WriteOutcome`, `CloseOutcome`, `CloseWriteOutcome`, `DeadlineOutcome`); the step
(`TcpStep`) looks the connection up, takes an outcome, and writes it back. Results are pairs, as
goose returns a Go function's results.

**Errors (D14).** Every failure has a kind (`TcpErr`), which the trusted models turn into Go's error
value: `closed`, an operation on the caller's own closed end or listener (Go's `poll.FD` refuses it
with `poll.ErrNetClosing`, which is `net.ErrClosed`); `timeout`, a deadline
(`poll.ErrDeadlineExceeded`, which is `os.ErrDeadlineExceeded`); `sys`, any other failure, a system
call's error (an `*os.SyscallError` around a `syscall.Errno`: `ECONNRESET`, `EPIPE`, `ETIMEDOUT`,
`ECONNREFUSED`, `EADDRINUSE`, `ENOTCONN`, ...). A failure's result is its kind's code
(`TcpErr.code`), success `0` (`errCode`).

* D1 `"Read"` of `n` bytes at an end, from the direction towards it (`ReadOutcome`): on a closed
  end, `closed`. Otherwise: `n = 0` returns nothing at once; else the first `k` unread bytes,
  `1 ≤ k ≤ n` (as many as arrived: any number); EOF once nothing is unread and the writer is done
  (`fin` or `cut`); after a cut, also a `sys` error; it waits while the direction is open and
  empty; with a read deadline set, a `timeout` that changes nothing (`ReadAvail`). And at any read,
  the connection may break: the direction becomes `cut`, keeping a prefix of its unread bytes,
  and the read answers as on the broken direction (bytes, EOF or an error). EOF does not say the
  writer finished cleanly: a cut that kept every byte reads as EOF, and that is what the death of
  the writer's process looks like (its kernel's FIN, or a reset whose error another call took).
  A read blocked when another goroutine closes the end returns `closed`: the read waits, the close
  steps, the read then steps on a closed end.
* D2 `"Write"` of `bs` at an end, into the direction from it (`WriteOutcome`): on a closed end,
  `closed`, writing nothing. Into a direction the end shut (`fin`): nothing written, a `sys` error
  (`EPIPE`), or `timeout` with a write deadline set (Go checks the deadline before `write(2)`).
  Into an open direction: all of `bs` appended; or a prefix of it, shorter (or nothing), appended,
  the connection broken (`cut`) and a `sys` error; or, with a write deadline set, a prefix,
  shorter (or nothing), appended and a `timeout`, the direction still open; or (D15) a prefix,
  shorter (or nothing), appended and `closed`, the direction still open: a `Write` blocked for
  buffer space returns what it wrote with `ErrNetClosing` when another goroutine closes the end
  (`poll.FD.Write`'s `waitWrite`), and is linearized just before that close, which it cannot see
  (`TestWriteCloseRace`). Into a cut direction: the bytes are discarded, with success or a failure
  of any kind (a `timeout` only with a write deadline), a prefix counted. Go's `Write` returns fewer
  bytes than asked only with an error (`poll.FD.Write` returns `nn, err` once `nn == len(p)`, `err`
  nil there); it may fail having written nothing even when asked for nothing (Go makes the system
  call for an empty buffer too, and the deadline check comes first: `TestEmptyWrite`).
* D3 `"Close"` of an end (`CloseOutcome`): `closed` if it is closed already; otherwise (D17) the
  end is closed and its direction, if open, becomes `fin`, with success: `poll.FD.Close` fails only
  when the fd is closing already (`increfAndClose`), and the system call's error is that of
  Linux's `close(2)` of a socket, which has none (`TestCloseTwice`, `TestCloseAfterReset`).
* D4 `"CloseWrite"` of an end (`CloseWriteOutcome`): `closed` if it is closed; otherwise its
  direction, if open, becomes `fin`, with success; or a `sys` error (`ENOTCONN`) that changes
  nothing.
* D5 `"SetDeadline"` of an end, for reads, writes or both, to a time (`DeadlineOutcome`): `closed`
  on a closed end; otherwise the deadline is set if the time is not Go's zero time (`timeIsZero`,
  Go's `Time.IsZero`) and cleared if it is. Deadline values are not modeled: with a deadline set,
  any operation of that kind may time out.
* D6 `"Listen"` of an address `a` (`ListenAt`, D21 for the wildcards): stuck unless `a` is in the
  plan with this node's host. A new open listener at `a`; or a `sys` failure, which is the only
  outcome if this node already has an open listener at `a` (`EADDRINUSE`).
* D7 `"Accept"` of a listener `l`: only `closed` once `l` is closed. Otherwise a connection dialed
  to `l`'s address and not yet accepted, now accepted; or a `sys` failure; or it waits. Pending
  connections belong to the address, not to a listener, because a node's step sees only its own
  local state and the network (Perennial's step relation): a `Dial` cannot see whether another node
  listens, and a crash cannot reset connections. So a connection dialed when no listener was open,
  or before the listening node's crash, may be accepted later: more than Linux, which refuses or
  resets it, an outcome the dialer sees as a failure or a cut, which the model also allows.
* D8 `"Dial"` of `a`: stuck unless `a` is in the plan. A new connection to `a`, not yet accepted,
  both ends fresh and both directions open and empty; or a `sys` failure (refused, unreachable);
  or (D16) a `sys` failure that leaves a connection to `a`, pending, whose dialer's end is closed
  and whose direction from it is `fin` and empty (`TcpConn.abandoned`): Go's `connect` gives up
  (a deadline, a cancelled context) and closes the socket after the kernel's handshake finished, so
  the listener's kernel has queued the connection and `Accept` returns it, reading EOF
  (`TestDialTimeoutAccepted`). For every dial (simplest, and sound: more than Linux).
* D9 `"LisClose"` of `l`: closes it, with success (D17, as D3); `closed` if it is closed already.
  Pending connections stay pending (D7).
* `"AnyBool"`, `"AnyString"`, `"AnyW64"`: an arbitrary value; `"AnyErrno"`: an arbitrary nonzero
  word (the parts of an error and of an address that the model does not explain: `OpError.Error`,
  the `syscall.Errno` of a `sys` error, a `TCPAddr`'s fields).

**Crashes** (D10, `crash`): a node's crash (or its process's exit, D11) leaves the network as it is
(DistLang's crash keeps the global state, and an extension's crash relation is node-local). Its
listeners are gone (`lis` empty), so the restarted node may listen at its addresses again. What
its peers see of its connections (a FIN, a reset, or nothing) is covered by cuts (D1, D2). The host
is kept.

**The deployment** (D13), which every theorem over this semantics assumes. *Well-formed plan
addresses* (D20, `Deploy.lean`'s `PlanWellFormed`, decidable, a premise of the theorems): each plan
string is the canonical spelling `a.b.c.d:p` of an IPv4 unicast address (not `0.0.0.0/8`, not
`224.0.0.0` and above) and a port outside Linux's default ephemeral range 32768-60999 (and not 0),
so that a `Dial` with no listener cannot connect to itself, and no two plan strings alias
(`TestAddressAliases`); `Listen` and `Dial` compare strings, as the kernel then does. *A closed
world* (stated in prose only): no process outside the system's nodes listens at, or dials, the
plan's addresses (an outside listener at a server's address would accept its clients:
`examples/axiomcx/tcp-squat`). *The target configuration*: Linux 7.0 with its default sysctls,
Go 1.27.3 (its listeners' default, MPTCP when available, behaves as TCP for every decision here),
measured in `examples/net/semantics/`.

**What is not modeled** (D12). Memory exhaustion in the kernel (`ENOMEM`/`ENOBUFS`: a failure of a
live connection that is not a cut, and the bare `Errno` of a failed `epoll_ctl` registration in
`Accept` or `Dial`), as the file extensions' allocation failures. Addresses are the plan's strings
and the wildcards of D21, compared as strings; `Listen` or `Dial` of any other string is stuck.
Port `0`, TLS, UDP, Unix sockets, the deadlines' values, keepalives, the listeners' deadlines: not
modeled (the methods are not modeled either, so a program calling them is stuck).

* D14 the error kinds (above).
* D15 the `Write`/`Close` race (D2).
* D16 abandoned dials (D8).
* D17 `Close` of an open end or listener succeeds (D3, D9).
* D18 addresses (`LocalAddr`, `RemoteAddr`, `TCPListener.Addr`): non-nil `*TCPAddr`s fixed at the
  connection's or listener's creation, otherwise arbitrary; in the Go heap, no state here
  (`NetTcp/TrustedCode/net.lean`).
* D19 `DialTimeout`: `"Dial"`; its model may turn a failure into a timeout (`net`'s `errTimeout`, or
  `poll.ErrDeadlineExceeded`: `NetTcp/TrustedCode/net.lean`), and D16 applies.
* D20 the plan's well-formedness (D13, `Deploy.lean`).
* D21 wildcard `Listen` (`ListenAt`): `":p"`, `"0.0.0.0:p"`, `"[::]:p"` (not themselves plan
  addresses) listen at the plan address with the port `p`, which must be at this node's host and
  the plan's only address with that port (stuck otherwise): on one machine a wildcard listener
  takes every local address with its port (`TestAddressAliases`, `TestWildcardListen`).
-/
module

public import Perennial.GooseLang.Lang

@[expose] public section

namespace Perennial

namespace Tcp

/-- The status of a direction of a connection. -/
inductive TcpStatus where
  /-- The writer may write more. -/
  | open
  /-- The writer shut its write side (`Close`, `CloseWrite`). -/
  | fin
  /-- The connection broke. -/
  | cut
deriving DecidableEq, Inhabited

/-- One direction of a connection: the bytes written and not yet read, oldest first, and its
status. -/
structure TcpDir where
  bytes : List w8
  status : TcpStatus
deriving DecidableEq, Inhabited

/-- An open, empty direction. -/
def TcpDir.fresh : TcpDir := ⟨[], .open⟩

/-- The state of one end of a connection. -/
structure TcpEnd where
  /-- `Close` was called on it. -/
  closed : Bool
  /-- A read deadline is set. -/
  rdl : Bool
  /-- A write deadline is set. -/
  wdl : Bool
deriving DecidableEq, Inhabited

/-- A fresh end. -/
def TcpEnd.fresh : TcpEnd := ⟨false, false, false⟩

/-- A connection: its address, whether it was accepted, its two ends (`false` the dialer, `true`
the acceptor) and its two directions. -/
structure TcpConn where
  addr : GoString
  accepted : Bool
  dEnd : TcpEnd
  aEnd : TcpEnd
  /-- From the dialer to the acceptor. -/
  up : TcpDir
  /-- From the acceptor to the dialer. -/
  down : TcpDir
deriving Inhabited

/-- A new connection to `a`. -/
def TcpConn.fresh (a : GoString) : TcpConn :=
  ⟨a, false, TcpEnd.fresh, TcpEnd.fresh, TcpDir.fresh, TcpDir.fresh⟩

/-- D16. The connection a failed dial of `a` may leave: pending, its dialer's end closed and its
direction from it shut and empty. -/
def TcpConn.abandoned (a : GoString) : TcpConn :=
  ⟨a, false, { TcpEnd.fresh with closed := true }, TcpEnd.fresh, ⟨[], .fin⟩, TcpDir.fresh⟩

/-- The state of the end `s` of `c`. -/
def TcpConn.endSt (c : TcpConn) : Bool → TcpEnd
  | false => c.dEnd
  | true => c.aEnd

/-- The direction from the end `s` of `c` (the one it writes). -/
def TcpConn.out (c : TcpConn) : Bool → TcpDir
  | false => c.up
  | true => c.down

/-- `c` with the state of its end `s` replaced. -/
def TcpConn.setEnd (c : TcpConn) : Bool → TcpEnd → TcpConn
  | false, st => { c with dEnd := st }
  | true, st => { c with aEnd := st }

/-- `c` with the direction from its end `s` replaced. -/
def TcpConn.setOut (c : TcpConn) : Bool → TcpDir → TcpConn
  | false, d => { c with up := d }
  | true, d => { c with down := d }

/-- The network. -/
structure TcpGlobal where
  /-- The deployment: each address the program may use, and the host that may listen at it. -/
  plan : GMap GoString GoString
  /-- Every connection dialed, by number. -/
  conns : GMap Nat TcpConn

instance : Inhabited TcpGlobal := ⟨⟨∅, ∅⟩⟩

/-- The network with the connection `c` set to `cn`. -/
def TcpGlobal.setConn (g : TcpGlobal) (c : Nat) (cn : TcpConn) : TcpGlobal :=
  { g with conns := g.conns.insert c cn }

/-- A node's state: its host, and its listeners (each its address and whether it is open). -/
structure TcpLocal where
  host : GoString
  lis : GMap w64 (GoString × Bool)

instance : Inhabited TcpLocal := ⟨⟨default, ∅⟩⟩

/-- The id of the end `s` of the connection `c`. -/
def endId (c : Nat) (s : Bool) : w64 := BitVec.ofNat 64 (2 * c + if s then 1 else 0)

/-- `e` is the end `s` of the connection `c`, in range. -/
def IsEnd (e : w64) (c : Nat) (s : Bool) : Prop :=
  2 * c + 1 < 2 ^ 64 ∧ e = endId c s

/-- The TCP extension. -/
@[reducible] def tcpExt : GooseExt where
  name := "net"
  Val := Empty
  LocalState := TcpLocal
  GlobalState := TcpGlobal

/-! ## Errors -/

/-- D14. The kind of a failure. -/
inductive TcpErr where
  /-- An operation on the caller's own closed end or listener (Go's `net.ErrClosed`). -/
  | closed
  /-- A deadline (Go's `os.ErrDeadlineExceeded`). -/
  | timeout
  /-- Any other failure: a system call's error. -/
  | sys
deriving DecidableEq, Inhabited

/-- The code of a failure's kind, as the trusted models receive it. -/
def TcpErr.code : TcpErr → w64
  | .closed => W64 1
  | .timeout => W64 2
  | .sys => W64 3

/-- The code of a result: `0` for success. -/
def errCode : Option TcpErr → w64
  | none => W64 0
  | some e => e.code

/-! ## The outcomes of the operations on an end -/

/-- What a read returns: bytes, EOF, an error; or it waits. -/
inductive ReadRes where
  | bytes (bs : List w8)
  | eof
  | err (e : TcpErr)
  | wait
deriving DecidableEq

/-- A read of `n > 0` bytes at an open end in state `st`, from the direction `d` as it is: its
result `r` and the direction after, `d'`. -/
def ReadAvail (st : TcpEnd) (d : TcpDir) (n : Nat) (r : ReadRes) (d' : TcpDir) : Prop :=
  -- the first `k` unread bytes
  (∃ k, 1 ≤ k ∧ k ≤ n ∧ k ≤ d.bytes.length ∧ r = .bytes (d.bytes.take k) ∧
    d' = { d with bytes := d.bytes.drop k }) ∨
  -- EOF: nothing unread, and the writer is done
  (d.bytes = [] ∧ d.status ≠ .open ∧ r = .eof ∧ d' = d) ∨
  -- it waits: nothing unread, and the writer may write more
  (d.bytes = [] ∧ d.status = .open ∧ r = .wait ∧ d' = d) ∨
  -- an error, once the connection broke
  (d.status = .cut ∧ r = .err .sys ∧ d' = d) ∨
  -- a timeout
  (st.rdl = true ∧ r = .err .timeout ∧ d' = d)

/-- D1. A read of `n` bytes at an end in state `st`, from the direction `d` towards it: its result
`r` and the direction after, `d'`. The connection may break at the read (a prefix of the unread
bytes survives, and the read answers as a read of the broken direction does: bytes, EOF or an
error), which is also how the death of the writer's process or machine shows. -/
def ReadOutcome (st : TcpEnd) (d : TcpDir) (n : Nat) (r : ReadRes) (d' : TcpDir) : Prop :=
  if st.closed then r = .err .closed ∧ d' = d
  else if n = 0 then r = .bytes [] ∧ d' = d
  else ReadAvail st d n r d' ∨
    -- the connection breaks now
    (∃ k, k ≤ d.bytes.length ∧ ReadAvail st ⟨d.bytes.take k, .cut⟩ n r d')

/-- D2, D15. A write of `bs` at an end in state `st`, into the direction `d` from it: the count `k`
it returns, its result `res` (`none` for success, else the failure's kind), and the direction
after, `d'`. A failure counts a prefix, shorter than `bs` (or nothing). -/
def WriteOutcome (st : TcpEnd) (d : TcpDir) (bs : List w8) (k : Nat) (res : Option TcpErr)
    (d' : TcpDir) : Prop :=
  if st.closed then k = 0 ∧ res = some .closed ∧ d' = d
  else match d.status with
  | .fin => k = 0 ∧ d' = d ∧ (res = some .sys ∨ (st.wdl = true ∧ res = some .timeout))
  | .cut =>
    -- discarded
    d' = d ∧ ((k = bs.length ∧ res = none) ∨
      ((k < bs.length ∨ k = 0) ∧
        (res = some .sys ∨ res = some .closed ∨ (st.wdl = true ∧ res = some .timeout))))
  | .open =>
    -- all of it
    (k = bs.length ∧ res = none ∧ d' = { d with bytes := d.bytes ++ bs }) ∨
    -- a prefix, and the connection breaks
    ((k < bs.length ∨ k = 0) ∧ res = some .sys ∧ d' = ⟨d.bytes ++ bs.take k, .cut⟩) ∨
    -- a prefix, and a timeout
    (st.wdl = true ∧ (k < bs.length ∨ k = 0) ∧ res = some .timeout ∧
      d' = { d with bytes := d.bytes ++ bs.take k }) ∨
    -- D15: a prefix, and the end closed by another goroutine (the close steps next)
    ((k < bs.length ∨ k = 0) ∧ res = some .closed ∧
      d' = { d with bytes := d.bytes ++ bs.take k })

/-- `d` shut by its writer, if it is open. -/
def TcpDir.shut (d : TcpDir) : TcpDir :=
  if d.status = .open then { d with status := .fin } else d

/-- D3, D17. A close of an end in state `st` whose direction is `d`: the result, the end's state
and the direction after. -/
def CloseOutcome (st : TcpEnd) (d : TcpDir) (res : Option TcpErr) (st' : TcpEnd) (d' : TcpDir) :
    Prop :=
  if st.closed then res = some .closed ∧ st' = st ∧ d' = d
  else res = none ∧ st' = { st with closed := true } ∧ d' = d.shut

/-- D4. A `CloseWrite` of an end in state `st` whose direction is `d`: the result and the
direction after. -/
def CloseWriteOutcome (st : TcpEnd) (d : TcpDir) (res : Option TcpErr) (d' : TcpDir) : Prop :=
  if st.closed then res = some .closed ∧ d' = d
  else (res = none ∧ d' = d.shut) ∨ (res = some .sys ∧ d' = d)

/-- D5. Setting the deadlines of kind `kind` (`0` both, `1` the read deadline, `2` the write
deadline) of an end in state `st` (`set`: the time is not zero): the result and the end's state
after. -/
def DeadlineOutcome (st : TcpEnd) (kind : w64) (set : Bool) (res : Option TcpErr) (st' : TcpEnd) :
    Prop :=
  if st.closed then res = some .closed ∧ st' = st
  else res = none ∧
    st' = { st with rdl := if kind = W64 2 then st.rdl else set,
                    wdl := if kind = W64 1 then st.wdl else set }

/-- Go's `Time.IsZero` (`time.go`): `t.wall == 0 && t.ext == 0`, of a `time.Time`'s two words. -/
def timeIsZero (wall ext : w64) : Bool := wall == 0 && ext == 0

/-! ## Addresses -/

/-- `a` with the prefix `p` removed, if it has it. -/
def stripPrefix : GoString → GoString → Option GoString
  | [], a => some a
  | _ :: _, [] => none
  | c :: p, x :: a => if c = x then stripPrefix p a else none

/-- D21. The port of a wildcard spelling `":p"`, `"0.0.0.0:p"` or `"[::]:p"`. -/
def wildPort (a : GoString) : Option GoString :=
  (stripPrefix go!":" a).or ((stripPrefix go!"0.0.0.0:" a).or (stripPrefix go!"[::]:" a))

/-- The port of `host:port` (what follows its first `:`). -/
def portOf (a : GoString) : Option GoString :=
  match a.dropWhile (fun c => decide (c ≠ (58 : w8))) with
  | [] => none
  | _ :: p => some p

/-- D6, D21. `Listen` of the string `a` by a node at `host` listens at the plan address `a0`: `a`
itself, in the plan at `host`; or, for a wildcard `a` with port `p` that is not itself in the
plan, the plan's only address with the port `p`, at `host` (so `a0` is unique:
`listenAt_unique`). -/
def ListenAt (plan : GMap GoString GoString) (host a a0 : GoString) : Prop :=
  plan !! a0 = some host ∧
  (a0 = a ∨ (plan !! a = none ∧ ∃ p, wildPort a = some p ∧ portOf a0 = some p ∧
    ∀ x, (plan !! x).isSome → portOf x = some p → x = a0))

/-! ## The step relation -/

section step
variable [GooseExts] [GoGlobalContext]

/-- The value of a read's result, as the trusted model takes it apart: the bytes and the code
(`0` bytes, `TcpErr.code` an error, `4` EOF). -/
def readRes (bs : List w8) (code : w64) : val := PairV (#bs) (#code)

/-- The value of a read's result `r` (`op` itself if it waits). -/
def ReadRes.toExpr (op : Expr) : ReadRes → Expr
  | .bytes bs => Val (readRes bs 0)
  | .eof => Val (readRes [] 4)
  | .err e => Val (readRes [] e.code)
  | .wait => op

/-- `"Read"` of `n` bytes at the end `s` of `c`. -/
def ReadStep (op : Expr) (c : Nat) (s : Bool) (n : w64) (g : TcpGlobal) (e' : Expr)
    (g' : TcpGlobal) : Prop :=
  ∃ cn r d', g.conns !! c = some cn ∧ ReadOutcome (cn.endSt s) (cn.out (!s)) n.toNat r d' ∧
    e' = r.toExpr op ∧ g' = g.setConn c (cn.setOut (!s) d')

/-- `"Write"` of `bs` at the end `s` of `c`. -/
def WriteStep (c : Nat) (s : Bool) (bs : List w8) (g : TcpGlobal) (e' : Expr) (g' : TcpGlobal) :
    Prop :=
  ∃ cn k res d', g.conns !! c = some cn ∧ WriteOutcome (cn.endSt s) (cn.out s) bs k res d' ∧
    e' = Val (PairV (#(BitVec.ofNat 64 k)) (#(errCode res))) ∧ g' = g.setConn c (cn.setOut s d')

/-- `"Close"` of the end `s` of `c`. -/
def CloseStep (c : Nat) (s : Bool) (g : TcpGlobal) (e' : Expr) (g' : TcpGlobal) : Prop :=
  ∃ cn res st' d', g.conns !! c = some cn ∧ CloseOutcome (cn.endSt s) (cn.out s) res st' d' ∧
    e' = Val (#(errCode res)) ∧ g' = g.setConn c ((cn.setEnd s st').setOut s d')

/-- `"CloseWrite"` of the end `s` of `c`. -/
def CloseWriteStep (c : Nat) (s : Bool) (g : TcpGlobal) (e' : Expr) (g' : TcpGlobal) : Prop :=
  ∃ cn res d', g.conns !! c = some cn ∧ CloseWriteOutcome (cn.endSt s) (cn.out s) res d' ∧
    e' = Val (#(errCode res)) ∧ g' = g.setConn c (cn.setOut s d')

/-- `"SetDeadline"` of the deadlines of kind `kind` of the end `s` of `c`. -/
def SetDeadlineStep (c : Nat) (s : Bool) (kind : w64) (set : Bool) (g : TcpGlobal) (e' : Expr)
    (g' : TcpGlobal) : Prop :=
  ∃ cn res st', g.conns !! c = some cn ∧ DeadlineOutcome (cn.endSt s) kind set res st' ∧
    e' = Val (#(errCode res)) ∧ g' = g.setConn c (cn.setEnd s st')

/-- A failure's value: no id, and the kind's code. -/
def failV (e : TcpErr) : val := PairV (#(W64 0)) (#e.code)

/-- `c` may number a new connection. -/
def NewConn (g : TcpGlobal) (c : Nat) : Prop :=
  c ≠ 0 ∧ g.conns !! c = none ∧ 2 * c + 1 < 2 ^ 64

/-- D8, D16. `"Dial"` of `a`. -/
def DialStep (a : GoString) (g : TcpGlobal) (e' : Expr) (g' : TcpGlobal) : Prop :=
  (g.plan !! a).isSome ∧
  ((e' = Val (failV .sys) ∧ g' = g) ∨
   (∃ c, NewConn g c ∧ e' = Val (PairV (#(endId c false)) (#(W64 0))) ∧
     g' = g.setConn c (TcpConn.fresh a)) ∨
   -- D16: a failure that leaves the connection, abandoned
   (∃ c, NewConn g c ∧ e' = Val (failV .sys) ∧ g' = g.setConn c (TcpConn.abandoned a)))

/-- D7. `"Accept"` of `l`, for the listener `(a, isOpen)`. -/
def AcceptStep (op : Expr) (a : GoString) (isOpen : Bool) (g : TcpGlobal) (e' : Expr)
    (g' : TcpGlobal) : Prop :=
  (isOpen = false ∧ e' = Val (failV .closed) ∧ g' = g) ∨
  (isOpen = true ∧ e' = Val (failV .sys) ∧ g' = g) ∨
  (isOpen = true ∧ e' = op ∧ g' = g) ∨
  (isOpen = true ∧ ∃ c cn, g.conns !! c = some cn ∧ cn.addr = a ∧ cn.accepted = false ∧
    2 * c + 1 < 2 ^ 64 ∧
    e' = Val (PairV (#(endId c true)) (#(W64 0))) ∧
    g' = g.setConn c { cn with accepted := true })

/-- D6, D21. `"Listen"` of `a` by the node with state `L`, at the plan address `a0`. -/
def ListenStep (a : GoString) (g : TcpGlobal) (L : TcpLocal) (e' : Expr) (L' : TcpLocal) : Prop :=
  ∃ a0, ListenAt g.plan L.host a a0 ∧
  ((e' = Val (failV .sys) ∧ L' = L) ∨
   ((∀ l, L.lis !! l ≠ some (a0, true)) ∧ ∃ l, l ≠ 0 ∧ L.lis !! l = none ∧
     e' = Val (PairV (#l) (#(W64 0))) ∧ L' = { L with lis := L.lis.insert l (a0, true) }))

/-- D9, D17. `"LisClose"` of the listener `(a, isOpen)`: the result and the listener after. -/
def LisCloseOutcome (isOpen : Bool) (res : Option TcpErr) (isOpen' : Bool) : Prop :=
  if isOpen then res = none ∧ isOpen' = false else res = some .closed ∧ isOpen' = false

/-- The step relation of the TCP extension, for a node with local state `L` on the network `g`. -/
def TcpStep (op : String) (v : val) (h : GMap Loc (NonAtomic val)) (L : TcpLocal) (g : TcpGlobal)
    (e' : Expr) (h' : GMap Loc (NonAtomic val)) (L' : TcpLocal) (g' : TcpGlobal) : Prop :=
  h' = h ∧
  match op with
  | "Listen" => ∃ a : GoString, v = #a ∧ ListenStep a g L e' L' ∧ g' = g
  | "Accept" => ∃ (l : w64) (a : GoString) (o : Bool), v = #l ∧ L.lis !! l = some (a, o) ∧
      AcceptStep (ExternalOp tcpExt.name "Accept" (Val v)) a o g e' g' ∧ L' = L
  | "LisClose" => ∃ (l : w64) (a : GoString) (o : Bool) (res : Option TcpErr) (o' : Bool),
      v = #l ∧ L.lis !! l = some (a, o) ∧ g' = g ∧ LisCloseOutcome o res o' ∧
      e' = Val (#(errCode res)) ∧ L' = { L with lis := L.lis.insert l (a, o') }
  | "Dial" => ∃ a : GoString, v = #a ∧ DialStep a g e' g' ∧ L' = L
  | "Read" => ∃ (e n : w64) (c : Nat) (s : Bool), v = PairV (#e) (#n) ∧ IsEnd e c s ∧
      ReadStep (ExternalOp tcpExt.name "Read" (Val v)) c s n g e' g' ∧ L' = L
  | "Write" => ∃ (e : w64) (bs : List w8) (c : Nat) (s : Bool), v = PairV (#e) (#bs) ∧
      IsEnd e c s ∧ WriteStep c s bs g e' g' ∧ L' = L
  | "Close" => ∃ (e : w64) (c : Nat) (s : Bool), v = #e ∧ IsEnd e c s ∧ CloseStep c s g e' g' ∧
      L' = L
  | "CloseWrite" => ∃ (e : w64) (c : Nat) (s : Bool), v = #e ∧ IsEnd e c s ∧
      CloseWriteStep c s g e' g' ∧ L' = L
  | "SetDeadline" => ∃ (e kind wall ext : w64) (c : Nat) (s : Bool),
      v = PairV (#e) (PairV (#kind) (PairV (#wall) (#ext))) ∧ IsEnd e c s ∧
      SetDeadlineStep c s kind (!timeIsZero wall ext) g e' g' ∧ L' = L
  | "AnyBool" => v = #() ∧ (∃ b : Bool, e' = Val (#b)) ∧ L' = L ∧ g' = g
  | "AnyString" => v = #() ∧ (∃ str : GoString, e' = Val (#str)) ∧ L' = L ∧ g' = g
  | "AnyW64" => v = #() ∧ (∃ n : w64, e' = Val (#n)) ∧ L' = L ∧ g' = g
  | "AnyErrno" => v = #() ∧ (∃ n : w64, n ≠ 0 ∧ e' = Val (#n)) ∧ L' = L ∧ g' = g
  | _ => False

end step

/-- D10. A crash keeps the host and drops the listeners. -/
instance tcp_semantics : ExtSemantics tcpExt where
  step := TcpStep
  crash L L' := L' = { L with lis := ∅ }

end Tcp

end Perennial
