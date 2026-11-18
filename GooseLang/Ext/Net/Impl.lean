/-
The net extension of GooseLang [Trusted definitions!]: the semantics of Go's `net` package's TCP
connections, between the nodes of a distributed system (Perennial's `DistLang.lean`). Its
operations are the socket layer under `net`'s exported API; the trusted models of `net`'s
functions and methods (`Net/TrustedCode/net.lean`) call them. Each decision below has a Go
example measured on Linux in `examples/net/semantics/` (its `doc.go` indexes them by the numbers
`D1`...), and an `example` of `GooseLang/Ext/Net/Tests.lean` (outside the trust base) that the
relations allow or exclude what the Go example shows; `notes/net-tcp.md` gives the reasons
(`notes/net-tcp-v3-plan.md` for v3, D14-D21).

**Version v3.2** (2026-11-15). History: v1 (2026-11-12, every byte ever sent and a `broken` flag),
v2 (observable state only: the unread bytes and a status), v2.1 (a failing `Write` may write
nothing; id 0 names nothing; the deployment, D13), v3 (Go's error values and D14-D21), v3.1 (a
`Write` is Go's loop of steps, D2/D15: v3's one-step `Write` could time out only with a deadline set
at its start; the v3 review's R1, `notes/axiom-review/tcp-semantics.md`), v3.2 (every operation may
stutter, which is how waiting is modeled, and an invalid use panics: D22, the convention of
Perennial's Grove extension).

**State: only what a program can observe.** The global state (`NetGlobal`) is the deployment's
plan (each address the program may use, and the host that may listen at it) and the connections.
A connection (`NetConn`) has the address it was dialed to, whether it has been accepted, two ends
(the dialer's `false`, the acceptor's `true`) and two directions. A direction (`NetDir`, from one
end to the other) is the bytes written and not yet read, oldest first, and its status: `open` (the
writer may write more), `fin` (the writer shut its write side, by `Close` or `CloseWrite`) or
`cut` (the connection broke: a reset, a kernel timeout, the death of the peer's process or
machine). An end (`NetEnd`) is whether `Close` was called on it, and whether a read deadline and a
write deadline are set. A node's local state (`NetLocal`) is its host and its listeners (each an
address and whether it is open). Nothing records past operations.

**Handles.** A connection end is named by a 64-bit id, `2 c + s` for the connection `c` and the
side `s` (0 the dialer, 1 the acceptor); a listener by a 64-bit id of its node. An operation on an
id that names nothing panics (D22). The trusted models pass only ids the extension returned, which
a Go program cannot forge (they are inside `net`'s unexported structs, and the heap does not
survive a crash): a zero-value `TCPConn` or `TCPListener` (`var c net.TCPConn`) holds the id 0,
which names nothing (no connection is numbered 0 and no listener has id 0: `DialStep`,
`ListenStep`), and the models check for it before calling the extension, returning Go's bare
`syscall.EINVAL` as Go's methods do (`c.ok()`, `l.ok()`: `TestZeroValues`;
`Net/TrustedCode/net.lean`, `model.einval`).

**Each operation's outcome is a pure relation** on one end's state and one direction
(`ReadOutcome`, `WriteOutcome`, `CloseOutcome`, `CloseWriteOutcome`, `DeadlineOutcome`); the step
(`NetStep`) looks the connection up, takes an outcome, and writes it back; or it stutters (D22).
A `Write` is several steps (D2, D15), the others one. Results are pairs, as goose returns a Go
function's results.

**Errors (D14).** Every failure has a kind (`NetErr`), which the trusted models turn into Go's error
value: `closed`, an operation on the caller's own closed end or listener (Go's `poll.FD` refuses it
with `poll.ErrNetClosing`, which is `net.ErrClosed`); `timeout`, a deadline
(`poll.ErrDeadlineExceeded`, which is `os.ErrDeadlineExceeded`); `sys`, any other failure, a system
call's error (an `*os.SyscallError` around a `syscall.Errno`: `ECONNRESET`, `EPIPE`, `ETIMEDOUT`,
`ECONNREFUSED`, `EADDRINUSE`, `ENOTCONN`, ...). A failure's result is its kind's code
(`NetErr.code`), success `0` (`errCode`).

* D1 `"Read"` of `n` bytes at an end, from the direction towards it (`ReadOutcome`): on a closed
  end, `closed`. Otherwise: `n = 0` returns nothing at once; else the first `k` unread bytes,
  `1 ≤ k ≤ n` (as many as arrived: any number); EOF once nothing is unread and the writer is done
  (`fin` or `cut`); after a cut, also a `sys` error; with a read deadline set, a `timeout` that
  changes nothing (`ReadAvail`); until one of these, it waits (a stutter, D22). And at any read,
  the connection may break: the direction becomes `cut`, keeping a prefix of its unread bytes,
  and the read answers as on the broken direction (bytes, EOF or an error). EOF does not say the
  writer finished cleanly: a cut that kept every byte reads as EOF, and that is what the death of
  the writer's process looks like (its kernel's FIN, or a reset whose error another call took).
  A read blocked when another goroutine closes the end returns `closed`: the read stutters, the
  close steps, the read then steps on a closed end.
* D2 `"Write"`: one step of a `Write` (`WriteOutcome`). Go's `(*poll.FD).Write`
  (`internal/poll/fd_unix.go`) is a loop: `writeLock` (`ErrNetClosing` once the end is closing),
  `prepareWrite` (that, or the deadline), then `write(2)` of the bytes not yet written and, while
  some remain, again; when the socket's buffer is full (`EAGAIN`) it first waits (`waitWrite`:
  `ErrNetClosing`, or the deadline). The trusted `conn.Write.impl` is that loop, each iteration
  the extension's `"Write"` of the bytes `rs` not yet written, on the end's state and the direction
  from it at that step: on a closed end, `closed`, nothing written. Into a direction the end shut
  (`fin`): `sys` (`EPIPE`), or `timeout` with a write deadline set. Into an open direction: the
  first `k` bytes of `rs` appended, any `1 ≤ k ≤ |rs|` (all of them; a part, the buffer full), with
  no failure (`k = 0` only for an empty `rs`: a step that would count nothing is a wait, a stutter,
  D22); or a `sys` failure, nothing appended, the connection broken (`cut`, its unread bytes kept);
  or, with a write deadline set, a `timeout`, nothing appended. Into a cut direction: the bytes are
  discarded, any `1 ≤ k ≤ |rs|` counted (a dead peer, before this kernel knows; `0` for an empty
  `rs`), or `sys`, or `timeout` with a write deadline set. A failing step appends nothing (a
  system call writes or fails); `write(2)` of a TCP socket never returns 0 for bytes (Linux's
  `tcp_sendmsg_locked` fails when it copied nothing), so Go's `io.ErrUnexpectedEOF` is not modeled.
  `Write` returns `(nn, nil)` once its steps counted `nn = len(b)` with no failure, and `(nn, err)`
  at its first failing step: fewer bytes than asked only with an error. An empty `b` takes one step
  (Go makes the system call for an empty buffer too, after the deadline check: `TestEmptyWrite`),
  which may fail. A step with no write deadline set does not time out.
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
* D6 `"Listen"` of an address `a` (`ListenAt`, D21 for the wildcards): a panic (D22) unless `a` is
  in the plan with this node's host. A new open listener at `a`; or a `sys` failure, which is the
  only outcome if this node already has an open listener at `a` (`EADDRINUSE`).
* D7 `"Accept"` of a listener `l`: only `closed` once `l` is closed. Otherwise a connection dialed
  to `l`'s address and not yet accepted, now accepted; or a `sys` failure; until one of these, it
  waits (a stutter, D22). Pending
  connections belong to the address, not to a listener, because a node's step sees only its own
  local state and the network (Perennial's step relation): a `Dial` cannot see whether another node
  listens, and a crash cannot reset connections. So a connection dialed when no listener was open,
  or before the listening node's crash, may be accepted later: more than Linux, which refuses or
  resets it, an outcome the dialer sees as a failure or a cut, which the model also allows.
* D8 `"Dial"` of `a`: a panic (D22) unless `a` is in the plan. A new connection to `a`, not yet
  accepted,
  both ends fresh and both directions open and empty; or a `sys` failure (refused, unreachable);
  or (D16) a `sys` failure that leaves a connection to `a`, pending, whose dialer's end is closed
  and whose direction from it is `fin` and empty (`NetConn.abandoned`): Go's `connect` gives up
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
and the wildcards of D21, compared as strings; `Listen` or `Dial` of any other string panics (D22).
Port `0`, TLS, UDP, Unix sockets, the deadlines' values, keepalives, the listeners' deadlines: not
modeled (the methods are not modeled either, so a program calling them is stuck: no model, no proof).

* D14 the error kinds (above).
* D15 a `Write` is a loop of steps (D2): a `Close` of its end, or a deadline set, by another
  goroutine while it waits applies at its next step, which fails (`closed`; `timeout`) after the
  bytes the earlier steps wrote, which the peer may have read (`TestWriteCloseRace`,
  `TestWriteDeadlineSetDuring`).
* D16 abandoned dials (D8).
* D17 `Close` of an open end or listener succeeds (D3, D9).
* D18 addresses (`LocalAddr`, `RemoteAddr`, `TCPListener.Addr`): non-nil `*TCPAddr`s fixed at the
  connection's or listener's creation, otherwise arbitrary; in the Go heap, no state here
  (`Net/TrustedCode/net.lean`).
* D19 `DialTimeout`: `"Dial"`; its model may turn a failure into a timeout (`net`'s `errTimeout`, or
  `poll.ErrDeadlineExceeded`: `Net/TrustedCode/net.lean`), and D16 applies.
* D20 the plan's well-formedness (D13, `Deploy.lean`).
* D21 wildcard `Listen` (`ListenAt`): `":p"`, `"0.0.0.0:p"`, `"[::]:p"` (not themselves plan
  addresses) listen at the plan address with the port `p`, which must be at this node's host and
  the plan's only address with that port (a panic otherwise, D22): on one machine a wildcard
  listener takes every local address with its port (`TestAddressAliases`, `TestWildcardListen`).
* D22 **Steps: every operation may stutter, which is how waiting is modeled; invalid uses panic**
  (`NetStep`, `IsNetStep`). The convention of Perennial's Grove extension (`Perennial/GooseLang/
  Ext/Grove/Impl.lean`, `GroveStep`): any call of the extension may take a step that changes nothing
  and leaves the call as it was (`e' = ExternalOp netExt.name op (Val v)`), in every state. A
  blocked `Read`, `Accept` or `Write` step is that stutter, repeated until an outcome rule decides
  it: the relations have no wait of their own. A stutter is never a call's last step, so it adds no
  result Go does not return; it lets a proof of a call that may block go by Löb induction
  (`Specs.lean`, `wp_net_op`) instead of showing that the call can step. So every state needs an
  outcome rule besides the stutter (else a program could stutter there forever, and a safety
  theorem would hide what the real program does next): for an argument the extension cannot use,
  the outcome is `Panic` (GooseLang's builtin panic, stuck and not recoverable, `wp_PanicOp`; not
  `go.panic`'s, which `recover` catches), so a proof must show that the program never makes the
  call. Every state, by operation (`Tests.lean`'s `isNetStep_total`: every operation in every state
  has an outcome that is not a stutter):

  | operation | argument, state | outcomes besides the stutter |
  |---|---|---|
  | `Listen` | `#a`, `ListenAt plan host a a0` | D6: a new open listener at `a0`, or `sys` (only `sys` with one open at `a0`) |
  | `Listen` | `#a`, no such `a0`: not a plan address at this host, another node's, a wildcard whose port is not unique, any other string | `Panic` (a violation of the deployment, D13) |
  | `Dial` | `#a`, a plan address | D8, D16: a new connection, `sys`, or `sys` leaving it abandoned |
  | `Dial` | `#a`, not a plan address | `Panic` (D13) |
  | `Accept` | `#l`, a listener of this node | D7: `closed` if it is closed; if open, `sys` or a pending connection accepted |
  | `LisClose` | `#l`, a listener of this node | D9: `LisCloseOutcome` (success if open, `closed` if not) |
  | `Accept`, `LisClose` | `#l`, no listener `l` of this node (`0` among them) | `Panic` (unreachable: the models check for `0`, and ids are unforgeable) |
  | `Read` | `(#e, #n)`, `e` an end of a connection | D1: `ReadOutcome`, never empty (`closed`; `n = 0`; else a cut, then bytes or EOF) |
  | `Write` | `(#e, #bs)`, `e` an end of a connection | D2: `WriteOutcome`, never empty (`closed`; `sys` into `fin` or `cut`; a cut of an open direction) |
  | `Close`, `CloseWrite` | `#e`, `e` an end of a connection | D3, D4: `CloseOutcome` (one outcome), `CloseWriteOutcome` (on an open end: success or `sys`) |
  | `SetDeadline` | `(#e, (#kind, (#wall, #ext)))`, `e` an end of a connection | D5: `DeadlineOutcome` (one) |
  | `Read` ... `SetDeadline` | `e` names no end of a connection (`0` among them) | `Panic` (unreachable: as `Accept`'s) |
  | `AnyBool`, `AnyString`, `AnyW64`, `AnyErrno` | `#()` | a value |
  | each of the above | an argument of another shape | `Panic` (unreachable: the models pass these shapes) |
  | any other name | any | `Panic` (unreachable: the models call only these) |
-/
module

public import Perennial.GooseLang.Lang

@[expose] public section

namespace Perennial

namespace Net

/-- The status of a direction of a connection. -/
inductive NetStatus where
  /-- The writer may write more. -/
  | open
  /-- The writer shut its write side (`Close`, `CloseWrite`). -/
  | fin
  /-- The connection broke. -/
  | cut
deriving DecidableEq, Inhabited

/-- One direction of a connection: the bytes written and not yet read, oldest first, and its
status. -/
structure NetDir where
  bytes : List w8
  status : NetStatus
deriving DecidableEq, Inhabited

/-- An open, empty direction. -/
def NetDir.fresh : NetDir := ⟨[], .open⟩

/-- The state of one end of a connection. -/
structure NetEnd where
  /-- `Close` was called on it. -/
  closed : Bool
  /-- A read deadline is set. -/
  rdl : Bool
  /-- A write deadline is set. -/
  wdl : Bool
deriving DecidableEq, Inhabited

/-- A fresh end. -/
def NetEnd.fresh : NetEnd := ⟨false, false, false⟩

/-- A connection: its address, whether it was accepted, its two ends (`false` the dialer, `true`
the acceptor) and its two directions. -/
structure NetConn where
  addr : GoString
  accepted : Bool
  dEnd : NetEnd
  aEnd : NetEnd
  /-- From the dialer to the acceptor. -/
  up : NetDir
  /-- From the acceptor to the dialer. -/
  down : NetDir
deriving Inhabited

/-- A new connection to `a`. -/
def NetConn.fresh (a : GoString) : NetConn :=
  ⟨a, false, NetEnd.fresh, NetEnd.fresh, NetDir.fresh, NetDir.fresh⟩

/-- D16. The connection a failed dial of `a` may leave: pending, its dialer's end closed and its
direction from it shut and empty. -/
def NetConn.abandoned (a : GoString) : NetConn :=
  ⟨a, false, { NetEnd.fresh with closed := true }, NetEnd.fresh, ⟨[], .fin⟩, NetDir.fresh⟩

/-- The state of the end `s` of `c`. -/
def NetConn.endSt (c : NetConn) : Bool → NetEnd
  | false => c.dEnd
  | true => c.aEnd

/-- The direction from the end `s` of `c` (the one it writes). -/
def NetConn.out (c : NetConn) : Bool → NetDir
  | false => c.up
  | true => c.down

/-- `c` with the state of its end `s` replaced. -/
def NetConn.setEnd (c : NetConn) : Bool → NetEnd → NetConn
  | false, st => { c with dEnd := st }
  | true, st => { c with aEnd := st }

/-- `c` with the direction from its end `s` replaced. -/
def NetConn.setOut (c : NetConn) : Bool → NetDir → NetConn
  | false, d => { c with up := d }
  | true, d => { c with down := d }

/-- The network. -/
structure NetGlobal where
  /-- The deployment: each address the program may use, and the host that may listen at it. -/
  plan : GMap GoString GoString
  /-- Every connection dialed, by number. -/
  conns : GMap Nat NetConn

instance : Inhabited NetGlobal := ⟨⟨∅, ∅⟩⟩

/-- The network with the connection `c` set to `cn`. -/
def NetGlobal.setConn (g : NetGlobal) (c : Nat) (cn : NetConn) : NetGlobal :=
  { g with conns := g.conns.insert c cn }

/-- A node's state: its host, and its listeners (each its address and whether it is open). -/
structure NetLocal where
  host : GoString
  lis : GMap w64 (GoString × Bool)

instance : Inhabited NetLocal := ⟨⟨default, ∅⟩⟩

/-- The id of the end `s` of the connection `c`. -/
def endId (c : Nat) (s : Bool) : w64 := BitVec.ofNat 64 (2 * c + if s then 1 else 0)

/-- `e` is the end `s` of the connection `c`, in range. -/
def IsEnd (e : w64) (c : Nat) (s : Bool) : Prop :=
  2 * c + 1 < 2 ^ 64 ∧ e = endId c s

/-- The net extension. -/
@[reducible] def netExt : GooseExt where
  name := "net"
  Val := Empty
  LocalState := NetLocal
  GlobalState := NetGlobal

/-! ## Errors -/

/-- D14. The kind of a failure. -/
inductive NetErr where
  /-- An operation on the caller's own closed end or listener (Go's `net.ErrClosed`). -/
  | closed
  /-- A deadline (Go's `os.ErrDeadlineExceeded`). -/
  | timeout
  /-- Any other failure: a system call's error. -/
  | sys
deriving DecidableEq, Inhabited

/-- The code of a failure's kind, as the trusted models receive it. -/
def NetErr.code : NetErr → w64
  | .closed => W64 1
  | .timeout => W64 2
  | .sys => W64 3

/-- The code of a result: `0` for success. -/
def errCode : Option NetErr → w64
  | none => W64 0
  | some e => e.code

/-! ## The outcomes of the operations on an end -/

/-- What a read returns: bytes, EOF, an error. (A read that waits stutters, D22.) -/
inductive ReadRes where
  | bytes (bs : List w8)
  | eof
  | err (e : NetErr)
deriving DecidableEq

/-- A read of `n > 0` bytes at an open end in state `st`, from the direction `d` as it is: its
result `r` and the direction after, `d'`. -/
def ReadAvail (st : NetEnd) (d : NetDir) (n : Nat) (r : ReadRes) (d' : NetDir) : Prop :=
  -- the first `k` unread bytes
  (∃ k, 1 ≤ k ∧ k ≤ n ∧ k ≤ d.bytes.length ∧ r = .bytes (d.bytes.take k) ∧
    d' = { d with bytes := d.bytes.drop k }) ∨
  -- EOF: nothing unread, and the writer is done
  (d.bytes = [] ∧ d.status ≠ .open ∧ r = .eof ∧ d' = d) ∨
  -- an error, once the connection broke
  (d.status = .cut ∧ r = .err .sys ∧ d' = d) ∨
  -- a timeout
  (st.rdl = true ∧ r = .err .timeout ∧ d' = d)

/-- D1. A read of `n` bytes at an end in state `st`, from the direction `d` towards it: its result
`r` and the direction after, `d'`. The connection may break at the read (a prefix of the unread
bytes survives, and the read answers as a read of the broken direction does: bytes, EOF or an
error), which is also how the death of the writer's process or machine shows. -/
def ReadOutcome (st : NetEnd) (d : NetDir) (n : Nat) (r : ReadRes) (d' : NetDir) : Prop :=
  if st.closed then r = .err .closed ∧ d' = d
  else if n = 0 then r = .bytes [] ∧ d' = d
  else ReadAvail st d n r d' ∨
    -- the connection breaks now
    (∃ k, k ≤ d.bytes.length ∧ ReadAvail st ⟨d.bytes.take k, .cut⟩ n r d')

/-- D2. One step of a `Write`, of the bytes `rs` not yet written, at an end in state `st`, into the
direction `d` from it: the count `k` it adds, its result `res` (`none`: no failure, the `Write` goes
on unless it has written everything; else the failure's kind) and the direction after, `d'`. A
step that does not fail counts at least one byte unless `rs` is empty (`1 ≤ k ∨ rs = []`): one
that would count none is a wait, a stutter (D22). -/
def WriteOutcome (st : NetEnd) (d : NetDir) (rs : List w8) (k : Nat) (res : Option NetErr)
    (d' : NetDir) : Prop :=
  if st.closed then k = 0 ∧ res = some .closed ∧ d' = d
  else match d.status with
  | .fin => k = 0 ∧ d' = d ∧ (res = some .sys ∨ (st.wdl = true ∧ res = some .timeout))
  | .cut =>
    -- discarded
    d' = d ∧ ((k ≤ rs.length ∧ (1 ≤ k ∨ rs = []) ∧ res = none) ∨
      (k = 0 ∧ (res = some .sys ∨ (st.wdl = true ∧ res = some .timeout))))
  | .open =>
    -- the first `k` bytes (all, or some: the buffer full)
    (k ≤ rs.length ∧ (1 ≤ k ∨ rs = []) ∧ res = none ∧
      d' = { d with bytes := d.bytes ++ rs.take k }) ∨
    -- the connection breaks
    (k = 0 ∧ res = some .sys ∧ d' = { d with status := .cut }) ∨
    -- a timeout
    (st.wdl = true ∧ k = 0 ∧ res = some .timeout ∧ d' = d)

/-- `d` shut by its writer, if it is open. -/
def NetDir.shut (d : NetDir) : NetDir :=
  if d.status = .open then { d with status := .fin } else d

/-- D3, D17. A close of an end in state `st` whose direction is `d`: the result, the end's state
and the direction after. -/
def CloseOutcome (st : NetEnd) (d : NetDir) (res : Option NetErr) (st' : NetEnd) (d' : NetDir) :
    Prop :=
  if st.closed then res = some .closed ∧ st' = st ∧ d' = d
  else res = none ∧ st' = { st with closed := true } ∧ d' = d.shut

/-- D4. A `CloseWrite` of an end in state `st` whose direction is `d`: the result and the
direction after. -/
def CloseWriteOutcome (st : NetEnd) (d : NetDir) (res : Option NetErr) (d' : NetDir) : Prop :=
  if st.closed then res = some .closed ∧ d' = d
  else (res = none ∧ d' = d.shut) ∨ (res = some .sys ∧ d' = d)

/-- D5. Setting the deadlines of kind `kind` (`0` both, `1` the read deadline, `2` the write
deadline) of an end in state `st` (`set`: the time is not zero): the result and the end's state
after. -/
def DeadlineOutcome (st : NetEnd) (kind : w64) (set : Bool) (res : Option NetErr) (st' : NetEnd) :
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
(`0` bytes, `NetErr.code` an error, `4` EOF). -/
def readRes (bs : List w8) (code : w64) : val := PairV (#bs) (#code)

/-- The value of a read's result `r`. -/
def ReadRes.toVal : ReadRes → val
  | .bytes bs => readRes bs 0
  | .eof => readRes [] 4
  | .err e => readRes [] e.code

/-- `"Read"` of `n` bytes at the end `s` of `c`. -/
def ReadStep (c : Nat) (s : Bool) (n : w64) (g : NetGlobal) (e' : Expr) (g' : NetGlobal) : Prop :=
  ∃ cn r d', g.conns !! c = some cn ∧ ReadOutcome (cn.endSt s) (cn.out (!s)) n.toNat r d' ∧
    e' = Val r.toVal ∧ g' = g.setConn c (cn.setOut (!s) d')

/-- `"Write"` of `bs` at the end `s` of `c`: one step of a `Write` (D2), `bs` the bytes it has not
written yet. -/
def WriteStep (c : Nat) (s : Bool) (bs : List w8) (g : NetGlobal) (e' : Expr) (g' : NetGlobal) :
    Prop :=
  ∃ cn k res d', g.conns !! c = some cn ∧ WriteOutcome (cn.endSt s) (cn.out s) bs k res d' ∧
    e' = Val (PairV (#(BitVec.ofNat 64 k)) (#(errCode res))) ∧ g' = g.setConn c (cn.setOut s d')

/-- `"Close"` of the end `s` of `c`. -/
def CloseStep (c : Nat) (s : Bool) (g : NetGlobal) (e' : Expr) (g' : NetGlobal) : Prop :=
  ∃ cn res st' d', g.conns !! c = some cn ∧ CloseOutcome (cn.endSt s) (cn.out s) res st' d' ∧
    e' = Val (#(errCode res)) ∧ g' = g.setConn c ((cn.setEnd s st').setOut s d')

/-- `"CloseWrite"` of the end `s` of `c`. -/
def CloseWriteStep (c : Nat) (s : Bool) (g : NetGlobal) (e' : Expr) (g' : NetGlobal) : Prop :=
  ∃ cn res d', g.conns !! c = some cn ∧ CloseWriteOutcome (cn.endSt s) (cn.out s) res d' ∧
    e' = Val (#(errCode res)) ∧ g' = g.setConn c (cn.setOut s d')

/-- `"SetDeadline"` of the deadlines of kind `kind` of the end `s` of `c`. -/
def SetDeadlineStep (c : Nat) (s : Bool) (kind : w64) (set : Bool) (g : NetGlobal) (e' : Expr)
    (g' : NetGlobal) : Prop :=
  ∃ cn res st', g.conns !! c = some cn ∧ DeadlineOutcome (cn.endSt s) kind set res st' ∧
    e' = Val (#(errCode res)) ∧ g' = g.setConn c (cn.setEnd s st')

/-- A failure's value: no id, and the kind's code. -/
def failV (e : NetErr) : val := PairV (#(W64 0)) (#e.code)

/-- `c` may number a new connection. -/
def NewConn (g : NetGlobal) (c : Nat) : Prop :=
  c ≠ 0 ∧ g.conns !! c = none ∧ 2 * c + 1 < 2 ^ 64

/-- D8, D16. `"Dial"` of `a`. -/
def DialStep (a : GoString) (g : NetGlobal) (e' : Expr) (g' : NetGlobal) : Prop :=
  (g.plan !! a).isSome ∧
  ((e' = Val (failV .sys) ∧ g' = g) ∨
   (∃ c, NewConn g c ∧ e' = Val (PairV (#(endId c false)) (#(W64 0))) ∧
     g' = g.setConn c (NetConn.fresh a)) ∨
   -- D16: a failure that leaves the connection, abandoned
   (∃ c, NewConn g c ∧ e' = Val (failV .sys) ∧ g' = g.setConn c (NetConn.abandoned a)))

/-- D7. `"Accept"` of `l`, for the listener `(a, isOpen)` (a wait is a stutter, D22). -/
def AcceptStep (a : GoString) (isOpen : Bool) (g : NetGlobal) (e' : Expr) (g' : NetGlobal) :
    Prop :=
  (isOpen = false ∧ e' = Val (failV .closed) ∧ g' = g) ∨
  (isOpen = true ∧ e' = Val (failV .sys) ∧ g' = g) ∨
  (isOpen = true ∧ ∃ c cn, g.conns !! c = some cn ∧ cn.addr = a ∧ cn.accepted = false ∧
    2 * c + 1 < 2 ^ 64 ∧
    e' = Val (PairV (#(endId c true)) (#(W64 0))) ∧
    g' = g.setConn c { cn with accepted := true })

/-- D6, D21. `"Listen"` of `a` by the node with state `L`, at the plan address `a0`. -/
def ListenStep (a : GoString) (g : NetGlobal) (L : NetLocal) (e' : Expr) (L' : NetLocal) : Prop :=
  ∃ a0, ListenAt g.plan L.host a a0 ∧
  ((e' = Val (failV .sys) ∧ L' = L) ∨
   ((∀ l, L.lis !! l ≠ some (a0, true)) ∧ ∃ l, l ≠ 0 ∧ L.lis !! l = none ∧
     e' = Val (PairV (#l) (#(W64 0))) ∧ L' = { L with lis := L.lis.insert l (a0, true) }))

/-- D9, D17. `"LisClose"` of the listener `(a, isOpen)`: the result and the listener after. -/
def LisCloseOutcome (isOpen : Bool) (res : Option NetErr) (isOpen' : Bool) : Prop :=
  if isOpen then res = none ∧ isOpen' = false else res = some .closed ∧ isOpen' = false

/-- D22. An invalid use: a panic (GooseLang's builtin one, stuck: `wp_PanicOp`), nothing
changed. -/
def Invalid (L : NetLocal) (g : NetGlobal) (e' : Expr) (L' : NetLocal) (g' : NetGlobal) : Prop :=
  e' = Panic "net: invalid use of the net extension" ∧ L' = L ∧ g' = g

/-- D22. An operation whose argument is valid when `valid` holds: its `step`, or, if `valid` does
not hold, a panic. -/
def OrInvalid (valid step : Prop) (L : NetLocal) (g : NetGlobal) (e' : Expr) (L' : NetLocal)
    (g' : NetGlobal) : Prop :=
  step ∨ (¬ valid ∧ Invalid L g e' L' g')

/-- D22. The id `e` is the end `s` of the connection `c`, which exists. -/
def EndOf (g : NetGlobal) (e : w64) (c : Nat) (s : Bool) : Prop :=
  IsEnd e c s ∧ (g.conns !! c).isSome

/-- The outcome rules of the net extension (all but the stutter), for a node with local state `L`
on the network `g`: each operation's step on a valid argument, else a panic (D22, its table). -/
def IsNetStep (op : String) (v : val) (L : NetLocal) (g : NetGlobal) (e' : Expr) (L' : NetLocal)
    (g' : NetGlobal) : Prop :=
  match op with
  | "Listen" => OrInvalid (∃ a a0 : GoString, v = #a ∧ ListenAt g.plan L.host a a0)
      (∃ a : GoString, v = #a ∧ ListenStep a g L e' L' ∧ g' = g) L g e' L' g'
  | "Accept" => OrInvalid (∃ (l : w64) (x : GoString × Bool), v = #l ∧ L.lis !! l = some x)
      (∃ (l : w64) (a : GoString) (o : Bool), v = #l ∧ L.lis !! l = some (a, o) ∧
        AcceptStep a o g e' g' ∧ L' = L) L g e' L' g'
  | "LisClose" => OrInvalid (∃ (l : w64) (x : GoString × Bool), v = #l ∧ L.lis !! l = some x)
      (∃ (l : w64) (a : GoString) (o : Bool) (res : Option NetErr) (o' : Bool),
        v = #l ∧ L.lis !! l = some (a, o) ∧ g' = g ∧ LisCloseOutcome o res o' ∧
        e' = Val (#(errCode res)) ∧ L' = { L with lis := L.lis.insert l (a, o') }) L g e' L' g'
  | "Dial" => OrInvalid (∃ a : GoString, v = #a ∧ (g.plan !! a).isSome)
      (∃ a : GoString, v = #a ∧ DialStep a g e' g' ∧ L' = L) L g e' L' g'
  | "Read" => OrInvalid
      (∃ (e n : w64) (c : Nat) (s : Bool), v = PairV (#e) (#n) ∧ EndOf g e c s)
      (∃ (e n : w64) (c : Nat) (s : Bool), v = PairV (#e) (#n) ∧ IsEnd e c s ∧
        ReadStep c s n g e' g' ∧ L' = L) L g e' L' g'
  | "Write" => OrInvalid
      (∃ (e : w64) (bs : List w8) (c : Nat) (s : Bool), v = PairV (#e) (#bs) ∧ EndOf g e c s)
      (∃ (e : w64) (bs : List w8) (c : Nat) (s : Bool), v = PairV (#e) (#bs) ∧
        IsEnd e c s ∧ WriteStep c s bs g e' g' ∧ L' = L) L g e' L' g'
  | "Close" => OrInvalid (∃ (e : w64) (c : Nat) (s : Bool), v = #e ∧ EndOf g e c s)
      (∃ (e : w64) (c : Nat) (s : Bool), v = #e ∧ IsEnd e c s ∧ CloseStep c s g e' g' ∧
        L' = L) L g e' L' g'
  | "CloseWrite" => OrInvalid (∃ (e : w64) (c : Nat) (s : Bool), v = #e ∧ EndOf g e c s)
      (∃ (e : w64) (c : Nat) (s : Bool), v = #e ∧ IsEnd e c s ∧
        CloseWriteStep c s g e' g' ∧ L' = L) L g e' L' g'
  | "SetDeadline" => OrInvalid
      (∃ (e kind wall ext : w64) (c : Nat) (s : Bool),
        v = PairV (#e) (PairV (#kind) (PairV (#wall) (#ext))) ∧ EndOf g e c s)
      (∃ (e kind wall ext : w64) (c : Nat) (s : Bool),
        v = PairV (#e) (PairV (#kind) (PairV (#wall) (#ext))) ∧ IsEnd e c s ∧
        SetDeadlineStep c s kind (!timeIsZero wall ext) g e' g' ∧ L' = L) L g e' L' g'
  | "AnyBool" => OrInvalid (v = #())
      (v = #() ∧ (∃ b : Bool, e' = Val (#b)) ∧ L' = L ∧ g' = g) L g e' L' g'
  | "AnyString" => OrInvalid (v = #())
      (v = #() ∧ (∃ str : GoString, e' = Val (#str)) ∧ L' = L ∧ g' = g) L g e' L' g'
  | "AnyW64" => OrInvalid (v = #())
      (v = #() ∧ (∃ n : w64, e' = Val (#n)) ∧ L' = L ∧ g' = g) L g e' L' g'
  | "AnyErrno" => OrInvalid (v = #())
      (v = #() ∧ (∃ n : w64, n ≠ 0 ∧ e' = Val (#n)) ∧ L' = L ∧ g' = g) L g e' L' g'
  | _ => Invalid L g e' L' g'

/-- The step relation of the net extension, for a node with local state `L` on the network `g`
(D22): the operation stutters (nothing changes, the call stays as it was), or it takes one of its
outcome rules (`IsNetStep`). The heap does not change. -/
def NetStep (op : String) (v : val) (h : GMap Loc (NonAtomic val)) (L : NetLocal) (g : NetGlobal)
    (e' : Expr) (h' : GMap Loc (NonAtomic val)) (L' : NetLocal) (g' : NetGlobal) : Prop :=
  h' = h ∧ ((e' = ExternalOp netExt.name op (Val v) ∧ L' = L ∧ g' = g) ∨
    IsNetStep op v L g e' L' g')

end step

/-- D10. A crash keeps the host and drops the listeners. -/
instance net_semantics : ExtSemantics netExt where
  step := NetStep
  crash L L' := L' = { L with lis := ∅ }

end Net

end Perennial
