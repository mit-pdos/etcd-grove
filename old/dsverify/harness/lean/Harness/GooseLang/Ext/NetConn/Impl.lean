/-
TCP as Go presents it: the GooseLang extension behind the lab's model of Go's `net`
[Trusted definitions!].

Its name is `"net"`, the Go package it implements: the trusted
models of `net` (`Harness/TrustedCode/net.lean`) call its operations by name,
`ExternalOp netConnExt.name "Read" ...`, and marshal Go values; goose knows nothing of it.
Review document: `notes/harness-m2a.md`. Every decision below has a Go example, run on the
claimed configuration, in `harness/netsem/` (named in brackets, e.g. [netsem: PartialWrite]).

**Claimed configuration.** Linux 7.0 TCP over IPv4 (loopback or veth links), Go 1.27's `net`,
`network` always `"tcp"`, every address a literal `"IP:port"` string that each node listens on
and its peers dial with the same spelling, distinct nodes on distinct IPs, each node in a network
namespace of its own with one IPv4 address (its IP), so that a node's wildcard `Listen`
(`":port"`, `"0.0.0.0:port"`, `"[::]:port"`) is its `Listen` on `"IP:port"` (see `Listen`).

**Local state** (per node): the node's IP, spelled as in the configured addresses (`"10.0.0.1"`),
fixed at the start (the statement, `Harness.SafeDist`, gives node `i` the IP `ips[i]`) and never
changed, by a step or a crash. Only `Listen` reads it, to resolve a wildcard host.

**State** (global, shared by all nodes):
* listeners, by id: the address, open or closed, and the connections dialed to it that no
  `Accept` has returned yet;
* connections, by id, each with two ends, the dialer's (`false`) and the acceptor's (`true`):
  per end, closed or not and its two deadline flags; per direction, a byte stream: the bytes
  written at one end and not yet read at the other, and the stream's status (`live`, `fin`,
  `cut`).
Ids are `w64`s the Go model keeps in unexported fields (`netFD`), so Go code cannot forge one; a
call with an unknown id has no step (stuck): only the trusted models make calls.

**Faults.** Loss, delay, reordering, duplication and corruption on the wire are not behaviors of
their own: TCP turns loss into delay, and delay is a schedule. What a fault can do to a
connection is (a) make an operation wait, (b) make a deadline expire, (c) break the connection.
A break (`Conn.Breaks`) may happen at any `Read`, `Write` or `Close` of either end, before the
operation takes effect, or within a `Write` that then fails with a break's error, after it
appended a prefix of its bytes (`WriteOutcome`): both streams become `cut`, and each loses an
arbitrary suffix of the bytes still in it. Afterwards each end finds out at its own pace: a
reader still gets the surviving bytes, then `io.EOF` or an error; a writer's bytes are
discarded, with success or an error. Nothing that is read was not written, in order, once.
A failed `Dial` may also have reached the listener (`Conn.abandoned`).

**Not modeled** (each a stuck call, or an over-approximation said where it is made): other
networks, addresses other than the configured ones (`NetState.addrs`) and the wildcard spellings
of a node's own (`listenAddr`; any other spelling of a host, e.g. `"localhost"`, `"::"` without
brackets, `"[0::0]"`, and a port spelled other than as configured, is stuck), `Listen` on port 0,
half-close (`CloseRead`/`CloseWrite`), keep-alive and buffer options, `SetLinger`, crashes
(phase 3: a crashed node's listeners stay open in the global state; see the review document).
Over-approximated: `Listen` on a configured address of another node may succeed (Linux fails it
with EADDRNOTAVAIL [netsem: NodeIdentity]; allowing it keeps the semantics independent of
`ip_nonlocal_bind`).
-/
module

public import Perennial.GooseLang.Lang

@[expose] public section

namespace Perennial

namespace NetConn

/-! ## State -/

/-- The status of a byte stream (one direction of a connection). -/
inductive StreamStatus where
  /-- The writer may still append. -/
  | live
  /-- The writer closed its end: once its bytes are read, the reader gets `io.EOF`
  [netsem: CloseThenEOF]. -/
  | fin
  /-- The connection broke: the bytes left are those that survived; once they are read, the
  reader gets `io.EOF` or an error, and bytes written later are discarded [netsem: BreakSuffix]. -/
  | cut
deriving DecidableEq

/-- One direction of a connection. -/
structure Stream where
  /-- Written and not yet read, oldest first. Unbounded: flow control only delays a `Write`,
  which a schedule already covers. -/
  bytes : List w8
  status : StreamStatus

/-- One end of a connection, as the process that holds it sees it. -/
structure EndState where
  /-- `Close` was called on this end; every later operation on it fails ("use of closed network
  connection"). -/
  closed : Bool
  /-- A read deadline is set (not the zero `time.Time`). Time is not modeled: with a deadline
  set, any `Read` may time out, whatever the deadline's value [netsem: DeadlineUsable]. -/
  readDeadline : Bool
  /-- A write deadline is set (as `readDeadline`). -/
  writeDeadline : Bool

/-- An end of a connection: `false` is the dialer's, `true` the acceptor's. -/
abbrev Side := Bool

/-- A connection. -/
structure Conn where
  /-- `stream s`: the bytes written at end `s` that end `!s` has not read. -/
  stream : Side → Stream
  ends : Side → EndState

/-- A listener. -/
structure Listener where
  /-- The address string passed to `Listen`, compared literally with `Dial`'s. -/
  addr : GoString
  isOpen : Bool
  /-- Connections dialed to this listener that no `Accept` has returned yet, in no particular
  order: `Accept` takes any of them (handshakes finish in any order). Some may come from a
  `Dial` that failed after the handshake (`Conn.abandoned`). Dropped by `Close` (Linux resets
  them; their dialer ends see that as a break). -/
  pending : List w64

/-- The extension's global state. -/
structure NetState where
  /-- The configured addresses (M2b): the only address strings `Listen` binds (after resolving
  a wildcard host, `listenAddr`) and `Dial` accepts; a call with another one has no step
  (stuck), so a program proved safe uses only these and its own wildcard spellings. Fixed at
  the start (`NetState.empty addrs`), never changed. The statement (`Harness.SafeDist`) requires
  each to be spelled `"IP:port"` canonically, for one IP per node: the configuration in which
  comparing address strings literally (`Listen`, `Dial`) is what the kernel does. -/
  addrs : List GoString
  listeners : GMap w64 Listener
  conns : GMap w64 Conn

instance : Inhabited NetState := ⟨⟨[], ∅, ∅⟩⟩

/-- The start state of a system with the configured addresses `addrs`: no listener, no
connection. This is the extension's start premise (`Harness.SafeDist`): every node starts with
no socket open, and nothing else uses the addresses. -/
def NetState.empty (addrs : List GoString) : NetState := ⟨addrs, ∅, ∅⟩

/-- A fresh connection: both streams live and empty, both ends open, no deadlines. -/
def Conn.fresh : Conn :=
  ⟨fun _ => ⟨[], .live⟩, fun _ => ⟨false, false, false⟩⟩

/-- The connection a failed `Dial` may leave pending at the listener: Go closed the dialer's
socket after the handshake, with nothing written (its stream `fin` and empty, its end closed,
and no one holds that end). The acceptor reads `io.EOF`, or a break's error, never data
[netsem: DialTimeoutAccepted]. -/
def Conn.abandoned : Conn :=
  ⟨fun s => ⟨[], if s then .live else .fin⟩, fun s => ⟨!s, false, false⟩⟩

/-- `c` with stream `s` replaced. -/
def Conn.setStream (c : Conn) (s : Side) (st : Stream) : Conn :=
  { c with stream := fun s' => if s' = s then st else c.stream s' }

/-- `c` with end `s` replaced. -/
def Conn.setEnd (c : Conn) (s : Side) (e : EndState) : Conn :=
  { c with ends := fun s' => if s' = s then e else c.ends s' }

/-- A break: both streams become `cut`, each keeping a prefix of its bytes (an arbitrary suffix,
possibly empty, possibly everything, is lost); the ends are unchanged. A stream already `cut`
may lose more: a later break is again a break. -/
def Conn.Breaks (c c' : Conn) : Prop :=
  c'.ends = c.ends ∧
    ∀ s, (c'.stream s).status = .cut ∧ (c'.stream s).bytes <+: (c.stream s).bytes

/-! ## Node identity -/

/-- The hosts Go's `Listen` treats as the unspecified address, binding every local interface
(Go 1.27 `net`: `isWildcard`; a socket of the IPv6 family that also takes IPv4): `""` (as in
`":port"`), `"0.0.0.0"`, `"[::]"` [netsem: NodeIdentity]. -/
def wildcardHosts : List GoString := [go!"", go!"0.0.0.0", go!"[::]"]

/-- `addr`'s port string if `addr` is `h ++ ":" ++ port` for a wildcard host `h`, else `none`. -/
def wildcardPort (addr : GoString) : Option GoString :=
  (wildcardHosts.find? (fun h => (h ++ go!":").isPrefixOf addr)).map
    (fun h => addr.drop (h.length + 1))

/-- The address string a `Listen(addr)` binds at the node whose IP is `me`: for a wildcard host,
the node's own `me ++ ":" ++ port` (with one IP per node, a wildcard listener takes exactly the
connections to that address, and it conflicts with a listener on it both ways: EADDRINUSE
[netsem: NodeIdentity]); otherwise `addr` itself. -/
def listenAddr (me addr : GoString) : GoString :=
  match wildcardPort addr with
  | some port => me ++ go!":" ++ port
  | none => addr

/-! ## Results

Every operation returns a result code (a `w64`), which the Go models turn into Go's errors. -/

/-- Success. -/
@[reducible] def errNone : w64 := 0
/-- End of stream: `io.EOF` (from `Read` only). -/
@[reducible] def errEOF : w64 := 1
/-- A deadline expired (`Timeout()` is true; the connection stays usable). -/
@[reducible] def errTimeout : w64 := 2
/-- The end (or listener) was closed by this process: "use of closed network connection". -/
@[reducible] def errClosed : w64 := 3
/-- The connection broke (a reset, a timeout of the kernel's retransmissions or keep-alives, a
broken pipe). -/
@[reducible] def errBroken : w64 := 4
/-- `Listen`, `Dial` or `Accept` failed (address in use, connection refused, unreachable,
handshake timeout, out of file descriptors, ...). -/
@[reducible] def errFail : w64 := 5

/-! ## The operations, on one connection -/

/-- `Read` at end `side` with a buffer of `n` bytes, on the connection `c` (after any break):
returns `data` and `code`, and the connection becomes `c'`. In Go a `Read` returns either some
bytes and no error, or no bytes and an error (`poll.FD.Read`). -/
def ReadOutcome (c : Conn) (side : Side) (n : Nat) (data : List w8) (code : w64) (c' : Conn) :
    Prop :=
  let e := c.ends side
  let s := c.stream (!side)
  if e.closed then data = [] ∧ code = errClosed ∧ c' = c
  -- Go returns (0, nil) for an empty buffer before any system call or deadline check
  else if n = 0 then data = [] ∧ code = errNone ∧ c' = c
  else
    -- a deadline is set: a timeout, whatever is buffered [netsem: DeadlineUsable]
    (e.readDeadline ∧ data = [] ∧ code = errTimeout ∧ c' = c) ∨
    -- some of the next bytes: at least one, at most `n` [netsem: ShortRead]
    (data ≠ [] ∧ data.length ≤ n ∧ data <+: s.bytes ∧ code = errNone ∧
      c' = c.setStream (!side) { s with bytes := s.bytes.drop data.length }) ∨
    -- the peer closed and every byte was read [netsem: CloseThenEOF]
    (s.bytes = [] ∧ s.status = .fin ∧ data = [] ∧ code = errEOF ∧ c' = c) ∨
    -- broken and every surviving byte was read: an error, or `io.EOF` (Linux reports a reset
    -- once, then end of file) [netsem: BreakSuffix]
    (s.bytes = [] ∧ s.status = .cut ∧ data = [] ∧ (code = errBroken ∨ code = errEOF) ∧ c' = c)

/-- `Write` of `data` at end `side` on the connection `c` (after any break): returns the count
`k` and `code`; the connection becomes `c'`. Go's `Write` (`poll.FD.Write`) loops over
`write(2)` until every byte is taken or an error stops it, and returns the count the kernel took
with that error, so on a live stream exactly the first `k` bytes are appended, whatever the
result; `k` is all of them when there is no error, and with an error may be any count up to
all of them [netsem: PartialWrite]. On a stream
that is not live (cut) the bytes are discarded, with success or an error: the kernel accepts
writes until it learns of the break [netsem: WriteAfterPeerClose]. The errors:
* a timeout, with a write deadline set [netsem: PartialWrite];
* `errClosed`: the end was closed when the `Write` began (nothing is written), or another
  goroutine closed it while the `Write` waited for buffer space, after the kernel took the first
  `k` bytes. The step is atomic, so it cannot see that `Close`, which the model linearizes after
  this `Write`: any `Write` at an open end may return `errClosed` after appending its first `k`
  bytes (an over-approximation) [netsem: WriteCloseRace];
* `errBroken`: the connection broke, after the kernel took the first `k` bytes (on a live stream,
  a break follows the append, which may keep all, some or none of the bytes; the reader may
  read up to all `k` of them, then a break's error) [netsem: WriteBreakPartial], or before (a
  break first, through `BreakOrNot`, then the bytes are discarded) [netsem: WriteAfterPeerClose].
-/
def WriteOutcome (c : Conn) (side : Side) (data : List w8) (k : Nat) (code : w64) (c' : Conn) :
    Prop :=
  let e := c.ends side
  let s := c.stream side
  -- the first `k` bytes appended to a live stream; discarded by one that is not live
  let c₁ := if s.status = .live then c.setStream side { s with bytes := s.bytes ++ data.take k }
    else c
  if e.closed then k = 0 ∧ code = errClosed ∧ c' = c
  else
    k ≤ data.length ∧
    ((code = errNone ∧ k = data.length ∧ c' = c₁) ∨
     (code = errTimeout ∧ e.writeDeadline ∧ c' = c₁) ∨
     (code = errClosed ∧ c' = c₁) ∨
     (code = errBroken ∧ c₁.Breaks c'))

/-- `Close` of end `side` (after any break): the end becomes closed, and its outgoing stream, if
live, `fin` (the peer reads the rest, then `io.EOF`). Unread incoming bytes are dropped with
the end (Linux then resets the connection, which the peer may see as a break). A second `Close`
fails. -/
def CloseOutcome (c : Conn) (side : Side) (code : w64) (c' : Conn) : Prop :=
  let e := c.ends side
  let s := c.stream side
  if e.closed then code = errClosed ∧ c' = c
  else code = errNone ∧
    c' = (c.setEnd side { e with closed := true }).setStream side
      (if s.status = .live then { s with status := .fin } else s)

/-- `SetDeadline` (`which = 0`), `SetReadDeadline` (1) or `SetWriteDeadline` (2) at end `side`,
setting (`set`) or clearing the deadline. Fails on a closed end. -/
def DeadlineOutcome (c : Conn) (side : Side) (which : w64) (set : Bool) (code : w64)
    (c' : Conn) : Prop :=
  let e := c.ends side
  if e.closed then code = errClosed ∧ c' = c
  else code = errNone ∧
    ((which = 0 ∧ c' = c.setEnd side { e with readDeadline := set, writeDeadline := set }) ∨
     (which = 1 ∧ c' = c.setEnd side { e with readDeadline := set }) ∨
     (which = 2 ∧ c' = c.setEnd side { e with writeDeadline := set }))

/-- The extension. Its values are none (ids are `w64`s); its local state is the node's IP. -/
@[reducible] def netConnExt : GooseExt where
  name := "net"
  Val := Empty
  LocalState := GoString
  GlobalState := NetState

section step
variable [GooseExts] [GoGlobalContext]

/-- `g` with connection `cid` replaced. -/
def NetState.setConn (g : NetState) (cid : w64) (c : Conn) : NetState :=
  { g with conns := <[cid := c]> g.conns }

/-- An operation on an existing connection end that may break the connection first: `c₁` is
the connection the operation sees, `c` itself or `c` broken. -/
def BreakOrNot (c c₁ : Conn) : Prop := c₁ = c ∨ c.Breaks c₁

/-- The step of operation `op` with argument `v` on the global state `g`, at the node whose IP
is `me`. An operation that is not listed, or an argument of another shape, or an unknown id, has
no step (stuck). -/
def NetConnStep (me : GoString) (op : String) (v : val) (g : NetState) (e' : Expr)
    (g' : NetState) : Prop :=
  match op with
  /- `Listen(addr)`: the address bound is `a = listenAddr me addr` (`addr` itself, or for a
  wildcard host the node's own address [netsem: NodeIdentity]), which must be configured (else
  stuck): a new open listener on `a`, if no open listener has that address string; or a
  failure, always allowed (the address may be in use by another process, not the node's own,
  ...) [netsem: DialListen]. The literal comparison of address strings is why the configuration
  requires each address to be spelled the same by listener and dialers. -/
  | "Listen" => ∃ addr a : GoString, v = #addr ∧ a = listenAddr me addr ∧ a ∈ g.addrs ∧
      ((g' = g ∧ e' = Val (PairV #(W64 0) #errFail)) ∨
       ∃ lid : w64, g.listeners !! lid = none ∧
         (∀ lid' l, g.listeners !! lid' = some l → l.isOpen = true → l.addr ≠ a) ∧
         g' = { g with listeners := <[lid := ⟨a, true, []⟩]> g.listeners } ∧
         e' = Val (PairV #lid #errNone))
  /- `Dial(addr)`, for a configured `addr` (else stuck): a failure, always allowed; or, if a
  listener is open on `addr`, a fresh connection, pending at that listener, whose dialer end is
  returned [netsem: DialListen]; or, again if a listener is open on `addr`, a failure that still
  leaves a connection pending there, with the dialer's end closed (`Conn.abandoned`): the kernel
  finished the handshake, but the dial's deadline fired first, and Go closed the socket and
  returned the timeout [netsem: DialTimeoutAccepted]. -/
  | "Dial" => ∃ addr : GoString, v = #addr ∧ addr ∈ g.addrs ∧
      ((g' = g ∧ e' = Val (PairV #(W64 0) #errFail)) ∨
       ∃ (lid : w64) (l : Listener) (cid : w64), g.listeners !! lid = some l ∧
         l.isOpen = true ∧ l.addr = addr ∧ g.conns !! cid = none ∧
         ((g' = { g with
                  listeners := <[lid := { l with pending := l.pending ++ [cid] }]> g.listeners,
                  conns := <[cid := Conn.fresh]> g.conns } ∧
           e' = Val (PairV #cid #errNone)) ∨
          (g' = { g with
                  listeners := <[lid := { l with pending := l.pending ++ [cid] }]> g.listeners,
                  conns := <[cid := Conn.abandoned]> g.conns } ∧
           e' = Val (PairV #(W64 0) #errFail))))
  /- `Accept()` on listener `lid`: on a closed listener, an error; else any pending connection
  (its acceptor end), or a failure, or it waits while none is pending. -/
  | "Accept" => ∃ (lid : w64) (l : Listener), v = #lid ∧ g.listeners !! lid = some l ∧
      if l.isOpen then
        (l.pending = [] ∧ g' = g ∧ e' = ExternalOp netConnExt.name "Accept" (Val v)) ∨
        (g' = g ∧ e' = Val (PairV #(W64 0) #errFail)) ∨
        (∃ cid, cid ∈ l.pending ∧
          g' = { g with listeners := <[lid := { l with pending := l.pending.erase cid }]>
                   g.listeners } ∧
          e' = Val (PairV #cid #errNone))
      else g' = g ∧ e' = Val (PairV #(W64 0) #errClosed)
  /- `Close()` of listener `lid`: it stops listening (its address is free again) and its pending
  connections are dropped; a second `Close` fails. -/
  | "CloseListener" => ∃ (lid : w64) (l : Listener), v = #lid ∧ g.listeners !! lid = some l ∧
      if l.isOpen then
        g' = { g with listeners := <[lid := { l with isOpen := false, pending := [] }]>
                 g.listeners } ∧ e' = Val #errNone
      else g' = g ∧ e' = Val #errClosed
  /- `Read` of at most `n` bytes at end `side` of connection `cid`: waits while the incoming
  stream is live and empty and the end open; otherwise, after any break, `ReadOutcome`. The
  bytes are returned as a Go string. -/
  | "Read" => ∃ (cid : w64) (side : Bool) (n : w64) (c : Conn),
      v = PairV #cid (PairV #side #n) ∧ g.conns !! cid = some c ∧
      ((g' = g ∧ e' = ExternalOp netConnExt.name "Read" (Val v) ∧ (c.ends side).closed = false ∧
          (c.stream (!side)).bytes = [] ∧ (c.stream (!side)).status = .live) ∨
       ∃ (c₁ c₂ : Conn) (data : List w8) (code : w64), BreakOrNot c c₁ ∧
         ReadOutcome c₁ side n.toNat data code c₂ ∧ g' = g.setConn cid c₂ ∧
         e' = Val (PairV #data #code))
  /- `Write` of `data` (a Go string) at end `side` of connection `cid`: after any break,
  `WriteOutcome`; returns the count. -/
  | "Write" => ∃ (cid : w64) (side : Bool) (data : List w8) (c : Conn),
      v = PairV #cid (PairV #side #data) ∧ g.conns !! cid = some c ∧
      ∃ (c₁ c₂ : Conn) (k : Nat) (code : w64), BreakOrNot c c₁ ∧
        WriteOutcome c₁ side data k code c₂ ∧ g' = g.setConn cid c₂ ∧
        e' = Val (PairV #(W64 k) #code)
  /- `Close` of end `side` of connection `cid`: after any break, `CloseOutcome`. -/
  | "Close" => ∃ (cid : w64) (side : Bool) (c : Conn),
      v = PairV #cid #side ∧ g.conns !! cid = some c ∧
      ∃ (c₁ c₂ : Conn) (code : w64), BreakOrNot c c₁ ∧ CloseOutcome c₁ side code c₂ ∧
        g' = g.setConn cid c₂ ∧ e' = Val #code
  /- The deadline setters at end `side` of connection `cid`: `DeadlineOutcome` (no break: a
  deadline call does not touch the streams). -/
  | "SetDeadline" => ∃ (cid : w64) (side : Bool) (which : w64) (set : Bool) (c : Conn),
      v = PairV #cid (PairV #side (PairV #which #set)) ∧ g.conns !! cid = some c ∧
      ∃ (c₂ : Conn) (code : w64), DeadlineOutcome c side which set code c₂ ∧
        g' = g.setConn cid c₂ ∧ e' = Val #code
  | _ => False

end step

/-- The extension's semantics: an operation changes neither the heap nor the local state (the
node's IP), and steps at the node's IP. A crash keeps the node's IP (the global state is never
changed by a crash, `DistLang.lean`). -/
instance netConn_semantics : ExtSemantics netConnExt where
  step op v h σ g e' h' σ' g' := h' = h ∧ σ' = σ ∧ NetConnStep σ op v g e' g'
  crash σ σ' := σ' = σ

end NetConn

end Perennial
