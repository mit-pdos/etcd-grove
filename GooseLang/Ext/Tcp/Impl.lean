/-
The TCP extension of GooseLang [Trusted definitions!]: the semantics of Go's `net` package's TCP
connections, between the nodes of a distributed system (Perennial's `DistLang.lean`). Its
operations are the socket layer under `net`'s exported API; the trusted models of `net`'s
functions and methods (`NetTcp/TrustedCode/net.lean`) call them. Each decision below has a Go
example measured on Linux in `examples/net/semantics/` (its `doc.go` indexes them by the numbers
`D1`...); `notes/net-tcp.md` gives the reasons.

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
id that names nothing is stuck: the trusted models only pass ids the extension returned, which a
Go program cannot forge (they are inside `net`'s unexported structs, and the heap does not survive
a crash).

**Each operation's outcome is a pure relation** on one end's state and one direction
(`ReadOutcome`, `WriteOutcome`, `CloseOutcome`, `CloseWriteOutcome`, `DeadlineOutcome`); the step
(`TcpStep`) looks the connection up, takes an outcome, and writes it back. Results are pairs, as
goose returns a Go function's results.

* D1 `"Read"` of `n` bytes at an end, from the direction towards it (`ReadOutcome`): on a closed
  end, an error. Otherwise: `n = 0` returns nothing at once; else the first `k` unread bytes,
  `1 ≤ k ≤ n` (as many as arrived: any number); EOF once nothing is unread and the writer is done
  (`fin` or `cut`); after a cut, also an error; it waits while the direction is open and empty;
  with a read deadline set, a timeout error that changes nothing (`ReadAvail`). And at any read,
  the connection may break: the direction becomes `cut`, keeping a prefix of its unread bytes,
  and the read answers as on the broken direction (bytes, EOF or an error). EOF does not say the
  writer finished cleanly: a cut that kept every byte reads as EOF, and that is what the death of
  the writer's process looks like (its kernel's FIN, or a reset whose error another call took).
* D2 `"Write"` of `bs` at an end, into the direction from it (`WriteOutcome`): on a closed end, or a
  direction the end shut (`fin`), an error writing nothing. Into an open direction: all of `bs`
  appended; or a prefix of it, shorter, appended and the connection broken (`cut`), with an error;
  with a write deadline set, a prefix, shorter, appended and a timeout error, the direction still
  open. Into a cut direction: the bytes are discarded, with success or an error (a write after a
  reset may land in the local buffer and be lost, or fail). Go's `Write` returns fewer bytes than
  asked only with an error.
* D3 `"Close"` of an end (`CloseOutcome`): an error if it is closed already; otherwise the end is
  closed and its direction, if open, becomes `fin`; the result may be an error all the same.
* D4 `"CloseWrite"` of an end (`CloseWriteOutcome`): an error if it is closed; otherwise its
  direction, if open, becomes `fin`, with success; or an error that changes nothing.
* D5 `"SetDeadline"` of an end, for reads, writes or both, to a time (`DeadlineOutcome`): an error
  on a closed end; otherwise the deadline is set if the time is not Go's zero time (`timeIsZero`,
  Go's `Time.IsZero`) and cleared if it is. Deadline values are not modeled: with a deadline set,
  any operation of that kind may time out.
* D6 `"Listen"` of an address `a`: stuck unless `a` is in the plan with this node's host. A new open
  listener at `a`; or a failure, which is the only outcome if this node already has an open
  listener at `a` (`EADDRINUSE`).
* D7 `"Accept"` of a listener `l`: only a failure once `l` is closed. Otherwise a connection dialed
  to `l`'s address and not yet accepted, now accepted; or a failure; or it waits. Pending
  connections belong to the address, not to a listener, because a node's step sees only its own
  local state and the network (Perennial's step relation): a `Dial` cannot see whether another node
  listens, and a crash cannot reset connections. So a connection dialed when no listener was open,
  or before the listening node's crash, may be accepted later: more than Linux, which refuses or
  resets it, an outcome the dialer sees as a failure or a cut, which the model also allows.
* D8 `"Dial"` of `a`: stuck unless `a` is in the plan. A new connection to `a`, not yet accepted,
  both ends fresh and both directions open and empty; or a failure (refused, unreachable).
* D9 `"LisClose"` of `l`: closes it (`true`); a failure (`false`) if it is closed already. Pending
  connections stay pending (D7).
* `"AnyBool"`, `"AnyString"`: an arbitrary value (the parts of an error that the model does not
  explain: `OpError.Timeout`, `Temporary`, `Error`).

**Crashes** (D10, `crash`): a node's crash (or its process's exit, D11) leaves the network as it is
(DistLang's crash keeps the global state, and an extension's crash relation is node-local). Its
listeners are gone (`lis` empty), so the restarted node may listen at its addresses again. What
its peers see of its connections (a FIN, a reset, or nothing) is covered by cuts (D1, D2). The host
is kept.

**What is not modeled** (D12). Memory exhaustion in the kernel (`ENOMEM`/`ENOBUFS`: a failure of a
live connection that is not a cut), as the file extensions' allocation failures. Addresses are the
plan's strings, compared as strings: the plan's strings must name distinct sockets (no two strings
for one `host:port`), an assumption of the deployment; `Listen` or `Dial` of any other string is
stuck. Port `0`, TLS, UDP, Unix sockets, `LocalAddr`/`RemoteAddr`, the deadlines' values,
keepalives: not modeled (the methods are not modeled either, so a program calling them is stuck).
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

/-! ## The outcomes of the operations on an end -/

/-- What a read returns: bytes, EOF, an error; or it waits. -/
inductive ReadRes where
  | bytes (bs : List w8)
  | eof
  | err
  | wait

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
  (d.status = .cut ∧ r = .err ∧ d' = d) ∨
  -- a timeout
  (st.rdl = true ∧ r = .err ∧ d' = d)

/-- D1. A read of `n` bytes at an end in state `st`, from the direction `d` towards it: its result
`r` and the direction after, `d'`. The connection may break at the read (a prefix of the unread
bytes survives, and the read answers as a read of the broken direction does: bytes, EOF or an
error), which is also how the death of the writer's process or machine shows. -/
def ReadOutcome (st : TcpEnd) (d : TcpDir) (n : Nat) (r : ReadRes) (d' : TcpDir) : Prop :=
  if st.closed then r = .err ∧ d' = d
  else if n = 0 then r = .bytes [] ∧ d' = d
  else ReadAvail st d n r d' ∨
    -- the connection breaks now
    (∃ k, k ≤ d.bytes.length ∧ ReadAvail st ⟨d.bytes.take k, .cut⟩ n r d')

/-- D2. A write of `bs` at an end in state `st`, into the direction `d` from it: the count `k` it
returns, whether it succeeded (`ok`), and the direction after, `d'`. -/
def WriteOutcome (st : TcpEnd) (d : TcpDir) (bs : List w8) (k : Nat) (ok : Bool)
    (d' : TcpDir) : Prop :=
  if st.closed || decide (d.status = .fin) then k = 0 ∧ ok = false ∧ d' = d
  else if d.status = .cut then
    -- discarded
    ((k = bs.length ∧ ok = true) ∨ (k < bs.length ∧ ok = false)) ∧ d' = d
  else
    -- all of it
    (k = bs.length ∧ ok = true ∧ d' = { d with bytes := d.bytes ++ bs }) ∨
    -- a prefix, and the connection breaks
    (k < bs.length ∧ ok = false ∧ d' = ⟨d.bytes ++ bs.take k, .cut⟩) ∨
    -- a prefix, and a timeout
    (st.wdl = true ∧ k < bs.length ∧ ok = false ∧ d' = { d with bytes := d.bytes ++ bs.take k })

/-- `d` shut by its writer, if it is open. -/
def TcpDir.shut (d : TcpDir) : TcpDir :=
  if d.status = .open then { d with status := .fin } else d

/-- D3. A close of an end in state `st` whose direction is `d`: the result, the end's state and
the direction after. -/
def CloseOutcome (st : TcpEnd) (d : TcpDir) (ok : Bool) (st' : TcpEnd) (d' : TcpDir) : Prop :=
  if st.closed then ok = false ∧ st' = st ∧ d' = d
  else st' = { st with closed := true } ∧ d' = d.shut

/-- D4. A `CloseWrite` of an end in state `st` whose direction is `d`: the result and the
direction after. -/
def CloseWriteOutcome (st : TcpEnd) (d : TcpDir) (ok : Bool) (d' : TcpDir) : Prop :=
  if st.closed then ok = false ∧ d' = d
  else (ok = true ∧ d' = d.shut) ∨ (ok = false ∧ d' = d)

/-- D5. Setting the deadlines of kind `kind` (`0` both, `1` the read deadline, `2` the write
deadline) of an end in state `st` (`set`: the time is not zero): the result and the end's state
after. -/
def DeadlineOutcome (st : TcpEnd) (kind : w64) (set : Bool) (ok : Bool) (st' : TcpEnd) : Prop :=
  if st.closed then ok = false ∧ st' = st
  else ok = true ∧
    st' = { st with rdl := if kind = W64 2 then st.rdl else set,
                    wdl := if kind = W64 1 then st.wdl else set }

/-- Go's `Time.IsZero` (`time.go`): `t.wall == 0 && t.ext == 0`, of a `time.Time`'s two words. -/
def timeIsZero (wall ext : w64) : Bool := wall == 0 && ext == 0

/-! ## The step relation -/

section step
variable [GooseExts] [GoGlobalContext]

/-- The value of a read's result, as the trusted model takes it apart: the bytes and the code
(`0` ok, `1` EOF, `2` error). -/
def readRes (bs : List w8) (code : w64) : val := PairV (#bs) (#code)

/-- The value of a read's result `r` (`op` itself if it waits). -/
def ReadRes.toExpr (op : Expr) : ReadRes → Expr
  | .bytes bs => Val (readRes bs 0)
  | .eof => Val (readRes [] 1)
  | .err => Val (readRes [] 2)
  | .wait => op

/-- `"Read"` of `n` bytes at the end `s` of `c`. -/
def ReadStep (op : Expr) (c : Nat) (s : Bool) (n : w64) (g : TcpGlobal) (e' : Expr)
    (g' : TcpGlobal) : Prop :=
  ∃ cn r d', g.conns !! c = some cn ∧ ReadOutcome (cn.endSt s) (cn.out (!s)) n.toNat r d' ∧
    e' = r.toExpr op ∧ g' = g.setConn c (cn.setOut (!s) d')

/-- `"Write"` of `bs` at the end `s` of `c`. -/
def WriteStep (c : Nat) (s : Bool) (bs : List w8) (g : TcpGlobal) (e' : Expr) (g' : TcpGlobal) :
    Prop :=
  ∃ cn k ok d', g.conns !! c = some cn ∧ WriteOutcome (cn.endSt s) (cn.out s) bs k ok d' ∧
    e' = Val (PairV (#(BitVec.ofNat 64 k)) (#ok)) ∧ g' = g.setConn c (cn.setOut s d')

/-- `"Close"` of the end `s` of `c`. -/
def CloseStep (c : Nat) (s : Bool) (g : TcpGlobal) (e' : Expr) (g' : TcpGlobal) : Prop :=
  ∃ cn ok st' d', g.conns !! c = some cn ∧ CloseOutcome (cn.endSt s) (cn.out s) ok st' d' ∧
    e' = Val (#ok) ∧ g' = g.setConn c ((cn.setEnd s st').setOut s d')

/-- `"CloseWrite"` of the end `s` of `c`. -/
def CloseWriteStep (c : Nat) (s : Bool) (g : TcpGlobal) (e' : Expr) (g' : TcpGlobal) : Prop :=
  ∃ cn ok d', g.conns !! c = some cn ∧ CloseWriteOutcome (cn.endSt s) (cn.out s) ok d' ∧
    e' = Val (#ok) ∧ g' = g.setConn c (cn.setOut s d')

/-- `"SetDeadline"` of the deadlines of kind `kind` of the end `s` of `c`. -/
def SetDeadlineStep (c : Nat) (s : Bool) (kind : w64) (set : Bool) (g : TcpGlobal) (e' : Expr)
    (g' : TcpGlobal) : Prop :=
  ∃ cn ok st', g.conns !! c = some cn ∧ DeadlineOutcome (cn.endSt s) kind set ok st' ∧
    e' = Val (#ok) ∧ g' = g.setConn c (cn.setEnd s st')

/-- `"Dial"` of `a`. -/
def DialStep (a : GoString) (g : TcpGlobal) (e' : Expr) (g' : TcpGlobal) : Prop :=
  (g.plan !! a).isSome ∧
  ((e' = Val (PairV (#(W64 0)) (#false)) ∧ g' = g) ∨
   (∃ c, g.conns !! c = none ∧ 2 * c + 1 < 2 ^ 64 ∧
     e' = Val (PairV (#(endId c false)) (#true)) ∧
     g' = g.setConn c (TcpConn.fresh a)))

/-- `"Accept"` of `l`, for the listener `(a, isOpen)`. -/
def AcceptStep (op : Expr) (a : GoString) (isOpen : Bool) (g : TcpGlobal) (e' : Expr)
    (g' : TcpGlobal) : Prop :=
  (e' = Val (PairV (#(W64 0)) (#false)) ∧ g' = g) ∨
  (isOpen = true ∧ e' = op ∧ g' = g) ∨
  (isOpen = true ∧ ∃ c cn, g.conns !! c = some cn ∧ cn.addr = a ∧ cn.accepted = false ∧
    2 * c + 1 < 2 ^ 64 ∧
    e' = Val (PairV (#(endId c true)) (#true)) ∧
    g' = g.setConn c { cn with accepted := true })

/-- `"Listen"` of `a` by the node with state `L`. -/
def ListenStep (a : GoString) (g : TcpGlobal) (L : TcpLocal) (e' : Expr) (L' : TcpLocal) : Prop :=
  g.plan !! a = some L.host ∧
  ((e' = Val (PairV (#(W64 0)) (#false)) ∧ L' = L) ∨
   ((∀ l, L.lis !! l ≠ some (a, true)) ∧ ∃ l, L.lis !! l = none ∧
     e' = Val (PairV (#l) (#true)) ∧ L' = { L with lis := L.lis.insert l (a, true) }))

/-- The step relation of the TCP extension, for a node with local state `L` on the network `g`. -/
def TcpStep (op : String) (v : val) (h : GMap Loc (NonAtomic val)) (L : TcpLocal) (g : TcpGlobal)
    (e' : Expr) (h' : GMap Loc (NonAtomic val)) (L' : TcpLocal) (g' : TcpGlobal) : Prop :=
  h' = h ∧
  match op with
  | "Listen" => ∃ a : GoString, v = #a ∧ ListenStep a g L e' L' ∧ g' = g
  | "Accept" => ∃ (l : w64) (a : GoString) (o : Bool), v = #l ∧ L.lis !! l = some (a, o) ∧
      AcceptStep (ExternalOp tcpExt.name "Accept" (Val v)) a o g e' g' ∧ L' = L
  | "LisClose" => ∃ (l : w64) (a : GoString) (o : Bool), v = #l ∧ L.lis !! l = some (a, o) ∧
      g' = g ∧
      (if o then e' = Val (#true) ∧ L' = { L with lis := L.lis.insert l (a, false) }
       else e' = Val (#false) ∧ L' = L)
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
  | _ => False

end step

/-- D10. A crash keeps the host and drops the listeners. -/
instance tcp_semantics : ExtSemantics tcpExt where
  step := TcpStep
  crash L L' := L' = { L with lis := ∅ }

end Tcp

end Perennial
