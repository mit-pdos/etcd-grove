/-
The TCP extension of GooseLang [Trusted definitions!]: the semantics of Go's `net` package's TCP
connections, between the nodes of a distributed system (Perennial's `DistLang.lean`). Its
operations are the socket layer under `net`'s exported API; the trusted models of `net`'s
functions and methods (`NetTcp/TrustedCode/net.lean`) call them. The design and its justification
are `notes/net-tcp.md`; the decisions are summarized here.

**State.** The global state (`TcpGlobal`) is the network: the deployment's plan (`plan`: each
address string the program may use, and the host that may listen at it) and every connection ever
dialed (`conns`). A connection (`TcpConn`) has the address it was dialed to, whether it has been
accepted, and two ends, the dialer's (`false`) and the acceptor's (`true`), each with its own state
(`TcpEnd`: closed, its write side shut, broken, a deadline set) and its *out-pipe* (`TcpPipe`): the
bytes the end has written (`sent`, in order, every byte ever written), how many of them the other
end has read (`rcvd`), and whether the end has sent its FIN (`fin`). The bytes written and not yet
read, `sent.drop rcvd`, are the bytes in flight. The local state of a node (`TcpLocal`) is its host
name and its listeners, each an address and whether it is open.

**Handles.** A connection end is named by a 64-bit id, `2 c + s` for the connection `c` and the
side `s` (0 the dialer, 1 the acceptor); a listener by a 64-bit id of its node. An operation on an
id that names nothing is stuck: the trusted models only pass ids the extension returned, which a
Go program cannot forge (they are inside `net`'s unexported structs, and the heap does not survive
a crash).

**Operations** (`TcpStep`; none changes the heap; results are pairs, as goose returns a Go
function's results). Every operation that can fail may fail at any time: a failure is what the
network or the kernel may do (a reset, a timeout, an exhausted resource), which the model does not
explain. The guarantees are only what a failure cannot break:

* `"Listen"` of an address `a`: stuck unless `a` is in the plan with this node's host. A new open
  listener at `a` (`(id, true)`); or a failure (`(0, false)`), which is the only outcome if this
  node already has an open listener at `a` (`EADDRINUSE`).
* `"Accept"` of a listener `l`: a connection dialed to `l`'s address and not yet accepted, now
  accepted (`(2 c + 1, true)`); or a failure, the only outcome once `l` is closed; or it waits.
  Any such connection, whenever it was dialed: also one dialed before this node's last crash, or
  before `l` was opened (more than a real kernel, whose accept queue is the listener's own; sound).
* `"LisClose"` of `l`: closes it (`true`); a failure (`false`) if it is closed already.
* `"Dial"` of `a`: stuck unless `a` is in the plan. A new connection to `a`, not yet accepted,
  both ends open (`(2 c, true)`); or a failure. It does not look for a listener: a dial nobody
  accepts is a connection never accepted (more than reality, where it fails; sound).
* `"Read"` of `(e, n)`, `n` the buffer's length: nothing but a failure once `e` is closed.
  Otherwise, `n = 0` returns no bytes; else the next `k` bytes in flight towards `e`, for some
  `1 ≤ k ≤ n` (as many as arrived: any number), in order; or EOF, once no byte is in flight and the
  other end has sent its FIN; or it waits; or a failure. Results `(bytes, code)`, the code `0` (ok),
  `1` (EOF) or `2` (failure).
* `"Write"` of `(e, bytes)`: a failure, writing nothing, once `e` is closed, shut for writing or
  broken. Otherwise all the bytes appended to `e`'s out-pipe (`(len, true)`), or a prefix of them,
  shorter, and a failure (`(k, false)`). Go's `Write` writes all or fails.
* `"Close"` of `e`: a failure if it is closed already; otherwise `e` closed and its FIN sent, unless
  it is broken or its FIN was sent already; the result may be a failure all the same.
* `"CloseWrite"` of `e`: a failure if it is closed; otherwise its write side shut and its FIN sent
  (unless broken or sent already), or a failure that changes nothing.
* `"SetDeadline"` of `e` (any of `conn`'s three deadline setters): a failure if it is closed;
  otherwise it records that a deadline was set (the deadline itself is not modeled: an operation may
  fail at any time anyway).
* `"AnyBool"`, `"AnyString"`: an arbitrary value (the parts of an error that the model does not
  explain: `OpError.Timeout`, `Temporary`, `Error`).

**Broken connections, and when a FIN is sent.** On Linux, an error from a read or a write of a TCP
socket with no deadline is a dead connection (`ECONNRESET`, `ETIMEDOUT`, `EPIPE`: the kernel has
dropped it); its later close sends no FIN. So a failed read or write of an end with no deadline set
marks it broken (`broken`): it writes nothing more, and its close sends no FIN. With a deadline, a
failure may be a timeout of a live connection, which a later close does FIN: a failure then marks
nothing. So EOF means: the writer closed its end (or shut its write side) after every write it made
succeeded, or with a deadline set. (Memory exhaustion in the kernel, `ENOMEM`/`ENOBUFS`, a failure
of a live connection with no deadline, is not modeled, as the file extensions' allocation failures.)

**Crashes** (`crash`): a node's crash is a machine's crash. It changes nothing of the network
(`DistLang`'s crash keeps the global state): the bytes in flight stay in flight, and the other ends
may still read them; the crashed node's ends send no FIN (its threads and heap are gone, so nothing
acts on them again). Its listeners are gone (`lis` empty), so the restarted node may listen at its
addresses again. The host is kept.

**What is not modeled.** A process that exits: Go's runtime closes its sockets, which FINs them; the
programs proved over this model never exit (every node's boot program ends by blocking forever,
`examples/net/doc.go`), and a theorem says nothing of one that does. Addresses are the plan's
strings, compared as strings: the plan's strings must name distinct sockets (no two strings for one
`host:port`), an assumption of the deployment; `Listen` or `Dial` of any other string is stuck.
Ports `0`, TLS, UDP, Unix sockets, `LocalAddr`/`RemoteAddr`, the deadlines' times, keepalives: not
modeled (the methods are not modeled either, so a program calling them is stuck).
-/
module

public import Perennial.GooseLang.Lang

@[expose] public section

namespace Perennial

namespace Tcp

/-- The state of one end of a connection. -/
structure TcpEnd where
  /-- `Close` was called. -/
  closed : Bool
  /-- `CloseWrite` was called: the end writes nothing more. -/
  wshut : Bool
  /-- An operation failed with no deadline set: the connection is dead at this end. -/
  broken : Bool
  /-- A deadline was set (ever). -/
  dl : Bool
deriving DecidableEq, Inhabited

/-- A fresh end. -/
def TcpEnd.fresh : TcpEnd := ⟨false, false, false, false⟩

/-- The out-pipe of an end: every byte it wrote, how many the other end has read, and whether it
has sent its FIN. -/
structure TcpPipe where
  sent : List w8
  rcvd : Nat
  fin : Bool
deriving DecidableEq, Inhabited

/-- An empty pipe. -/
def TcpPipe.fresh : TcpPipe := ⟨[], 0, false⟩

/-- A connection: its address, whether it was accepted, and its two ends (`false` the dialer,
`true` the acceptor), each with its state and its out-pipe. -/
structure TcpConn where
  addr : GoString
  accepted : Bool
  dEnd : TcpEnd
  aEnd : TcpEnd
  /-- The dialer's out-pipe (towards the acceptor). -/
  up : TcpPipe
  /-- The acceptor's out-pipe (towards the dialer). -/
  down : TcpPipe
deriving Inhabited

/-- A new connection to `a`. -/
def TcpConn.fresh (a : GoString) : TcpConn :=
  ⟨a, false, TcpEnd.fresh, TcpEnd.fresh, TcpPipe.fresh, TcpPipe.fresh⟩

/-- The state of the end `s` of `c`. -/
def TcpConn.endSt (c : TcpConn) : Bool → TcpEnd
  | false => c.dEnd
  | true => c.aEnd

/-- The out-pipe of the end `s` of `c`. -/
def TcpConn.out (c : TcpConn) : Bool → TcpPipe
  | false => c.up
  | true => c.down

/-- `c` with the state of its end `s` replaced. -/
def TcpConn.setEnd (c : TcpConn) : Bool → TcpEnd → TcpConn
  | false, st => { c with dEnd := st }
  | true, st => { c with aEnd := st }

/-- `c` with the out-pipe of its end `s` replaced. -/
def TcpConn.setOut (c : TcpConn) : Bool → TcpPipe → TcpConn
  | false, p => { c with up := p }
  | true, p => { c with down := p }

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

/-! ## The step relation -/

section step
variable [GooseExts] [GoGlobalContext]

/-- The end state after a failure: broken unless a deadline was set. -/
def TcpEnd.onFail (st : TcpEnd) : TcpEnd := if st.dl then st else { st with broken := true }

/-- The out-pipe after the end's FIN, if it is not broken. -/
def TcpPipe.finIf (st : TcpEnd) (p : TcpPipe) : TcpPipe :=
  if st.broken then p else { p with fin := true }

/-- The result of a read: the bytes and the code (`0` ok, `1` EOF, `2` failure). -/
def readRes (bs : List w8) (code : w64) : val := PairV (#bs) (#code)

/-- `"Read"` of `(e, n)` on the network `g`, giving `e'` and `g'`: `e` is the end `s` of `c`.
The bytes come from the other end's out-pipe. -/
def ReadStep (op : Expr) (c : Nat) (s : Bool) (n : w64) (g : TcpGlobal) (e' : Expr)
    (g' : TcpGlobal) : Prop :=
  ∃ cn, g.conns !! c = some cn ∧
  let st := cn.endSt s
  let p := cn.out (!s)
  -- it waits
  (e' = op ∧ g' = g) ∨
  -- a failure
  (e' = Val (readRes [] 2) ∧ g' = g.setConn c (cn.setEnd s st.onFail)) ∨
  (st.closed = false ∧
    ( -- an empty buffer
      (n = 0 ∧ e' = Val (readRes [] 0) ∧ g' = g) ∨
      -- the next `k` bytes in flight
      (∃ k, 1 ≤ k ∧ k ≤ n.toNat ∧ p.rcvd + k ≤ p.sent.length ∧
        e' = Val (readRes ((p.sent.drop p.rcvd).take k) 0) ∧
        g' = g.setConn c (cn.setOut (!s) { p with rcvd := p.rcvd + k })) ∨
      -- EOF
      (p.rcvd = p.sent.length ∧ p.fin = true ∧ e' = Val (readRes [] 1) ∧ g' = g)))

/-- `"Write"` of `(e, bs)`: `e` is the end `s` of `c`. -/
def WriteStep (c : Nat) (s : Bool) (bs : List w8) (g : TcpGlobal) (e' : Expr) (g' : TcpGlobal) :
    Prop :=
  ∃ cn, g.conns !! c = some cn ∧
  let st := cn.endSt s
  let p := cn.out s
  if st.closed || st.wshut || st.broken then
    e' = Val (PairV (#(W64 0)) (#false)) ∧ g' = g
  else
    -- all of it
    (e' = Val (PairV (#(BitVec.ofNat 64 bs.length)) (#true)) ∧
      g' = g.setConn c (cn.setOut s { p with sent := p.sent ++ bs })) ∨
    -- a shorter prefix, and a failure
    (∃ k, k < bs.length ∧ e' = Val (PairV (#(BitVec.ofNat 64 k)) (#false)) ∧
      g' = g.setConn c ((cn.setOut s { p with sent := p.sent ++ bs.take k }).setEnd s st.onFail))

/-- `"Close"` of `e`, the end `s` of `c`. -/
def CloseStep (c : Nat) (s : Bool) (g : TcpGlobal) (e' : Expr) (g' : TcpGlobal) : Prop :=
  ∃ cn, g.conns !! c = some cn ∧
  let st := cn.endSt s
  if st.closed then e' = Val (#false) ∧ g' = g
  else ∃ ok : Bool, e' = Val (#ok) ∧
    g' = g.setConn c ((cn.setOut s ((cn.out s).finIf st)).setEnd s { st with closed := true })

/-- `"CloseWrite"` of `e`, the end `s` of `c`. -/
def CloseWriteStep (c : Nat) (s : Bool) (g : TcpGlobal) (e' : Expr) (g' : TcpGlobal) : Prop :=
  ∃ cn, g.conns !! c = some cn ∧
  let st := cn.endSt s
  (e' = Val (#false) ∧ g' = g) ∨
  (st.closed = false ∧ e' = Val (#true) ∧
    g' = g.setConn c ((cn.setOut s ((cn.out s).finIf st)).setEnd s { st with wshut := true }))

/-- `"SetDeadline"` of `e`, the end `s` of `c`. -/
def SetDeadlineStep (c : Nat) (s : Bool) (g : TcpGlobal) (e' : Expr) (g' : TcpGlobal) : Prop :=
  ∃ cn, g.conns !! c = some cn ∧
  let st := cn.endSt s
  if st.closed then e' = Val (#false) ∧ g' = g
  else e' = Val (#true) ∧ g' = g.setConn c (cn.setEnd s { st with dl := true })

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
  (e' = op ∧ g' = g) ∨
  (e' = Val (PairV (#(W64 0)) (#false)) ∧ g' = g) ∨
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
  | "SetDeadline" => ∃ (e : w64) (c : Nat) (s : Bool), v = #e ∧ IsEnd e c s ∧
      SetDeadlineStep c s g e' g' ∧ L' = L
  | "AnyBool" => v = #() ∧ (∃ b : Bool, e' = Val (#b)) ∧ L' = L ∧ g' = g
  | "AnyString" => v = #() ∧ (∃ str : GoString, e' = Val (#str)) ∧ L' = L ∧ g' = g
  | _ => False

end step

/-- A crash keeps the host and drops the listeners. -/
instance tcp_semantics : ExtSemantics tcpExt where
  step := TcpStep
  crash L L' := L' = { L with lis := ∅ }

end Tcp

end Perennial
