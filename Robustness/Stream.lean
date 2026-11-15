/-
Robustness statements over the TCP extension (`GooseLang/Ext/Tcp/Impl.lean`) [Trusted
definitions!]: what an observer of the network sees of a run.

**What an observer sees** (`StreamEv`): bytes written into a connection, by its dialer or by its
acceptor, with the address it was dialed to. A trace of them is all a client can tell about a
server: which bytes went in which direction of which connection, in what order relative to the
others.

**The events of a step** (`tcpObs`). The extension's network keeps only what a program can
observe (each direction's unread bytes and its status), not what was sent, so the events are read
off a step's change of it: a direction whose unread bytes grew by a suffix `bs` had `bs` written
into it (`appended`). That is exactly a `"Write"` step into an open direction (`WriteOutcome`):
a read only removes a prefix, a cut keeps a prefix, a dial adds a connection with empty
directions, and no other step changes a direction's bytes (`appended_write`, `appended_read`). A
step changes at most one direction, so it has at most one event. Bytes written into a broken
direction are discarded by the semantics and are no event: nobody can read them.

`streamTrace` is the events of a run's global states, each with the index of its step (the time:
the run's interleaving is the order in which things happen); `envStream` the events of the
environment's steps (`Statement.lean`'s `envSteps`), without times.

Every network fault is the semantics' (a direction may break at any read or write, keeping a
prefix of its unread bytes; bytes wait any time, a schedule; a dial may fail): a partition, a
reset by a middlebox, loss and delay are runs of `DistCrashStep`.

**Requests and answers** (`ReqResp`, `opEvents`): a service whose clients send one request on a
connection and read one answer (or several, retried, on other connections) gives operation events:
the call of an operation at the event that completes its request (the dialer's bytes so far first
decode as one), the return at the event that completes its answer (the acceptor's bytes so far
first decode as one), of the operation of that connection's request. A request is complete when
the client wrote its last byte, and an answer when the server wrote its last byte: the operation's
interval is at most what the client sees (it reads the answer later), so its linearizability is at
least as strong as the client's view of it.
-/
module

public import Robustness.Statement
public import Robustness.Linearizability
public import GooseLang.Ext.Tcp.Impl

@[expose] public section

noncomputable section

namespace Perennial
namespace Robustness

/-- Bytes `data` written into the connection `conn`, dialed to the address `addr`, by its acceptor
(`fromAcceptor`) or its dialer. -/
structure StreamEv where
  conn : Nat
  addr : GoString
  fromAcceptor : Bool
  data : List w8

/-- The bytes a step appended to a direction, from the direction before (`d`) and after (`d'`):
what `d'`'s unread bytes have after `d`'s, when they extend them. -/
def appended (d d' : Tcp.TcpDir) : List w8 :=
  if d.bytes <+: d'.bytes then d'.bytes.drop d.bytes.length else []

/-- The events of a step that changes the network from `g` to `g'`: for each connection of `g`
and each of its ends, the bytes the step appended to the direction from it, if any. -/
def tcpObs (g g' : Tcp.TcpGlobal) : List StreamEv :=
  g.conns.toList.flatMap fun x =>
    match g'.conns.lookup x.1 with
    | none => []
    | some cn' => [false, true].filterMap fun s =>
      match appended (x.2.out s) (cn'.out s) with
      | [] => none
      | bs => some ⟨x.1, x.2.addr, s, bs⟩

section trace
variable [GooseExts] [ElemExt Tcp.tcpExt]

/-- The network of a global state. -/
abbrev netOf (g : GlobalState) : Tcp.TcpGlobal := extGlobal Tcp.tcpExt g.globalWorld

/-- The events of the global states `gs` of a run, each with the index of the step that made it
(step `j` is the one from `gs[j]` to `gs[j + 1]`). -/
def streamTrace (gs : List GlobalState) : List (Nat × StreamEv) :=
  (gs.zip gs.tail).zipIdx.flatMap fun x => (tcpObs (netOf x.1.1) (netOf x.1.2)).map (x.2, ·)

/-- The events of the steps `steps` (each the global state before and after), in order. -/
def envStream (steps : List (GlobalState × GlobalState)) : List StreamEv :=
  steps.flatMap fun x => tcpObs (netOf x.1) (netOf x.2)

end trace

/-! ## Sanity: only a write into an open direction appends -/

/-- A write of `bs` into a direction appends `bs`. -/
theorem appended_write (d : Tcp.TcpDir) (bs : List w8) :
    appended d { d with bytes := d.bytes ++ bs } = bs := by
  simp [appended]

/-- A read of `k` bytes from a direction, or a cut that keeps `k` of them, appends nothing. -/
theorem appended_read (d : Tcp.TcpDir) (k : Nat) (st : Tcp.TcpStatus) :
    appended d ⟨d.bytes.drop k, st⟩ = [] ∧ appended d ⟨d.bytes.take k, st⟩ = [] := by
  constructor <;>
  · simp only [appended]
    split
    · rename_i h
      have := h.length_le
      simp only [List.length_drop, List.length_take] at this
      exact List.drop_eq_nil_of_le (by simp only [List.length_drop, List.length_take]; omega)
    · rfl

/-- The bytes the events `evs` wrote into the direction of connection `c` from its acceptor
(`s = true`) or its dialer, in order. -/
def streamBytes (evs : List StreamEv) (c : Nat) (s : Bool) : List w8 :=
  (evs.filter fun e => e.conn = c && e.fromAcceptor == s).flatMap StreamEv.data

/-- A request/response protocol: the operation (its key and input) of a connection to the address
`a` whose dialer wrote `bs` (`req a bs`: `none` until the request is complete, or if it is not
one); the output of an answer whose acceptor wrote `bs` (`resp bs`). -/
structure ReqResp (K I O : Type) where
  req : GoString → List w8 → Option (K × I)
  resp : List w8 → Option O

variable {K I O : Type}

/-- The operation event at the `j`-th event of the trace `tr` (events with their times), under the protocol `P`, if any: a
call when the dialer's write completes its connection's request, a return when the acceptor's
write completes the answer to it. -/
def opEventAt (P : ReqResp K I O) (tr : List (Nat × StreamEv)) (j : Nat) :
    Option (Nat × OpEv K I O) :=
  match tr[j]? with
  | none => none
  | some x =>
    let e := x.2
    let before := (tr.take j).map Prod.snd
    let upto := (tr.take (j + 1)).map Prod.snd
    let q := P.req e.addr (streamBytes upto e.conn false)
    if e.fromAcceptor then
      match P.resp (streamBytes before e.conn true), P.resp (streamBytes upto e.conn true), q with
      | none, some o, some (k, _) => some (x.1, .ret k o)
      | _, _, _ => none
    else
      match P.req e.addr (streamBytes before e.conn false), q with
      | none, some (k, i) => some (x.1, .call k i)
      | _, _ => none

/-- The operation events of the trace `tr` under the protocol `P`, in order. -/
def opEvents (P : ReqResp K I O) (tr : List (Nat × StreamEv)) : List (Nat × OpEv K I O) :=
  (List.range tr.length).filterMap (opEventAt P tr)

end Robustness
end Perennial
