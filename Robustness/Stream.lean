/-
Robustness statements over a connection-oriented network (TCP) [Trusted definitions!].

**What an observer sees** (`StreamEv`): bytes written into a connection, by its dialer or by its
acceptor, with the address it was dialed to. A trace of them is all a client can tell about a
server: which bytes went in which direction of which connection, in what order relative to the
others.

**What a network semantics provides** (`StreamNet`, a class an extension instantiates; its
instance is part of the statement's meaning, so trusted): the events of a change of the shared
state (`obs`); a node's host (`host`), which the deployment's plan ties to addresses; the shared
state at a deployment's start with a plan of addresses and no connection (`fresh`); a node's local
state with no listener (`freshNode`). The TCP extension of branch `net-tcp`
(`GooseLang/Ext/Tcp/Impl.lean`: a global state of the plan and the connections, each direction its
unread bytes and a status; a node's local state its host and listeners) instantiates it as: `obs g
g'`, for the one connection whose direction's unread bytes grew by a suffix `bs` (a `"Write"`
step), the event of `bs` (a read only removes a prefix, a cut keeps a prefix, a dial adds an empty
connection: no event); `host` the local state's host; `fresh plan g` the plan `GMap.ofList plan`,
well formed (`PlanWellFormed`), and no connection; `freshNode` no listener.

**No world moves** (`World.ofStream`). Such a network allows every network fault at every step: a
direction may break at any read or write, keeping a prefix of its unread bytes; bytes wait any
time (a schedule); a dial may fail. A partition, a reset by a middlebox, loss and delay are
therefore runs of the semantics, not moves of the environment.

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

/-- What a robustness statement needs of a network semantics with connections (see the file
header). -/
class StreamNet [GooseExts] where
  /-- the bytes a change of the shared state wrote, oldest first -/
  obs : GlobalState → GlobalState → List StreamEv
  /-- the host of the node with this local state -/
  host : state → GoString
  /-- the shared state at a deployment's start: the plan `plan` (each address and the host that
  may listen at it), well formed, and no connection -/
  fresh : List (GoString × GoString) → GlobalState → Prop
  /-- a node's local state at its first start: no listener -/
  freshNode : state → Prop

section stream
variable [GooseExts] [GooseSemantics] [GoGlobalContext]

/-- The world of a network semantics with connections: no moves (every fault is the semantics'),
its observation. -/
def World.ofStream [StreamNet] : World StreamEv := ⟨fun _ _ => False, StreamNet.obs⟩

end stream

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

/-- The operation event at the `j`-th event of the trace `tr`, under the protocol `P`, if any: a
call when the dialer's write completes its connection's request, a return when the acceptor's
write completes the answer to it. -/
def opEventAt (P : ReqResp K I O) (tr : List (Timed StreamEv)) (j : Nat) :
    Option (Nat × OpEv K I O) :=
  match tr[j]? with
  | none => none
  | some x =>
    let e := x.ev
    let before := (tr.take j).map Timed.ev
    let upto := (tr.take (j + 1)).map Timed.ev
    let q := P.req e.addr (streamBytes upto e.conn false)
    if e.fromAcceptor then
      match P.resp (streamBytes before e.conn true), P.resp (streamBytes upto e.conn true), q with
      | none, some o, some (k, _) => some (x.time, .ret k o)
      | _, _, _ => none
    else
      match P.req e.addr (streamBytes before e.conn false), q with
      | none, some (k, i) => some (x.time, .call k i)
      | _, _ => none

/-- The operation events of the trace `tr` under the protocol `P`, in order. -/
def opEvents (P : ReqResp K I O) (tr : List (Timed StreamEv)) : List (Nat × OpEv K I O) :=
  (List.range tr.length).filterMap (opEventAt P tr)

end Robustness
end Perennial
