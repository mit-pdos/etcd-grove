/-
Lean-first (no Rocq counterpart). Trace-check's layer B, Draft (2026-11-09): the simulation's
ghost state (`notes/trace-validation-sim.md`, revision 13, "Phases" and "The messages").

- `TraceNames`, `traceDir`: the simulation's ghost names, in a persistent directory that the
  cluster's `γ.raft.reTrace = some γd` names (so names can be added without changing `RaftNames`);
- `simInit C`: the specification's state after the bootstrap of the voters `C` (each node's
  bootstrap lines, which `TraceNext` steps over);
- `SimRun C L σ`: the trace so far, `L`, runs line by line from `simInit C` to `σ`, as TLC's
  verdict needs (`Trace.RunRel`: one state per line, no branching, the invariants);
- `simNode tn i c P`: node `i`'s share, its server `c` and its pending messages `P`; `inFlight tn
  k m`: the token of a handed-out message (at most once, after its sender's `Ready`: the user's,
  2026-11-08);
- `simInv C tn`: the trace's simulation half, the specification's state, the shares' and tokens'
  authorities, and the phantom replies (requests of a lower term the specification answers and
  raft, check-quorum and pre-vote off, ignores).
-/
module

public import Proof.go_etcd_io.raft.v3.TraceSim

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

namespace TraceSim

/-! ## Countability of the specification's values (to store them in ghost state) -/

instance entryType_countable : Pos.Countable Etcdraft.EntryType :=
  countableOfLeftInverse (fun t : Etcdraft.EntryType => match t with | .value => false | .config => true)
    (fun b => if b then .config else .value) (fun t => by cases t <;> rfl)

instance value_countable : Pos.Countable Etcdraft.Value :=
  countableOfLeftInverse
    (fun v : Etcdraft.Value => match v with
      | .val n => (Sum.inl n : Int ⊕ (Unit ⊕ (List Nat × List Nat)))
      | .emptySeq => Sum.inr (Sum.inl ())
      | .conf nc ln => Sum.inr (Sum.inr (nc, ln)))
    (fun x => match x with
      | .inl n => .val n
      | .inr (.inl _) => .emptySeq
      | .inr (.inr p) => .conf p.1 p.2)
    (fun v => by cases v <;> rfl)

instance entry_countable : Pos.Countable Etcdraft.Entry :=
  countableOfLeftInverse (fun e : Etcdraft.Entry => (e.term, e.type, e.value))
    (fun p => ⟨p.1, p.2.1, p.2.2⟩) (fun _ => rfl)

instance config_countable : Pos.Countable Etcdraft.Config :=
  countableOfLeftInverse (fun c : Etcdraft.Config => (c.incoming, c.outgoing, c.learners))
    (fun p => ⟨p.1, p.2.1, p.2.2⟩) (fun _ => rfl)

instance durable_countable : Pos.Countable Etcdraft.Durable :=
  countableOfLeftInverse (fun d : Etcdraft.Durable => (d.currentTerm, d.votedFor, d.log, d.commitIndex, d.config))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2⟩) (fun _ => rfl)

instance msgType_countable : Pos.Countable Etcdraft.MsgType :=
  countableOfLeftInverse
    (fun t : Etcdraft.MsgType => match t with
      | .requestVoteRequest => (0 : Nat) | .requestVoteResponse => 1 | .appendEntriesRequest => 2
      | .appendEntriesResponse => 3 | .preVoteRequest => 4 | .preVoteResponse => 5)
    (fun n => match n with
      | 0 => .requestVoteRequest | 1 => .requestVoteResponse | 2 => .appendEntriesRequest
      | 3 => .appendEntriesResponse | 4 => .preVoteRequest | _ => .preVoteResponse)
    (fun t => by cases t <;> rfl)

instance msg_countable : Pos.Countable Etcdraft.Msg :=
  countableOfLeftInverse
    (fun m : Etcdraft.Msg => (m.type, m.subtype, m.term, m.lastLogTerm, m.lastLogIndex, m.voteGranted,
      m.prevLogIndex, m.prevLogTerm, m.entries, m.commitIndex, m.success, m.matchIndex, m.source, m.dest))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2.1,
      p.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2.1,
      p.2.2.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2.2.2.2⟩)
    (fun _ => rfl)

/-- A server's variables with `matchIndex` on a list of servers (a `Server`'s `matchIndex` is a
function, which ghost state cannot hold; the specification compares it on the servers only). -/
structure ServerC where
  currentTerm : Int
  state : Etcdraft.Role
  votedFor : Etcdraft.ID
  lead : Etcdraft.ID
  log : List Etcdraft.Entry
  commitIndex : Int
  votesResponded : Etcdraft.SetIds
  votesGranted : Etcdraft.SetIds
  matchIndex : List Int
  pendingConfChangeIndex : Int
  config : Etcdraft.Config
  durable : Etcdraft.Durable

instance serverC_countable : Pos.Countable ServerC :=
  countableOfLeftInverse
    (fun v : ServerC => (v.currentTerm, v.state, v.votedFor, v.lead, v.log, v.commitIndex, v.votesResponded,
      v.votesGranted, v.matchIndex, v.pendingConfChangeIndex, v.config, v.durable))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2.1,
      p.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2.1,
      p.2.2.2.2.2.2.2.2.2.2.2⟩)
    (fun _ => rfl)

/-- A server's variables as `ServerC`, `matchIndex` on the servers `srv`. -/
def toC (srv : Etcdraft.SetIds) (v : Etcdraft.Server) : ServerC :=
  { currentTerm := v.currentTerm, state := v.state, votedFor := v.votedFor, lead := v.lead, log := v.log,
    commitIndex := v.commitIndex, votesResponded := v.votesResponded, votesGranted := v.votesGranted,
    matchIndex := srv.map v.matchIndex, pendingConfChangeIndex := v.pendingConfChangeIndex,
    config := v.config, durable := v.durable }

/-! ## The ghost names -/

/-- The simulation's ghost names: the trace (`traceAuth`/`traceFrag`), the nodes' shares, the
message tokens. -/
structure TraceNames where
  tr : GName
  st : GName
  bag : GName

instance traceNames_countable : Pos.Countable TraceNames :=
  countableOfLeftInverse (fun n : TraceNames => (n.tr, n.st, n.bag)) (fun p => ⟨p.1, p.2.1, p.2.2⟩)
    (fun _ => rfl)

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The directory: `γd` names the simulation's names `tn`, persistently. -/
def traceDir (γd : GName) (tn : TraceNames) : IProp GF := dghostVar γd DfracDiscarded tn

instance traceDir_persistent (γd : GName) (tn : TraceNames) : Persistent (traceDir (GF := GF) γd tn) := by
  unfold traceDir; infer_instance

/-! ## The initial state and the run -/

/-- The specification's state after the bootstrap of the voters `C` (`TraceInit` once every voter's
bootstrap lines are logged): each server at term 1, a follower without a vote or a leader, its log
the `|C|` bootstrap entries (0010's incremental configurations), all committed, its configuration
`C`, `matchIndex` 0, its durable state its own; no message. -/
def simInit (C : List w64) : Etcdraft.State :=
  let srv := confAbs C
  let v : Etcdraft.Server :=
    { currentTerm := 1, state := Etcdraft.follower, votedFor := Etcdraft.nil, lead := Etcdraft.nil,
      log := (List.range C.length).map (fun k =>
        { term := 1, type := .config, value := .conf (confAbs (C.take (k + 1))) [] }),
      commitIndex := C.length, votesResponded := [], votesGranted := [], matchIndex := fun _ => 0,
      pendingConfChangeIndex := 0, config := { incoming := srv, outgoing := [], learners := [] },
      durable := default }
  { server := srv, s := fun _ => { v with durable := Etcdraft.durableOf v }, messages := [],
    pendingMessages := [], reconfigCount := 0 }

/-- The trace so far runs, from `simInit C`, to `σ` (TLC's verdict on it so far: one state per
line, no branching, the invariants). The trace of a prefix is read with the voters' initial state
and server set (a voter not yet started has logged nothing; `simRun_accepts` relates it to the
whole trace's once every voter's bootstrap lines are in). -/
def SimRun (C : List w64) (L : List TraceEv) (σ : Etcdraft.State) : Prop :=
  (L = [] ∧ σ = simInit C) ∨
  ∃ t, Etcdraft.newTraceWith (L.map evConv) false false = .ok t ∧
    Etcdraft.Trace.RunRel { t with init := simInit C, server := confAbs C } L.length
      { s := σ, l := L.length + 1, pl := L.length }

/-- A bag of the messages of a list. -/
def bagOf (l : List Etcdraft.Msg) : Etcdraft.Bag := l.foldl Etcdraft.Bag.with []

/-! ## The shares and the invariant -/

/-- Node `i`'s share: its server `c` (`toC`) and its pending messages `P` (sent, not yet handed out
in a `Ready`). -/
def simNode (tn : TraceNames) (i : w64) (c : ServerC) (P : List Etcdraft.Msg) : IProp GF :=
  ghostMapElem tn.st i (DFrac.own 1) (c, P)

/-- The token of a handed-out message `m`, `k` its key (a multiset: equal messages occur). -/
def inFlight (tn : TraceNames) (k : Nat) (m : Etcdraft.Msg) : IProp GF :=
  ghostMapElem tn.bag k (DFrac.own 1) m

/-- The simulation's invariant, the voters `C` (Draft: the relation of the shares to raft's state is
the nodes' own, at their hook points; the determinism facts `MsgsDet`, `AppSlices` of the design
are added with S5's proofs). -/
def simInv (C : List w64) (tn : TraceNames) : IProp GF :=
  iprop(∃ (L : List TraceEv) (σ : Etcdraft.State) (A : GMap w64 (ServerC × List Etcdraft.Msg))
      (B : GMap Nat Etcdraft.Msg) (phP phM : List Etcdraft.Msg),
    traceFrag tn.tr L ∗ ghostMapAuth tn.st 1 A ∗ ghostMapAuth tn.bag 1 B ∗
    ⌜SimRun C L σ ∧ σ.server = confAbs C ∧
      (∀ i ∈ C, ∃ P, A !! i = some (toC σ.server (σ.s (idAbs i)), P)) ∧
      (∀ i, i ∉ C → A !! i = none) ∧
      σ.pendingMessages.eq (bagOf ((C.flatMap (fun i => ((A !! i).map Prod.snd).getD [])) ++ phP)) ∧
      σ.messages.eq (bagOf ((GMap.toList B).map Prod.snd ++ phM))⌝)

/-- The exported law (layer D's): a trace the simulation ran through every line is accepted (the
corollary's `TraceAccepts`), once the whole trace's own initial state and servers are the voters'
(`newTrace` reads them from the bootstrap lines: layer B's bootstrap clause gives it once every
voter's are logged). -/
theorem simRun_accepts (C : List w64) (L : List TraceEv) (σ : Etcdraft.State) (t : Etcdraft.Trace) :
    SimRun C L σ → Etcdraft.newTraceWith (L.map evConv) false false = .ok t →
    t.init = simInit C → t.server = confAbs C →
    Etcdraft.TraceAccepts (L.map evConv) false false := by
  intro hrun hnt hinit hsrv
  rcases hrun with ⟨hL, -⟩ | ⟨t', ht', hr⟩
  · subst hL; exact absurd hnt (Etcdraft.newTraceWith_nil false false t)
  · rw [hnt] at ht'
    cases ht'
    have heq : ({ t with init := simInit C, server := confAbs C } : Etcdraft.Trace) = t := by
      rw [← hinit, ← hsrv]
    rw [heq] at hr
    have hlen : t.len = L.length := by
      simpa using Etcdraft.newTraceWith_len _ false false t hnt
    rw [← hlen] at hr
    obtain ⟨res, hres, hok⟩ := hr.accepts
    exact ⟨t, hnt, res, hres, hok⟩

end ghost

end TraceSim

end EtcdGrove
end Perennial
