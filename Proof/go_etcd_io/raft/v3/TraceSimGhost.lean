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
- `simInv C tn Fx`: the trace's simulation half, the specification's state, the shares' and tokens'
  authorities, and the phantom replies (requests of a lower term the specification answers and
  raft, check-quorum and pre-vote off, ignores).
-/
module

public import Proof.go_etcd_io.raft.v3.TraceSim
public import Proof.go_etcd_io.raft.v3.TraceSimBag
public import Proof.strconv.FormatUintDefs

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
message tokens; and the cluster's voters (the bootstrap configuration, constant: P3). -/
structure TraceNames where
  tr : GName
  st : GName
  bag : GName
  voters : List w64
  /-- the nodes' `booted` flags (review round 2's A7) -/
  bt : GName

instance traceNames_countable : Pos.Countable TraceNames :=
  countableOfLeftInverse (fun n : TraceNames => (n.tr, n.st, n.bag, n.voters, n.bt))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2⟩) (fun _ => rfl)

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

/-- The events' lines, as `newTraceWith` parses them. -/
def parseLines (evs : List Etcdraft.Event) : Except Etcdraft.TraceError (List Etcdraft.Line) :=
  ((List.range evs.length).zip evs).mapM (fun p => Etcdraft.parseLine p.1 p.2)

/-- Which lines are bootstrap lines of one of the servers `srv` (as `newTraceWith` computes them). -/
def bootFlags (srv : Etcdraft.SetIds) (lines : List Etcdraft.Line) : List Bool :=
  (List.range lines.length).map (fun k =>
    (srv.map (fun i => (Etcdraft.bootstrapOf lines i).1)).any (fun f => f.getD k false))

/-- The trace specification of the lines so far, read with the voters' servers and initial state
(`newTraceWith` of a prefix may fail where the whole trace does not: before every voter's bootstrap
lines are in, the first node's configuration names servers not yet seen). -/
def linesTrace (C : List w64) (lines : List Etcdraft.Line) : Etcdraft.Trace :=
  { lines := lines, server := confAbs C, initSrv := confAbs C,
    bootstrap := bootFlags (confAbs C) lines, init := simInit C }

/-- The trace so far runs, from `simInit C`, to `σ` (TLC's verdict on it so far: one state per
line, no branching, the invariants), read by `linesTrace` (`simRun_accepts` relates it to the whole
trace's `newTraceWith` once every voter's bootstrap lines are in). -/
def SimRun (C : List w64) (L : List TraceEv) (σ : Etcdraft.State) : Prop :=
  (L = [] ∧ σ = simInit C) ∨
  ∃ lines ts, parseLines (L.map evConv) = .ok lines ∧
    Etcdraft.Trace.RunRel (linesTrace C lines) L.length ts ∧ ts.s = σ ∧ ts.l = L.length + 1

/-- Draft (to be proved, with `newTraceWith_len`): `newTraceWith` reads the events' lines, and its
bootstrap flags are `bootFlags` of its servers. -/
theorem newTraceWith_lines (evs : List Etcdraft.Event) (t : Etcdraft.Trace) :
    Etcdraft.newTraceWith evs false false = .ok t →
    parseLines evs = .ok t.lines ∧ t.bootstrap = bootFlags t.server t.lines := by
  sorry

/-- A bag of the messages of a list. -/
def bagOf (l : List Etcdraft.Msg) : Etcdraft.Bag := l.foldl Etcdraft.Bag.with []

/-! ## The shares and the invariant -/

/-- Node `i`'s share: its server `c` (`toC`) and its pending messages `P` (sent, not yet handed out
in a `Ready`). -/
def simNode (tn : TraceNames) (i : w64) (c : ServerC) (P : List Etcdraft.Msg) : IProp GF :=
  ghostMapElem tn.st i (DFrac.own 1) (c, P)

/-- **Node `i` has logged a non-bootstrap line in `L`** (its bootstrap segment is over). -/
def booted (L : List TraceEv) (i : Etcdraft.ID) : Prop :=
  ∃ x ∈ L, ∃ ln, Etcdraft.parseLine 0 (evConv x) = .ok ln ∧ ln.nid = i ∧ Etcdraft.isBootstrapName ln.ev.name = false

/-- **Node `i`'s last event in `L`** (`none`: none yet), by its id's string. -/
def LastOf (L : List TraceEv) (n : GoString) (o : Option TraceEv) : Prop :=
  match o with
  | none => ∀ x ∈ L, x.nid ≠ n
  | some e0 => ∃ L1 L2, L = L1 ++ e0 :: L2 ∧ e0.nid = n ∧ ∀ x ∈ L2, x.nid ≠ n

/-- Node `i`'s `booted` flag (its bootstrap segment over: `booted`) and its last event. -/
def simBoot (tn : TraceNames) (i : w64) (b : Bool) (o : Option TraceEv) : IProp GF :=
  ghostMapElem tn.bt i (DFrac.own 1) (b, o)

/-- The token of a handed-out message `m`, `k` its key (a multiset: equal messages occur). -/
def inFlight (tn : TraceNames) (k : Nat) (m : Etcdraft.Msg) : IProp GF :=
  ghostMapElem tn.bag k (DFrac.own 1) m

/-- The simulation's invariant, the voters `C`, with the facts `Fx σ` the specification's state
carries (Draft: `TracedHooksDraft`'s `simFx`: the per-server raft facts and the specification
invariants; the relation of the shares to raft's state is the nodes' own, at their hook points). -/
def simInv (C : List w64) (tn : TraceNames) (Fx : Etcdraft.State → IProp GF) : IProp GF :=
  iprop(∃ (L : List TraceEv) (σ : Etcdraft.State) (A : GMap w64 (ServerC × List Etcdraft.Msg))
      (B : GMap Nat Etcdraft.Msg) (phP phM : List Etcdraft.Msg) (Bt : GMap w64 (Bool × Option TraceEv)),
    traceFrag tn.tr L ∗ ghostMapAuth tn.st 1 A ∗ ghostMapAuth tn.bag 1 B ∗ ghostMapAuth tn.bt 1 Bt ∗ Fx σ ∗
    ⌜SimRun C L σ ∧ σ.server = confAbs C ∧
      (∀ i ∈ C, ∃ P, A !! i = some (toC σ.server (σ.s (idAbs i)), P)) ∧
      (∀ i, i ∉ C → A !! i = none) ∧
      BagRep σ.pendingMessages ((C.flatMap (fun i => ((A !! i).map Prod.snd).getD [])) ++ phP) ∧
      BagRep σ.messages ((GMap.toList B).map Prod.snd ++ phM) ∧ σ.preVote = false ∧ σ.checkQuorum = false ∧
      (∀ i ∈ C, ∀ x ∈ ((A !! i).map Prod.snd).getD [], x.source = idAbs i) ∧
      (∀ i ∈ C, ∃ b o, Bt !! i = some (b, o) ∧ (b = true ↔ booted L (idAbs i)) ∧ LastOf L (decStr i) o ∧
        (b = true → o.isSome)) ∧
      -- `ConvertEvents`'s premise: the events are ASCII
      (∀ x ∈ L, TraceEv.Ascii x)⌝)

instance simInv_timeless (C : List w64) (tn : TraceNames) (Fx : Etcdraft.State → IProp GF)
    [hFx : ∀ σ, Timeless (Fx σ)] : Timeless (simInv C tn Fx) := by
  unfold simInv traceFrag; infer_instance

/-- The exported law (layer D's): a trace the simulation ran through every line is accepted (the
corollary's `TraceAccepts`), once the whole trace's own initial state and servers are the voters'
(`newTrace` reads them from the bootstrap lines: layer B's bootstrap clause gives it once every
voter's are logged). -/
theorem simRun_accepts (C : List w64) (L : List TraceEv) (σ : Etcdraft.State) (t : Etcdraft.Trace) :
    SimRun C L σ → Etcdraft.newTraceWith (L.map evConv) false false = .ok t →
    t.init = simInit C → t.server = confAbs C → t.initSrv = confAbs C →
    Etcdraft.TraceAccepts (L.map evConv) false false := by
  intro hrun hnt hinit hsrv hisrv
  rcases hrun with ⟨hL, -⟩ | ⟨lines, ts, hl, hr, -, -⟩
  · subst hL; exact absurd hnt (Etcdraft.newTraceWith_nil false false t)
  · obtain ⟨hpl, hb⟩ := newTraceWith_lines _ t hnt
    rw [hl] at hpl
    cases hpl
    have heq : linesTrace C t.lines = t := by
      unfold linesTrace
      rcases t with ⟨tl, ts, ti, tb, tin⟩
      simp only at hinit hsrv hisrv hb ⊢
      subst hinit hsrv hisrv hb
      rfl
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
