/-
Lean-first (no Rocq counterpart).

# The refinement to Antithesis's binding: parity B2's statements (#33, durability)

Restarts, batching and `-parallel` (`mskB2`); split writes and `AsyncStorageWrites` with them (`mskB25`, B2.5). Statements only
(round 1): the relation the B2 reports keep (`AntSimD`) and one `abbrev …_in.stmt` per report kind
or reportless step, each over the runs and inputs a mask `msk ≤ mskB2` admits.

**Why a new relation.** Several conjuncts of the B1 relation (`AntSim`) are false once writes are
announced in memory first or undone by a restart (the counterexamples are in the B2 inventory,
`notes/antithesis-parity-b2.md` once landed): raft's outbox fills between a batching node's inputs;
with async writes an applied entry can be past the disk's commit, a leader's `confirmed` lags its
log, a candidate's vote request is recorded only by its write, and an immediate heartbeat response
carries a term its sender has not written; a restart lowers a node's `currentTerm`, so the binding
keeps facts while some node's `EffTerm` (not its `currentTerm`) is at most their term. `AntSimD` is
`AntSim` with those conjuncts guarded by the run's modes or restated over `EffTerm` and the undo
record, plus the B2 bookkeeping (`UndoFacts`, `DiskFold`, `JobsOk`, `UndoBindOk`). With the B2
modes off it is `AntSim` with `EffTerm` forms that the B1 steps keep (round 2: `AntSimD ↔ AntSim ∧ …`
at `mskB1`, so B1's `_in` theorems carry over).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.Scope

@[expose] public section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace AntSim

open GMap go_etcd_io.raft.v3

/-- **Parity B2's scope**: `mskB1` with batching, `-parallel` and restarts, storage synchronous (the
driver's `DrawMode`: parallel only without batching). Split writes and async storage writes are
B2.5's (`mskB25`). -/
def mskB2 : SimMask :=
  { md := { prevote := true, cq := true, reads := true, transfer := true, nonVoters := true },
    k := { prevote := true, cq := true, sdr := true }, campaign := true, unreachable := true,
    batch := true, parallel := true, split := false, restarts := true }

/-- **Parity B2.5's scope**: `mskB2` with split writes (`splitTermEntriesCommit`, without batching)
and async storage writes (`AsyncStorageWrites`; drawn independently of batching). -/
def mskB25 : SimMask :=
  { mskB2 with md := { mskB2.md with async := true }, split := true }

section b2
variable [GooseExts]

/-! ## The view's bases -/

/-- The view whose disk is raft's own state: the hard state and log an async `Ready` is compared
with (the last `Ready`'s, which raft's `prevHardSt` and the harness's `rhs` hold). -/
def NodeView.memV (v : NodeView) : NodeView := { v with dur := durOf v.r }

/-- The `Ready` has something to write (`write` in `drain`, `drainAsync`, `parallel`): its hard state
differs from the view's disk's, or it has entries or a snapshot. -/
def Writes (v : NodeView) (rd : ReadyD) : Prop :=
  rd.term ≠ v.dur.term ∨ rd.vote ≠ v.dur.vote ∨ rd.commit ≠ v.dur.commit ∨ rd.ents ≠ [] ∨
    rd.snap ≠ none

/-- A request to append or a heartbeat (`isRequest`: what `-parallel` sends before the write). -/
def isReqM (q : Msg) : Bool := decide (q.ty = .app ∨ q.ty = .heartbeat)

/-- A request for votes: held until its `Ready`'s write (design §6.1, the driver's rule). -/
def heldVote (q : Msg) : Bool := decide (q.ty = .vote)

/-- Async: the storage write an async `Ready` queues (`drainAsync`'s `job`): its `mem` if it writes,
the messages that wait for it (the `AfterAppTy` ones to others and the held vote requests), the
drain's cause and `by`, raft's state after it. -/
def ReadyD.job (rd : ReadyD) (v : NodeView) (r : RState) (w : Bool) : WJob :=
  { wrec := if w then some (rd.memRec v) else none, resp := rd.resp ++ rd.msgs.filter heldVote,
    cause := v.cause, byE := v.byE, st := accepted r }

/-- Async: the view after a `Ready` (reported by `mem` or not): the drain phase, its immediate
messages pending (all but the held vote requests; no self-message for `Advance`, which raft steps
with the write's responses), its write queued (`hasJob`: raft asked for one), its committed entries
queued for the apply goroutine. -/
def NodeView.afterMemA (v : NodeView) (r : RState) (rd : ReadyD) (w hasJob : Bool) : NodeView :=
  { (v.drainOf r rd) with pend := rd.msgs.filter (fun q => !heldVote q), qs := [], ce := [],
                          mems := if w then v.mems ++ [rd.memRec v] else v.mems,
                          jobs := if hasJob then v.jobs ++ [rd.job v r w] else v.jobs,
                          ajobs := if rd.ce.isEmpty then v.ajobs else v.ajobs ++ [{ ents := rd.ce, byE := v.byE }] }

/-- The head job marked run. -/
def markHead : List WJob → List WJob
  | [] => []
  | j :: js => { j with ran := true } :: js

/-- Batch: a batching node's `mem` record (`note`): raft's role and hard state after the input and
the entries it appended (`bat`: the report carries them only for a leader, and no `first`). -/
def memRecB (v : NodeView) (r : RState) (pre : Bool) (es : List EntryM) : MemRec :=
  { role := r.p.role, pre := pre, term := r.p.term, vote := r.p.vote, commit := r.p.commit,
    ents := es, snap := none, cause := v.cause, byE := v.byE, bat := true, xcause := v.xcause }

/-- Batch: the input was a request to append at raft's term (`note`'s `request`: its write records an
acknowledgement even when nothing changes). -/
def ReqCause (v : NodeView) (r : RState) : Prop :=
  ∃ m, v.cause = some m ∧ m.ty = .app ∧ m.term = r.p.term

/-- Split writes (`parts`, `splitTermEntriesCommit`): the term and vote with the disk's commit, then
the entries, then the commit, each when it changes; as `MemRec`s (`base` the `Ready`'s). -/
def splitParts (d : DurW) (rd : ReadyD) (base : MemRec) : List MemRec :=
  (if decide (rd.term ≠ d.term ∨ rd.vote ≠ d.vote) then
    [{ base with term := rd.term, vote := rd.vote, commit := d.commit, ents := [] }] else []) ++
  (if rd.ents.isEmpty then [] else
    [{ base with term := rd.term, vote := rd.vote, commit := d.commit, ents := rd.ents }]) ++
  (if decide (rd.commit ≠ d.commit) then
    [{ base with term := rd.term, vote := rd.vote, commit := rd.commit, ents := [] }] else [])

/-! ## The relation (C1-C4 with the B2 modes) -/

/-- **A candidate's log is of earlier terms**: every entry of a candidate's log is of a term below
its own (its campaign raised the term above the log's, and only a non-candidate adds entries). What a
win's `LeaderConfOkD` reads: the disk holds no entry of the new leader's term before its win's write
(#33 parity B2, Sim round 14, lead-approved). -/
def CandLt (s : PState) : Prop :=
  s.role = .candidate → ∀ e ∈ s.log, uint.Z e.Term' < uint.Z s.term

/-- **The log's terms at most the term** (raft's ghost `TermsLe`, which the harness reads of raft's
state at a `Ready` with `rawNode_logTerms`): what a campaign's `CandLt` reads (`candLt_reachP`) (#33
parity B2, Sim round 15, lead-approved). -/
def LogTermsLe (s : PState) : Prop :=
  ∀ e ∈ s.log, uint.Z e.Term' ≤ uint.Z s.term

/-- **A leader's own `Match` within its log**, and so are its queued self-acknowledgements' indices:
`reset` sets the leader's own `Match` to its last index, only its own acknowledgements raise it, each
of an index it appended (`appendEntry`'s `pselfAck`, at the last index then), and a leader's log only
grows (#33 parity B2, Sim round 16, lead-approved). What a proposal's `LeaderPartD` reads: the indices
up to the leader's own `Match` are of its log before the proposal. -/
def SelfMatchLe (id : w64) (s : PState) (qs : List Msg) : Prop :=
  s.role = .leader → uint.Z (matchOf s id) ≤ plogLastIndexZ s.base s.log ∧
    ∀ q ∈ qs, q.ty = .appResp → uint.Z q.index ≤ plogLastIndexZ s.base s.log

/-- **C1, raft's side, B2** (`NodeFacts` with two conjuncts guarded): raft's outbox is empty between
`Ready`s only when not batching (a batching node takes several inputs before its `Ready`); what was
handed out is within the disk's commit only in sync mode (async: the apply goroutine may hand out
entries whose commit is not yet written; they are within the binding's `chain`, `ApplyChainOk`),
and sync, within the commit of the disk with the announced writes made (a `-parallel` leader's `mem`
announces a commit its write makes later; #33 B2 round 11). The other conjuncts are `NodeFacts`', and
a candidate's log of earlier terms (`CandLt`, Sim round 14), the log's terms at most the term
(`LogTermsLe`, Sim round 15) and a leader's own `Match` and queued self-acknowledgements within its log
(`SelfMatchLe`, Sim round 16). -/
def NodeFactsD (R : RunCfg) (n : Fin R.N) (v : NodeView) : Prop :=
  (R.drv.batch = false → v.ps.outbox = []) ∧
  (R.md.snapshots = false → v.ps.base = base0 ∧ v.r.fp = [] ∧ v.r.snap = false) ∧
  (R.md.confChanges = false →
    v.r.cfg.cfg = CfgM.simple R.voters0 ∅ ∧ EntsNormal v.r.full ∧ EntsNormal v.dur.log) ∧
  LogIdx v.dur.log ∧
  v.delivered ++ v.ce <+: v.dur.log ∧
  (R.md.async = false →
    (v.delivered ++ v.ce).length ≤ uint.nat ((v.mems ++ v.parts).foldl DurW.write v.dur).commit) ∧
  (∀ q ∈ v.pend, MsgMask R q) ∧ uint.Z v.dur.term ≤ uint.Z v.ps.term ∧
  (v.pre = true → v.ps.role = .follower) ∧
  (R.md.reads = false → v.ps.rd.pend = [] ∧ (v.ps.role = .leader → v.ps.rd.ro.pending = [])) ∧
  (v.pre = true → (R.k n).prevote = true) ∧
  (∀ p ∈ v.ps.rd.pend, (p.1.From' = W64 0 ∨ ∃ j : Fin R.N, p.1.From' = nodeId j) ∧
    (R.md.confChanges = false → EntsNormal p.2)) ∧
  (v.ps.role = .leader → ∀ q ∈ v.ps.rd.ro.pending, (q.src = W64 0 ∨ ∃ j : Fin R.N, q.src = nodeId j) ∧
    (R.md.confChanges = false → EntsNormal q.ents)) ∧
  ReadOk v.ps ∧ v.ps.rd.states = [] ∧ CandLt v.ps ∧ LogTermsLe v.ps ∧
  SelfMatchLe (nodeId n) v.ps v.qs

/-- **A leader's confirmation, B2**: once the disk holds raft's whole log (sync) or an entry of the
leader's term (its win's write is announced), its `confirmed` is at its term and covers the disk's
log (`LeaderConfOk` reads raft's whole log, which async, batched and `-parallel` writes announce
before the binding's `OnDisk` confirms them). -/
def LeaderConfOkD (S : AntCheck.State) {N : Nat} (n : Fin N) (v : NodeView) : Prop :=
  (v.dur.log = v.r.full ∨ ∃ e ∈ v.dur.log, e.Term' = v.ps.term) →
    (S.confirmed[n.val]!).term = uint.Z v.ps.term ∧ (v.dur.log.length : Int) ≤ (S.confirmed[n.val]!).index

/-- An ack fact of `j` is not one its unmade write added (`OnDisk`'s `pre.msgs`, which a restart
removes, B 162-194): what `Garbage`'s domination test reads (B 696-706). -/
def AckOut (S : AntCheck.State) {N : Nat} (j : Fin N) (a : AntCheck.Fact) : Prop :=
  ∀ u : AntCheck.Pre, S.undo[j.val]! = some u → u.made = false → a ∉ u.msgs

/-- `AckIn` with a witness outside `j`'s unmade write (an acknowledgement `j` has sent: its `send`
ended the write's undo record, B 1026, and later writes record only new facts). -/
def AckInD (S : AntCheck.State) {N : Nat} (j : Fin N) (dst : AntCheck.Str) (t k : Int) : Prop :=
  ∃ a ∈ S.msgs, a.type = go!"ack" ∧ a.src = nameOf (nodeId j) ∧ a.dst = dst ∧ a.term = t ∧
    k ≤ a.index ∧ AckOut S j a

/-- A leader's `AckIn` for `j`'s acknowledgement: `AckInD` for another node (its `Match` comes from
a response `j` sent), `AckIn` for itself. -/
def AckInX (S : AntCheck.State) {N : Nat} (n j : Fin N) (t k : Int) : Prop :=
  ∃ a ∈ S.msgs, a.type = go!"ack" ∧ a.src = nameOf (nodeId j) ∧ a.dst = nameOf (nodeId n) ∧
    a.term = t ∧ k ≤ a.index ∧ (j ≠ n → AckOut S j a)

/-- **C2, a leader's part, B2** (`LeaderPart` with `LeaderConfOkD`; the acknowledgements of the other
nodes outside their unmade writes, `AckInX`). -/
def LeaderPartD (S : AntCheck.State) {N : Nat} (n : Fin N) (v : NodeView) : Prop :=
  v.ps.role = .leader →
    S.leaders.contains { server := nameOf (nodeId n), term := uint.Z v.ps.term } ∧
    S.ledLog.get (uint.Z v.ps.term) = .ok (logOf v.r.full) ∧
    (∀ (j : Fin N) (k : w64), uint.Z k ≤ uint.Z (matchOf v.ps (nodeId j)) →
      plogTermAt v.ps.base v.ps.log k = some v.ps.term →
      AckInX S n j (uint.Z v.ps.term) (uint.Z k)) ∧
    (∀ j : Fin N, j ≠ n → matchOf v.ps (nodeId j) = W64 0 ∨
      AckInX S n j (uint.Z v.ps.term) (uint.Z (matchOf v.ps (nodeId j)))) ∧
    LeaderConfOkD S n v

/-- **C2, a candidate's part, B2**: its grants are in `Granted(n)`; its vote request's fact is in
`msgs` once its campaign's write is announced (`OnDisk`'s `elect`; async, the candidate's `mem`
comes first). -/
def CandPartD (S : AntCheck.State) {N : Nat} (n : Fin N) (v : NodeView) : Prop :=
  v.ps.role = .candidate →
    (∀ j : Fin N, v.ps.votes !! nodeId j = some true → (S.granted n.val).has (nameOf (nodeId j))) ∧
    (v.dur.term = v.ps.term → S.voteRequest n.val (S.currentTerm[n.val]!) ∈ S.msgs)

/-- **A batch's pending message** (`send` with `b`, B 526-593): to a server; a granted vote's record,
a vote request's fact and an acknowledgement's fact are in `S` or in the batch's undo record (what
the binding's `mine`, `cast` and `Acks` read); the others as `PendOk`. -/
def PendOkB (S : AntCheck.State) {N : Nat} (n : Fin N) (v : NodeView) (q : Msg) : Prop :=
  q.dst ≠ nodeId n ∧ (∃ j : Fin N, q.dst = nodeId j) ∧
  (q.ty = .appResp → q.src = nodeId n ∧ (q.reject = false → q.index ≠ W64 0 →
    ∃ u, S.undo[n.val]! = some u ∧
      AntCheck.ackFact (nameOf (nodeId n)) (nameOf q.dst) (uint.Z q.term) (uint.Z q.index) ∈ u.acks)) ∧
  (q.ty = .voteResp → q.src = nodeId n ∧ (q.reject = false →
    let r : AntCheck.VoteRec := { voter := nameOf (nodeId n), term := uint.Z q.term, cand := nameOf q.dst }
    r ∈ S.votes ∨ ∃ u, S.undo[n.val]! = some u ∧ r ∈ u.votes)) ∧
  (q.ty = .vote → q.src = nodeId n ∧ ∃ f, AntCheck.voteFact (msgOf q q.dst) = .ok f ∧
    (f ∈ S.msgs ∨ ∃ u, S.undo[n.val]! = some u ∧ f ∈ u.msgs)) ∧
  (q.ty ≠ .appResp → q.ty ≠ .voteResp → q.ty ≠ .vote → PendOk N (nodeId n) v q)

/-- **The disk before an unmade write** (what a restart may revert to): its log indexed by position,
normal without conf changes, its term within the disk's. -/
def UndoFacts (R : RunCfg) (v : NodeView) : Prop :=
  ∀ d, v.undo = some d → LogIdx d.log ∧ (R.md.confChanges = false → EntsNormal d.log) ∧
    uint.Z d.term ≤ uint.Z v.dur.term

/-- **The disk and the announced writes** (every mode): outside a split write's parts, the disk with
the queued `mem`s' writes applied in order is raft's own hard state and full log. (Sync, unbatched:
`mems = []`, `SyncDisk`'s `dur = durOf r`.) -/
def DiskFold (v : NodeView) : Prop :=
  v.parts = [] → v.mems.foldl DurW.write v.dur = durOf v.r

/-- **The async storage queues**: none without async; at most the head job run (its messages not
yet sent) and at most the head apply handed out; unbatched, the binding's queue is the jobs not run
that write, in order; every waiting message is what raft says of it at its `Ready`'s state
(`PendOk` at `st`, with the job's cause, sent to the node) and under the mask; a held vote request
waits for a write; an immediate message is neither a vote request nor `AfterAppTy`. -/
def JobsOk (R : RunCfg) (n : Fin R.N) (net : List Msg) (v : NodeView) : Prop :=
  (R.md.async = false → v.jobs = [] ∧ v.ajobs = []) ∧
  (∀ j ∈ v.jobs.drop 1, j.ran = false) ∧ (∀ a ∈ v.ajobs.drop 1, a.ran = false) ∧
  (R.md.async = true → R.drv.batch = false →
    v.mems = (v.jobs.filter (fun j => !j.ran)).filterMap (·.wrec)) ∧
  (∀ j ∈ v.jobs, (∀ m, j.cause = some m → m ∈ net ∧ m.dst = nodeId n) ∧
    ∀ q ∈ j.resp, MsgMask R q ∧ (q.ty = .vote → j.wrec.isSome) ∧
      (R.drv.batch = false →
        PendOk R.N (nodeId n) { v with r := j.st, cause := j.cause, byE := j.byE } q)) ∧
  (R.md.async = true → ∀ q ∈ v.pend, q.ty ≠ .vote ∧ ¬ AfterAppTy q.ty)

/-- **What the apply goroutine hands out** (async): what was handed out and the queued applies are a
prefix of the disk's log (raft applies only entries it knows written) within the binding's `chain`
(the `apply` check, B 600-603). -/
def ApplyChainOk (R : RunCfg) (S : AntCheck.State) (n : Fin R.N) (v : NodeView) : Prop :=
  R.md.async = true →
    let ap := v.delivered ++ (v.ajobs.filter (fun a => !a.ran)).flatMap (·.ents)
    ap <+: v.dur.log ∧ (ap.length : Int) ≤ S.chain.length ∧
      S.chain.take ap.length = logOf ap

/-- **The in-memory commit is recorded** (outside a split write's parts): raft's commit is within
`chain`, which agrees with raft's log up to it, and is recorded in `termLen` under a term at most
raft's (`InMemory` extends `chain` and `termLen` at the `mem` that announces the commit, before its
write: what `Sendable`'s `RecordedIn` reads of a `-parallel` request sent before the write). -/
def MemCommitOk (S : AntCheck.State) (v : NodeView) : Prop :=
  v.parts = [] →
    uint.Z v.ps.commit ≤ S.chain.length ∧
    S.chain.take (uint.nat v.ps.commit) = (logOf v.r.full).take (uint.nat v.ps.commit) ∧
    (v.ps.commit = W64 0 ∨ ∃ p ∈ S.termLen, p.1 ≤ uint.Z v.ps.term ∧ uint.Z v.ps.commit ≤ p.2)

/-- **A leader's self-acknowledgement waiting for its write** (`-parallel`, #33 B2 round 11): a win's
or a proposal's `Ready` queues the leader's acknowledgement of its new last index, whose ack fact
the binding records only at the write's `OnDisk` (B 407); until then it is within the log of the disk
with the announced writes made. -/
def QsAckW {N : Nat} (n : Fin N) (v : NodeView) (q : Msg) : Prop :=
  q.src = nodeId n ∧ q.dst = nodeId n ∧ q.reject = false ∧ q.ty = .appResp ∧ q.term = v.ps.term ∧
    v.ps.role = .leader ∧ v.mems ≠ [] ∧
    uint.nat q.index ≤ ((v.mems ++ v.parts).foldl DurW.write v.dur).log.length

/-- **C1, C2 and the drain's facts, B2** (`NodeOk` with `NodeFactsD`, `LeaderPartD`, `CandPartD`; a
batch's pending messages by `PendOkB` once its queued `mem`s are written: a vote, a vote request
and an acknowledgement are recorded by the write, `OnDisk`), and the B2 bookkeeping: in a sync,
unbatched run an announced write is not `made` while the binding keeps its undo record (the first
`send` after it ends it, B 1026), and the in-memory commit is recorded (`MemCommitOk`). -/
def NodeOkD (R : RunCfg) (dec : CCDec) (S : AntCheck.State) (net : List Msg) (n : Fin R.N)
    (v : NodeView) : Prop :=
  DiskIs S n v ∧ MemIs R.N S n v ∧ SyncDisk R v ∧ UndoIs S n v ∧ QueueIs S n v ∧ ReadsIs S n v ∧
  ConfLag dec R v ∧ NodeFactsD R n v ∧ LeaderPartD S n v ∧ CandPartD S n v ∧
  (R.drv.batch = false → ∀ q ∈ v.pend, PendOk R.N (nodeId n) v q) ∧
  (R.drv.batch = true → v.mems = [] → ∀ q ∈ v.pend, PendOkB S n v q) ∧
  (∀ x ∈ v.xpend, XPendOk R.N (nodeId n) v.ps x) ∧
  (∀ q ∈ v.qs, QsOk R S n v q ∨ QsAckW n v q) ∧
  (v.told = true → (∃ m, v.cause = some m ∧ S.pending[n.val]! = [msgOf m (nodeId n)]) ∨
    (∃ x, v.xcause = some x ∧ S.pending[n.val]! = [xmsgOf x])) ∧
  (∀ m, v.cause = some m → m ∈ net ∧ m.dst = nodeId n) ∧
  (∀ x, v.xcause = some x → x.dst = nodeId n ∧ v.cause = none) ∧
  LeadOk n v ∧ VoteSelf n v ∧
  UndoFacts R v ∧ DiskFold v ∧ JobsOk R n net v ∧ ApplyChainOk R S n v ∧
  (R.md.async = false → R.drv.batch = false → v.undo ≠ none → v.made = false) ∧ MemCommitOk S v

/-- **C3 with restarts**: what `GC` keeps is kept while some node's `EffTerm` (B 152: the lower of its
term and its unmade write's undo term) is at most the term, so the `currentTerm` forms of
`TermLenOk`'s and `ConfirmedOk`'s "every node passed it" hold over `EffTerm`; and the state `Boot`
reverts to (an unmade write's undo record) has the per-node C3 facts: its terms, its commit within
`chain` and agreeing with it, the acks from the node other than the write's within its term, and
those at its term within its confirmed or committed log (they were sent from it). -/
def UndoBindOk (N : Nat) (S : AntCheck.State) : Prop :=
  (∀ T, 0 < tlOld S.termLen T →
    (∃ l ∈ S.leaders, l.term = T) ∨ ∀ i : Fin N, T < S.effTerm i.val) ∧
  (∀ j : Fin N, (S.confirmed[j.val]!).index = 0 ∨ S.ledLog.has (S.confirmed[j.val]!).term = true ∨
      ∀ i : Fin N, (S.confirmed[j.val]!).term < S.effTerm i.val) ∧
  ∀ (j : Fin N) (u : AntCheck.Pre), S.undo[j.val]! = some u → u.made = false →
    S.bootTerm ≤ u.term ∧ u.voteTerm ≤ u.term ∧ u.confirmed.term ≤ u.term ∧ 0 ≤ u.commit ∧
    u.commit ≤ S.chain.length ∧
    S.chain.take u.commit.toNat = ((S.log[j.val]!).take u.keep.toNat ++ u.suffix).take u.commit.toNat ∧
    (∀ a ∈ S.msgs, a ∉ u.msgs → a.type = go!"ack" → a.src = nameOf (nodeId j) → a.term ≤ u.term) ∧
    ∀ a ∈ S.msgs, a ∉ u.msgs → a.type = go!"ack" → a.src = nameOf (nodeId j) → a.term = u.term →
      (u.confirmed.term = a.term ∧ a.index ≤ u.confirmed.index) ∨ a.index ≤ u.commit

/-- **C3, the terms' recorded commits, B2** (`TermLenOk` with its leader clause read at the leader's
announced commit, `MemCommit`, B 139): a `-parallel` leader's `cmt` records its new commit in
`termLen` at its `mem` (`InMemory`, B 252-258), before the write that makes it its `commitIndex`
(#33 B2 round 11). With no `mem` queued it is `TermLenOk` (`termLenOkM_iff`). -/
def TermLenOkM (N : Nat) (S : AntCheck.State) : Prop :=
  (∀ T, 0 < tlOld S.termLen T →
    (∃ l ∈ S.leaders, l.term = T) ∨ ∀ i : Fin N, T < S.currentTerm[i.val]!) ∧
  ∀ n : Fin N, S.role[n.val]! = AntCheck.leader → ∃ c, S.memCommit n.val = .ok c ∧
    (AntCheck.termAt (S.log[n.val]!) c = S.currentTerm[n.val]! →
      c ≤ tlOld S.termLen (S.currentTerm[n.val]!)) ∧
    tlOld S.termLen (S.currentTerm[n.val]!) ≤ c

/-- **C3 over the announced commits** (`BindingOk` with `TermLenOkM` for `TermLenOk`, the rest
unchanged). -/
def BindingOkM (R : RunCfg) (dec : CCDec) (S : AntCheck.State) : Prop :=
  S.viol = [] ∧
  (∀ p ∈ S.termLen, p.2 ≤ S.chain.length) ∧
  (∀ n : Fin R.N, S.commitIndex[n.val]! ≤ S.chain.length ∧
    S.chain.take (S.commitIndex[n.val]!).toNat = (S.log[n.val]!).take (S.commitIndex[n.val]!).toNat) ∧
  (∀ n : Fin R.N, S.commitIndex[n.val]! = 0 ∨
    ∃ p ∈ S.termLen, p.1 ≤ S.currentTerm[n.val]! ∧ S.commitIndex[n.val]! ≤ p.2) ∧
  (∀ n : Fin R.N, ∀ l, S.ledLog.get (S.confirmed[n.val]!).term = .ok l →
    (S.confirmed[n.val]!).index ≤ (S.log[n.val]!).length ∧ (S.confirmed[n.val]!).index ≤ l.length ∧
    (S.log[n.val]!).take (S.confirmed[n.val]!).index.toNat = l.take (S.confirmed[n.val]!).index.toNat) ∧
  (∀ n : Fin R.N, ∀ a ∈ S.msgs, a.type = go!"ack" → a.src = nameOf (nodeId n) →
    a.term = S.currentTerm[n.val]! →
    ((S.confirmed[n.val]!).term = a.term ∧ a.index ≤ (S.confirmed[n.val]!).index) ∨
      a.index ≤ S.commitIndex[n.val]!) ∧
  (∀ p ∈ S.ledLog, ∃ l ∈ S.leaders, l.term = p.1) ∧
  (∀ n : Fin R.N, ∀ l ∈ S.leaders, l.server = nameOf (nodeId n) →
    l.term < S.currentTerm[n.val]! ∨
      (l.term = S.currentTerm[n.val]! ∧ S.role[n.val]! ≠ AntCheck.candidate)) ∧
  (∀ f ∈ S.msgs, f.type ≠ go!"vote" →
    (∃ i : Fin R.N, f.src = nameOf (nodeId i)) ∧ ∃ j : Fin R.N, f.dst = nameOf (nodeId j)) ∧
  (∀ v ∈ S.votes, ∃ i : Fin R.N, v.voter = nameOf (nodeId i)) ∧
  (∀ n : Fin R.N, S.vote n.val ≠ [] →
    { voter := nameOf (nodeId n), term := S.currentTerm[n.val]!, cand := S.vote n.val } ∈ S.votes) ∧
  AckTermsOk R.N S ∧ VoteTermOk R.N S ∧ ConfirmedOk R.N S ∧ TermLenOkM R.N S ∧ LedConfOk R dec S ∧
  TlSorted S ∧ BootTermOk R.N S

/-- **C3, B2**: `BindingOkM` and the restart facts. -/
def BindingOkD (R : RunCfg) (dec : CCDec) (S : AntCheck.State) : Prop :=
  BindingOkM R dec S ∧ UndoBindOk R.N S

/-- **C4, a heartbeat's commit, B2**: as `HbCommitOk` for the receiver's current state, and for the
state a restart may revert it to (its unmade write's undo record), when that is at most the
heartbeat's term. -/
def HbCommitOkD (N : Nat) (S : AntCheck.State) (net : List Msg) : Prop :=
  ∀ m ∈ net, m.ty = .heartbeat → ∀ j : Fin N, m.dst = nodeId j →
    (S.currentTerm[j.val]! ≤ uint.Z m.term →
      ((S.confirmed[j.val]!).term = uint.Z m.term ∧ uint.Z m.commit ≤ (S.confirmed[j.val]!).index) ∨
        uint.Z m.commit ≤ S.commitIndex[j.val]!) ∧
    (∀ u : AntCheck.Pre, S.undo[j.val]! = some u → u.made = false → u.term ≤ uint.Z m.term →
      (u.confirmed.term = uint.Z m.term ∧ uint.Z m.commit ≤ u.confirmed.index) ∨
        uint.Z m.commit ≤ u.commit)

/-- **C4, a leader's message's commit, B2** (`LeadCommitMsgOk` over the in-memory commit,
`MemCommit`, B 139): a `-parallel` leader sends its requests before their `Ready`'s write, so an
append or heartbeat carries a commit its sender has announced (its last queued `mem`'s) but maybe not
written. -/
def LeadCommitMsgOkD (N : Nat) (S : AntCheck.State) (net : List Msg) : Prop :=
  ∀ m ∈ net, (m.ty = .app ∨ m.ty = .heartbeat) → ∀ i : Fin N, m.src = nodeId i →
    S.role[i.val]! ≠ AntCheck.follower → S.currentTerm[i.val]! = uint.Z m.term →
    ∃ c, S.memCommit i.val = .ok c ∧ uint.Z m.commit ≤ c

/-- **C4, B2** (`NetOk` restated): every message sent is between two nodes, of a type in scope; its
term is one some node has written (`EffTerm`: kept by restarts; what `OnDisk`'s `adopt` asks), and
in sync mode within its sender's (async sends a heartbeat response or a read answer at raft's
in-memory term, before its write); what the binding checks at its receipt is in `S` while its
receiver's `EffTerm` has not passed its term (`GC`'s `Garbage` reads `EffTerm`, B 696-706: a restart
can bring a passed term back), an acknowledgement's outside its sender's unmade write (`AckInD`);
then `HbCommitOkD` and the rest of `NetOk`. -/
def NetOkD (R : RunCfg) (S : AntCheck.State) (net : List Msg) : Prop :=
  (∀ m ∈ net,
    (m.ty = .vote ∨ m.ty = .voteResp ∨ m.ty = .app ∨ m.ty = .appResp ∨ m.ty = .heartbeat ∨
      m.ty = .heartbeatResp ∨ m.ty = .propose ∨ m.ty = .preVote ∨ m.ty = .preVoteResp ∨
      m.ty = .readIndex ∨ m.ty = .readIndexResp ∨ m.ty = .snap) ∧
    (∃ i : Fin R.N, m.src = nodeId i ∧
      (PreTermKeep m ∨ ∃ k : Fin R.N, uint.Z m.term ≤ S.effTerm k.val) ∧
      (R.md.async = false → PreTermKeep m ∨ uint.Z m.term ≤ S.currentTerm[i.val]!)) ∧
    ∃ j : Fin R.N, m.dst = nodeId j ∧
      (S.effTerm j.val ≤ uint.Z m.term →
        ((m.ty = .app ∨ m.ty = .heartbeat) →
          (AntCheck.toAppendFact (msgOf m m.dst) >>= S.sendable) = .ok true) ∧
        (m.ty = .vote → ∃ f, AntCheck.voteFact (msgOf m m.dst) = .ok f ∧ f ∈ S.msgs) ∧
        ((m.ty = .voteResp ∧ m.reject = false) →
          ({ type := go!"grant", src := nameOf m.src, dst := nameOf m.dst, term := uint.Z m.term } :
            AntCheck.Fact) ∈ S.msgs) ∧
        ((m.ty = .appResp ∧ m.reject = false ∧ m.index ≠ W64 0) → ∀ i : Fin R.N, m.src = nodeId i →
          AckInD S i (nameOf m.dst) (uint.Z m.term) (uint.Z m.index)))) ∧
  HbCommitOkD R.N S net ∧ NetShape net ∧ LeadCommitMsgOkD R.N S net ∧ (∀ m ∈ net, MsgMask R m) ∧
  (∀ m ∈ net, PreVoterOk R m) ∧ ∀ m ∈ net, m.ty = .readIndexResp → MsgNums (2 ^ 61) m

/-- **C4, the transfer messages, B2**: of a term some node has written (`EffTerm`). -/
def XNetOkD (R : RunCfg) (S : AntCheck.State) (xnet : List XMsg) : Prop :=
  ∀ x ∈ xnet, ∃ i : Fin R.N, uint.Z x.term ≤ S.effTerm i.val

set_option linter.iris.dupNamespace false in
/-- **The refinement relation, B2.** -/
def AntSimD (R : RunCfg) (dec : CCDec) (S : AntCheck.State) (V : Fin R.N → NodeView)
    (net : List Msg) (xnet : List XMsg) : Prop :=
  Shape R S ∧ BindingOkD R dec S ∧ NetOkD R S net ∧ XNetOkD R S xnet ∧ ∀ n, NodeOkD R dec S net n (V n)

/-- `SimPre` over `AntSimD`. -/
def SimPreD (R : RunCfg) (dec : CCDec) (S : AntCheck.State) (V : Fin R.N → NodeView) (net : List Msg)
    (xnet : List XMsg) (evs : List AntCheck.Event) (G : RaftFacts) : Prop :=
  Prefix R.cfg evs S ∧ AntSimD R dec S V net xnet ∧ RaftLaws G ∧ GlobalOk R S net G

/-- `SimStep` over `AntSimD`. -/
def SimStepD (R : RunCfg) (dec : CCDec) (evs : List AntCheck.Event) (G : RaftFacts)
    (ev : AntCheck.Event) (V' : Fin R.N → NodeView) (net' : List Msg) (xnet' : List XMsg) : Prop :=
  ∃ S', Prefix R.cfg (evs ++ [ev]) S' ∧ AntSimD R dec S' V' net' xnet' ∧ GlobalOk R S' net' G

/-! ## Restarts -/

/-- **A kill** (reportless, `inKill`/`fuse`): the node stops; nothing else moves (the binding keeps its
queue, pending message and undo record until `boot`). -/
abbrev antSim_kill_in.stmt : Prop :=
  ∀ (msk : SimMask), msk ≤ mskB2 →
  ∀ (R : RunCfg) (dec : CCDec) (S : AntCheck.State) (V : Fin R.N → NodeView) (net : List Msg)
    (xnet : List XMsg) (G : RaftFacts) (n : Fin R.N),
    InMask msk R net xnet → R.drv.restarts = true →
    AntSimD R dec S V net xnet → RaftLaws G → GlobalOk R S net G →
    AntSimD R dec S (setV V n { V n with alive := false }) net xnet

/-- **`boot` after a restart** (B 162-194): a stopped node restarts from its disk, or from the disk
before an unmade write (the binding's `Recovered` against `undo[n]`); raft's restart state
(`RestartR`, with no read state), its disk's log certified, its applied prefix committed. -/
abbrev antSim_bootR_in.stmt : Prop :=
  ∀ (msk : SimMask), msk ≤ mskB2 →
  ∀ (R : RunCfg) (dec : CCDec) (S : AntCheck.State) (V : Fin R.N → NodeView) (net : List Msg)
    (xnet : List XMsg) (evs : List AntCheck.Event) (G : RaftFacts) (n : Fin R.N) (d : DurW)
    (a : Nat) (cs : CCState) (r0 : RState),
    InMask msk R net xnet → SimPreD R dec S V net xnet evs G → R.drv.restarts = true →
    (V n).alive = false →
    (d = (V n).dur ∨ ((V n).undo = some d ∧ (V n).made = false)) → RestartR dec R d a cs r0 →
    d.log ∈ G.logs → d.log.take a <+: G.committed →
    SimStepD R dec evs G
      (evBootR (nodeId n) d.term d.vote d.commit (lastIT d.log).1 (lastIT d.log).2 a
        (confView R.N cs))
      (setV V n ((V n).boot r0 d a cs)) net xnet

/-! ## Async storage writes (`drainAsync`, the storage goroutine's `work`) -/

/-- **`mem`** (async, B 450-459): an async `Ready` that writes or changes the reported role is
reported (`w` whether it writes, against the last `Ready`'s state); its immediate messages are
pending, its write and applies queued. -/
abbrev antSim_memA_in.stmt : Prop :=
  ∀ (msk : SimMask), msk ≤ mskB25 →
  ∀ (R : RunCfg) (dec : CCDec) (S : AntCheck.State) (V : Fin R.N → NodeView) (net : List Msg)
    (xnet : List XMsg) (evs : List AntCheck.Event) (G : RaftFacts) (n : Fin R.N) (r₁ : RState)
    (rd : ReadyD) (w hasJob : Bool) (Adm : List EntryM → CCState → Prop),
    InMask msk R net xnet → SimPreD R dec S V net xnet evs G →
    R.md.async = true → R.drv.batch = false →
    ReachIn msk R dec Adm net xnet n (V n) r₁ → ReadyOutP R n (V n).memV r₁ rd →
    Reported (V n).memV rd → (w = true ↔ Writes (V n).memV rd) →
    (hasJob = true ↔ (w = true ∨ rd.resp ≠ [] ∨ rd.qs ≠ [])) →
    Told (V n) → ReadyFacts G (nodeId n) r₁ → TermRoom (V n) →
    SimStepD R dec evs G
      (evMem (nodeId n) (V n).byE (roleStr rd.pre rd.role) rd.term rd.vote rd.commit rd.ents rd.snap w)
      (setV V n ((V n).afterMemA r₁ rd w hasJob)) net xnet

/-- **An async `Ready` the harness does not report** (no write, the same role): its immediate
messages pending, its waiting messages and applies queued. -/
abbrev antSim_quietA_in.stmt : Prop :=
  ∀ (msk : SimMask), msk ≤ mskB25 →
  ∀ (R : RunCfg) (dec : CCDec) (S : AntCheck.State) (V : Fin R.N → NodeView) (net : List Msg)
    (xnet : List XMsg) (G : RaftFacts) (n : Fin R.N) (r₁ : RState) (rd : ReadyD) (hasJob : Bool)
    (Adm : List EntryM → CCState → Prop),
    InMask msk R net xnet → AntSimD R dec S V net xnet → RaftLaws G → GlobalOk R S net G →
    R.md.async = true → R.drv.batch = false →
    ReachIn msk R dec Adm net xnet n (V n) r₁ → ReadyOutP R n (V n).memV r₁ rd →
    ¬ Reported (V n).memV rd → (hasJob = true ↔ (rd.resp ≠ [] ∨ rd.qs ≠ [])) →
    ReadyFacts G (nodeId n) r₁ →
    AntSimD R dec S (setV V n ((V n).afterMemA r₁ rd false hasJob)) net xnet

/-- **`send`, async, at once** (B 510-593 with `cause`): the next immediate message of the node's
async `Ready` is reported with the drain's cause, then it is on the network. -/
abbrev antSim_sendC_in.stmt : Prop :=
  ∀ (msk : SimMask), msk ≤ mskB25 →
  ∀ (R : RunCfg) (dec : CCDec) (S : AntCheck.State) (V : Fin R.N → NodeView) (net : List Msg)
    (xnet : List XMsg) (evs : List AntCheck.Event) (G : RaftFacts) (n : Fin R.N) (q : Msg)
    (rest : List Msg),
    InMask msk R net xnet → SimPreD R dec S V net xnet evs G → R.md.async = true →
    R.drv.batch = false → (V n).pend = q :: rest → Told (V n) → MsgFacts G q →
    SimStepD R dec evs G (evSendC (nodeId n) (V n).byE q (V n).cause)
      (setV V n { V n with pend := rest }) (net ++ [q]) xnet

/-- **`write`** (async, B 462-470; and `-parallel`'s write after its requests): the oldest queued
`mem`'s write is announced (async: the head job's, not yet run); the disk is its result, the disk
before it the undo record. -/
abbrev antSim_write_in.stmt : Prop :=
  ∀ (msk : SimMask), msk ≤ mskB25 →
  ∀ (R : RunCfg) (dec : CCDec) (S : AntCheck.State) (V : Fin R.N → NodeView) (net : List Msg)
    (xnet : List XMsg) (evs : List AntCheck.Event) (G : RaftFacts) (n : Fin R.N) (m : MemRec)
    (rest : List MemRec),
    InMask msk R net xnet → SimPreD R dec S V net xnet evs G → R.drv.batch = false →
    (R.md.async = true ∨ R.drv.parallel = true) → (V n).mems = m :: rest →
    (R.md.async = true → ∃ j ∈ (V n).jobs.head?, j.wrec = some m ∧ j.ran = false) →
    SimStepD R dec evs G (evWrite (nodeId n) m.term m.vote m.commit m.ents m.snap)
      (setV V n { V n with dur := (V n).dur.write m, undo := some (V n).dur, made := false,
                           mems := rest, jobs := markHead (V n).jobs }) net xnet

/-- **A write job with nothing to write is run** (async, reportless: `runWrite` of a job holding only
messages, or a batch job before its flushes). -/
abbrev antSim_runW0_in.stmt : Prop :=
  ∀ (msk : SimMask), msk ≤ mskB25 →
  ∀ (R : RunCfg) (dec : CCDec) (S : AntCheck.State) (V : Fin R.N → NodeView) (net : List Msg)
    (xnet : List XMsg) (G : RaftFacts) (n : Fin R.N) (j : WJob) (js : List WJob),
    InMask msk R net xnet → AntSimD R dec S V net xnet → RaftLaws G → GlobalOk R S net G →
    R.md.async = true → (V n).jobs = j :: js → j.wrec = none → j.ran = false →
    AntSimD R dec S (setV V n { V n with jobs := { j with ran := true } :: js }) net xnet

/-- **The end of a sync batch** (reportless: `flush`'s `note("write")` after the batch's `Advance`): a
batching node between inputs again takes the next `Ready`'s drain as the write's (`by = "write"`), so
that the batch's `Advance` is `ReachIn.advance` (whose `DrainBy` has `"write"`, `Input.storeAck`'s). -/
abbrev antSim_batchEnd_in.stmt : Prop :=
  ∀ (msk : SimMask), msk ≤ mskB2 →
  ∀ (R : RunCfg) (dec : CCDec) (S : AntCheck.State) (V : Fin R.N → NodeView) (net : List Msg)
    (xnet : List XMsg) (n : Fin R.N),
    InMask msk R net xnet → AntSimD R dec S V net xnet → R.drv.batch = true → (V n).Idle →
    AntSimD R dec S (setV V n { V n with byE := go!"write" }) net xnet

/-- **`wrote`** (B 502-504): the announced write is made (async: right after `write`; `-parallel`:
after its write; batch: after the batch's sends); the undo record goes. -/
abbrev antSim_wrote_in.stmt : Prop :=
  ∀ (msk : SimMask), msk ≤ mskB2 →
  ∀ (R : RunCfg) (dec : CCDec) (S : AntCheck.State) (V : Fin R.N → NodeView) (net : List Msg)
    (xnet : List XMsg) (evs : List AntCheck.Event) (G : RaftFacts) (n : Fin R.N),
    InMask msk R net xnet → SimPreD R dec S V net xnet evs G →
    (R.md.async = true ∨ R.drv.parallel = true ∨ R.drv.batch = true) → (V n).undo ≠ none →
    SimStepD R dec evs G (evWrote (nodeId n)) (setV V n { V n with undo := none, made := true })
      net xnet

/-- **`send` of a message that waited for its write** (`doneWrite`, B 510-593 with `cause`, or `b` in
a batch): the run head job's next message, with its drain's cause and `by`. -/
abbrev antSim_sendJ_in.stmt : Prop :=
  ∀ (msk : SimMask), msk ≤ mskB25 →
  ∀ (R : RunCfg) (dec : CCDec) (S : AntCheck.State) (V : Fin R.N → NodeView) (net : List Msg)
    (xnet : List XMsg) (evs : List AntCheck.Event) (G : RaftFacts) (n : Fin R.N) (j : WJob)
    (js : List WJob) (q : Msg) (rest : List Msg),
    InMask msk R net xnet → SimPreD R dec S V net xnet evs G → R.md.async = true →
    (V n).jobs = j :: js → j.ran = true → j.resp = q :: rest → MsgFacts G q →
    SimStepD R dec evs G
      (if R.drv.batch then evSendB (nodeId n) j.byE q else evSendC (nodeId n) j.byE q j.cause)
      (setV V n { V n with jobs := { j with resp := rest } :: js }) (net ++ [q]) xnet

/-- **A write job done** (async, reportless: `doneWrite` after its messages; raft's step of the
write's acknowledgement and its responses to the node itself is the next input, `storeAck`). -/
abbrev antSim_doneW_in.stmt : Prop :=
  ∀ (msk : SimMask), msk ≤ mskB25 →
  ∀ (R : RunCfg) (dec : CCDec) (S : AntCheck.State) (V : Fin R.N → NodeView) (net : List Msg)
    (xnet : List XMsg) (G : RaftFacts) (n : Fin R.N) (j : WJob) (js : List WJob),
    InMask msk R net xnet → AntSimD R dec S V net xnet → RaftLaws G → GlobalOk R S net G →
    R.md.async = true → (V n).Idle → (V n).jobs = j :: js → j.ran = true → j.resp = [] →
    AntSimD R dec S (setV V n { V n with jobs := js }) net xnet

/-- **`apply` by the apply goroutine** (async, B 598-609 with `a`): the oldest queued committed
entries are handed out. -/
abbrev antSim_applyA_in.stmt : Prop :=
  ∀ (msk : SimMask), msk ≤ mskB25 →
  ∀ (R : RunCfg) (dec : CCDec) (S : AntCheck.State) (V : Fin R.N → NodeView) (net : List Msg)
    (xnet : List XMsg) (evs : List AntCheck.Event) (G : RaftFacts) (n : Fin R.N) (a : AJob)
    (aj : List AJob),
    InMask msk R net xnet → SimPreD R dec S V net xnet evs G → R.md.async = true →
    (V n).ajobs = a :: aj → a.ran = false → a.ents ≠ [] →
    SimStepD R dec evs G (evApplyA (nodeId n) a.byE a.ents)
      (setV V n { V n with delivered := (V n).delivered ++ a.ents,
                           ajobs := { a with ran := true } :: aj }) net xnet

/-- **An apply job done** (async, reportless: `doneApply`, or `runApply` of no entries; raft's step of
the apply's acknowledgement is the next input). -/
abbrev antSim_doneA_in.stmt : Prop :=
  ∀ (msk : SimMask), msk ≤ mskB25 →
  ∀ (R : RunCfg) (dec : CCDec) (S : AntCheck.State) (V : Fin R.N → NodeView) (net : List Msg)
    (xnet : List XMsg) (G : RaftFacts) (n : Fin R.N) (a : AJob) (aj : List AJob),
    InMask msk R net xnet → AntSimD R dec S V net xnet → RaftLaws G → GlobalOk R S net G →
    R.md.async = true → (V n).ajobs = a :: aj → (a.ran = true ∨ a.ents = []) →
    AntSimD R dec S (setV V n { V n with ajobs := aj }) net xnet

/-! ## `-parallel` (a sync leader's `Ready`: `mem`, the requests, `write`, `wrote`, the rest) -/

/-- **`mem`, `-parallel`** (B 450-459): a leader's sync `Ready` that writes or changes the reported
role is reported; its write is queued for `write`; its messages pending, the requests (appends and
heartbeats) moved first, in their order, then the others in theirs (`parallel` sends the requests
before the write and the rest after it). No write is queued and no split write is in progress before
it (the loop head's, synchronous storage). -/
abbrev antSim_memP_in.stmt : Prop :=
  ∀ (msk : SimMask), msk ≤ mskB2 →
  ∀ (R : RunCfg) (dec : CCDec) (S : AntCheck.State) (V : Fin R.N → NodeView) (net : List Msg)
    (xnet : List XMsg) (evs : List AntCheck.Event) (G : RaftFacts) (n : Fin R.N) (r₁ : RState)
    (rd : ReadyD) (w : Bool) (Adm : List EntryM → CCState → Prop),
    InMask msk R net xnet → SimPreD R dec S V net xnet evs G →
    R.md.async = false → R.drv.batch = false → R.drv.parallel = true →
    ReachIn msk R dec Adm net xnet n (V n) r₁ → ReadyOutP R n (V n) r₁ rd → rd.role = .leader →
    rd.snap = none → Reported (V n) rd → (w = true ↔ Writes (V n) rd) →
    Told (V n) → ReadyFacts G (nodeId n) r₁ → TermRoom (V n) → (V n).mems = [] → (V n).parts = [] →
    SimStepD R dec evs G
      (evMem (nodeId n) (V n).byE (roleStr rd.pre rd.role) rd.term rd.vote rd.commit rd.ents none w)
      (setV V n { ((V n).drainOf r₁ rd) with
        pend := rd.msgs.filter isReqM ++ rd.msgs.filter (fun q => !isReqM q),
        mems := if w then (V n).mems ++ [rd.memRec (V n)] else (V n).mems }) net xnet

/-! ## Split writes (sync, `splitTermEntriesCommit`; B2.5: `mskB25`) -/

/-- **`ready`, the first part of a split write** (B 439-447): a sync `Ready` that writes is reported
part by part; the first part is announced at the drain's start. -/
abbrev antSim_readyS_in.stmt : Prop :=
  ∀ (msk : SimMask), msk ≤ mskB25 →
  ∀ (R : RunCfg) (dec : CCDec) (S : AntCheck.State) (V : Fin R.N → NodeView) (net : List Msg)
    (xnet : List XMsg) (evs : List AntCheck.Event) (G : RaftFacts) (n : Fin R.N) (r₁ : RState)
    (rd : ReadyD) (p : MemRec) (ps : List MemRec) (Adm : List EntryM → CCState → Prop),
    InMask msk R net xnet → SimPreD R dec S V net xnet evs G →
    R.md.async = false → R.drv.batch = false → R.drv.split ≠ 0 →
    ReachIn msk R dec Adm net xnet n (V n) r₁ → ReadyOutP R n (V n) r₁ rd →
    ¬ (R.drv.parallel = true ∧ rd.role = .leader) → rd.snap = none → Writes (V n) rd →
    splitParts (V n).dur rd (rd.memRec (V n)) = p :: ps →
    Told (V n) → ReadyFacts G (nodeId n) r₁ → TermRoom (V n) →
    SimStepD R dec evs G
      (evReady (nodeId n) (V n).byE (roleStr rd.pre rd.role) p.term p.vote p.commit p.ents)
      (setV V n { ((V n).drainOf r₁ rd) with dur := (V n).dur.write p, undo := some (V n).dur,
                                             made := false, parts := ps }) net xnet

/-- **`ready`, a later part of a split write**: the next part, with the reported role. -/
abbrev antSim_readyP_in.stmt : Prop :=
  ∀ (msk : SimMask), msk ≤ mskB25 →
  ∀ (R : RunCfg) (dec : CCDec) (S : AntCheck.State) (V : Fin R.N → NodeView) (net : List Msg)
    (xnet : List XMsg) (evs : List AntCheck.Event) (G : RaftFacts) (n : Fin R.N) (p : MemRec)
    (ps : List MemRec),
    InMask msk R net xnet → SimPreD R dec S V net xnet evs G → R.drv.split ≠ 0 →
    (V n).parts = p :: ps → Told (V n) →
    SimStepD R dec evs G
      (evReady (nodeId n) (V n).byE (roleS (V n)) p.term p.vote p.commit p.ents)
      (setV V n { V n with dur := (V n).dur.write p, undo := some (V n).dur, made := false,
                           parts := ps }) net xnet

/-! ## Batching (`note`, `flush`) -/

/-- **`mem`, batching** (`note`, B 450-459): after an input, what raft has in memory is reported when
its hard state or role changed, it appended, or the input was a request to append (`w` but for a
role change alone); raft's state moves, its outbox kept for the batch's `Ready`. `es` is what the
input appended (the full log after it is the one before cut at `es`'s first index). -/
abbrev antSim_note_in.stmt : Prop :=
  ∀ (msk : SimMask), msk ≤ mskB2 →
  ∀ (R : RunCfg) (dec : CCDec) (S : AntCheck.State) (V : Fin R.N → NodeView) (net : List Msg)
    (xnet : List XMsg) (evs : List AntCheck.Event) (G : RaftFacts) (n : Fin R.N) (r₁ : RState)
    (pre : Bool) (es : List EntryM) (w : Bool) (Adm : List EntryM → CCState → Prop),
    InMask msk R net xnet → SimPreD R dec S V net xnet evs G → R.drv.batch = true →
    ReachIn msk R dec Adm net xnet n (V n) r₁ →
    (∀ e0 ∈ es.head?, r₁.full = (V n).r.full.take (uint.nat e0.Index' - 1) ++ es) →
    (es = [] → r₁.full = (V n).r.full) →
    (pre = true → r₁.p.role = .follower ∧ (R.k n).prevote = true) →
    (w = true ↔ (r₁.p.term ≠ (V n).ps.term ∨ r₁.p.vote ≠ (V n).ps.vote ∨
      r₁.p.commit ≠ (V n).ps.commit ∨ es ≠ [] ∨ ReqCause (V n) r₁)) →
    (w = true ∨ roleStr pre r₁.p.role ≠ roleS (V n)) →
    Told (V n) → ReadyFacts G (nodeId n) r₁ → TermRoom (V n) →
    SimStepD R dec evs G
      (evMemB (nodeId n) (V n).byE (roleStr pre r₁.p.role) r₁.p.term r₁.p.vote r₁.p.commit es w)
      (setV V n { V n with r := r₁, pre := pre,
                           mems := if w then (V n).mems ++ [memRecB (V n) r₁ pre es] else (V n).mems }) net xnet

/-- **An input a batching node does not report** (`note` with nothing changed). -/
abbrev antSim_noteQ_in.stmt : Prop :=
  ∀ (msk : SimMask), msk ≤ mskB2 →
  ∀ (R : RunCfg) (dec : CCDec) (S : AntCheck.State) (V : Fin R.N → NodeView) (net : List Msg)
    (xnet : List XMsg) (G : RaftFacts) (n : Fin R.N) (r₁ : RState)
    (Adm : List EntryM → CCState → Prop),
    InMask msk R net xnet → AntSimD R dec S V net xnet → RaftLaws G → GlobalOk R S net G →
    R.drv.batch = true → ReachIn msk R dec Adm net xnet n (V n) r₁ →
    r₁.full = (V n).r.full → r₁.p.term = (V n).ps.term → r₁.p.vote = (V n).ps.vote →
    r₁.p.commit = (V n).ps.commit → r₁.p.role = (V n).ps.role → ¬ ReqCause (V n) r₁ →
    ReadyFacts G (nodeId n) r₁ →
    AntSimD R dec S (setV V n { V n with r := r₁ }) net xnet

/-- **The batch's `Ready`** (sync, reportless: `flush`'s `Ready()`, before its `flush` reports): taken
at raft's state, read against the disk (the last batch's write); the drain phase, `by = "batch"`. -/
abbrev antSim_readyB_in.stmt : Prop :=
  ∀ (msk : SimMask), msk ≤ mskB2 →
  ∀ (R : RunCfg) (dec : CCDec) (S : AntCheck.State) (V : Fin R.N → NodeView) (net : List Msg)
    (xnet : List XMsg) (G : RaftFacts) (n : Fin R.N) (rd : ReadyD),
    InMask msk R net xnet → AntSimD R dec S V net xnet → RaftLaws G → GlobalOk R S net G →
    R.drv.batch = true → R.md.async = false → (V n).Idle →
    ReadyOutP R n (V n) (V n).r rd → rd.pre = (V n).pre → ReadyFacts G (nodeId n) (V n).r →
    AntSimD R dec S
      (setV V n { ((V n).drainOf (V n).r rd) with byE := go!"batch", cause := none, xcause := none,
                                                  told := false }) net xnet

/-- **`flush`** (batch, B 474-478): the oldest queued `mem` joins the batch's write (`more` for every
one after the first): the disk is its result; the first's undo record is the batch's. -/
abbrev antSim_flush_in.stmt : Prop :=
  ∀ (msk : SimMask), msk ≤ mskB2 →
  ∀ (R : RunCfg) (dec : CCDec) (S : AntCheck.State) (V : Fin R.N → NodeView) (net : List Msg)
    (xnet : List XMsg) (evs : List AntCheck.Event) (G : RaftFacts) (n : Fin R.N) (m : MemRec)
    (rest : List MemRec) (more : Bool),
    InMask msk R net xnet → SimPreD R dec S V net xnet evs G → R.drv.batch = true →
    (V n).mems = m :: rest → (more = true → (V n).undo ≠ none) →
    SimStepD R dec evs G (evFlush (nodeId n) more)
      (setV V n { V n with dur := (V n).dur.write m, mems := rest,
                           undo := if more then (V n).undo else some (V n).dur,
                           made := if more then (V n).made else false }) net xnet

/-- **`net`** (batch, B 483-492): the batch's write is announced: the disk's hard state and its
entries from the lowest conflict with the disk before the batch. -/
abbrev antSim_net_in.stmt : Prop :=
  ∀ (msk : SimMask), msk ≤ mskB2 →
  ∀ (R : RunCfg) (dec : CCDec) (S : AntCheck.State) (V : Fin R.N → NodeView) (net : List Msg)
    (xnet : List XMsg) (evs : List AntCheck.Event) (G : RaftFacts) (n : Fin R.N) (d0 : DurW)
    (es : List EntryM),
    InMask msk R net xnet → SimPreD R dec S V net xnet evs G → R.drv.batch = true →
    (V n).undo = some d0 →
    (∀ e0 ∈ es.head?, (V n).dur.log = (V n).dur.log.take (uint.nat e0.Index' - 1) ++ es ∧
      ∀ e ∈ d0.log[uint.nat e0.Index' - 1]?, e.Term' ≠ e0.Term') →
    (es = [] → (V n).dur.log = d0.log) →
    SimStepD R dec evs G (evNet (nodeId n) (V n).dur.term (V n).dur.vote (V n).dur.commit es) V
      net xnet

/-- **`made`** (batch, B 496-499): the batch's write is on disk. -/
abbrev antSim_made_in.stmt : Prop :=
  ∀ (msk : SimMask), msk ≤ mskB2 →
  ∀ (R : RunCfg) (dec : CCDec) (S : AntCheck.State) (V : Fin R.N → NodeView) (net : List Msg)
    (xnet : List XMsg) (evs : List AntCheck.Event) (G : RaftFacts) (n : Fin R.N),
    InMask msk R net xnet → SimPreD R dec S V net xnet evs G → R.drv.batch = true →
    (V n).undo ≠ none →
    SimStepD R dec evs G (evMade (nodeId n)) (setV V n { V n with made := true }) net xnet

/-- **`send` of a batch** (B 510-593 with `b`): the next message of the batch's `Ready` (sync: after
`made`; async: those sent at once, never a vote request or an `AfterAppTy` one). -/
abbrev antSim_sendB_in.stmt : Prop :=
  ∀ (msk : SimMask), msk ≤ mskB2 →
  ∀ (R : RunCfg) (dec : CCDec) (S : AntCheck.State) (V : Fin R.N → NodeView) (net : List Msg)
    (xnet : List XMsg) (evs : List AntCheck.Event) (G : RaftFacts) (n : Fin R.N) (q : Msg)
    (rest : List Msg),
    InMask msk R net xnet → SimPreD R dec S V net xnet evs G → R.drv.batch = true →
    (V n).pend = q :: rest → MsgFacts G q →
    ((q.ty = .vote ∨ AfterAppTy q.ty) → (V n).made = true) →
    SimStepD R dec evs G (evSendB (nodeId n) (V n).byE q) (setV V n { V n with pend := rest })
      (net ++ [q]) xnet

end b2

end AntSim
end EtcdGrove
end Perennial
