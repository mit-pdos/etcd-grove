/-
Lean-first (no Rocq counterpart).

# The refinement to Antithesis's binding: the relation (#33 S3c step 5 / S4; parity B1)

`AntSim R dec S V net xnet` (`notes/antithesis-parity-design.md` §3.3; S4's
`notes/antithesis-rawnode-design.md` §3.2, C1-C4) relates the binding's state `S` (the S3b
transcription's `AntCheck.State`) for the run `R` (`RunCfg`: `N` servers, `K` initial voters, boot,
flags, mask), each node's view `V n` (raft's `RState` between inputs, or at its last `Ready` in a
drain, with the binding's disk, announced write, queue, reads and configuration of it, §3.2), the
messages sent so far `net` and the transfer messages sent `xnet`; `dec` is the run's conf-change
decoder. `GlobalOk R S net G` (C5) says that what `S` and `net` hold is certified by raft's global
facts `G` (`RaftFacts`: the pure content of the persistent ghost facts `isLeader`, `isVote`,
`logRecs`, `isCamp`, `isCommitted`, `commitIn`, and for snapshots and conf changes the certified
prefixes and admissible configurations, which the harness's invariant keeps and turns into a
`RaftFacts` satisfying `RaftLaws` before each report). `Prefix cfg evs S`
(`notes/antithesis-s4-design.md` §3): the checker took `evs`, rejected none, found no violation,
and is at `S`; `Prefix.accepts` turns it into the closed statement's `Accepts`. `SimPre`/`SimStep`
are every statement's frame (`Stmts.lean`).

Imports raft's protocol model, `InputEnd`, `StepR` (`RState`, `CCState`, `cfgFold`), and the
transcription.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.Abs
public import Proof.go_etcd_io.raft.v3.Protocol.InputEnd
public import Proof.go_etcd_io.raft.v3.Protocol.StepR

@[expose] public section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace AntSim

open GMap go_etcd_io.raft.v3

/-! ## The checker's prefix -/

/-- The checker from `init0 cfg` has taken `evs` (each with the `GC` steps due before it), rejected
none, found no violation, and is at `S` (`notes/antithesis-s4-design.md` §3). -/
def Prefix (cfg : AntCheck.Config) (evs : List AntCheck.Event) (S : AntCheck.State) : Prop :=
  ∃ c : AntCheck.Checker,
    ((AntCheck.init0 cfg).bind fun s => evs.foldlM (fun c ev => c.next ev) ({ state := s } : AntCheck.Checker))
      = .ok c ∧ c.done = false ∧ c.state = S

/-- **A prefix is accepted**: the stream so far is `ACCEPTED` (`Checker.finish` of a checker that
is not done). -/
theorem Prefix.accepts {cfg : AntCheck.Config} {evs : List AntCheck.Event} {S : AntCheck.State}
    (h : Prefix cfg evs S) : AntCheck.Accepts cfg evs := by
  obtain ⟨c, hc, hd, -⟩ := h
  refine ⟨c.finish, ?_, ?_⟩
  · unfold AntCheck.run
    cases h0 : AntCheck.init0 cfg with
    | error e => rw [h0] at hc; cases hc
    | ok s =>
      rw [h0] at hc
      change evs.foldlM (fun c ev => c.next ev) ({ state := s } : AntCheck.Checker) = .ok c at hc
      change (evs.foldlM (fun c ev => c.next ev) ({ state := s } : AntCheck.Checker) >>= fun c =>
        pure c.finish) = _
      rw [hc]; rfl
  · simp [AntCheck.Checker.finish, hd]

section rel
variable [GooseExts]

/-! ## The run's initial state -/

/-- The entry a bootstrapped run's node writes first (`node.start`: `{Term: 1, Index: 1, Data:
bootData()}`, a normal entry): `entOf` reports it as the binding's `"config"` entry (B 742). -/
def bootEnt : EntryM := EntryM.mk (W64 1) (W64 1) (W32 0) bootData

/-- The log every node of the run starts with: empty, or the boot entry (`BootInit`, B 733-753). -/
def bootLog (R : RunCfg) : List EntryM := if R.boot then [bootEnt] else []

/-- The initial voters, `1, …, K`. -/
def RunCfg.voters0 (R : RunCfg) : GSet w64 :=
  GMap.listToSet ((List.range R.K).map fun (i : Nat) => W64 ((i : Int) + 1))

/-- The initial configuration state: voters `1, …, K`, no learner, not joint (the conf state raft
starts from, before any conf entry). -/
def RunCfg.c0 (R : RunCfg) : CCState :=
  { cfg := CfgM.simple R.voters0 ∅, prs := cfgFlags R.voters0 ∅ }

/-- The static configuration of the S4 run (`R3`): voters `1, 2, 3`. -/
def voters3 : GSet w64 := GMap.listToSet [W64 1, W64 2, W64 3]

/-- A set of ids as the binding's set of names (`idNames`, sorted): the ids `1, …, N` in it. The
configurations of the run hold only those (the harness proposes no other id). -/
def idsView (N : Nat) (s : GSet w64) : AntCheck.SSet :=
  AntCheck.setOf ((List.range N).filterMap fun (i : Nat) =>
    if W64 ((i : Int) + 1) ∈ s then some (nameOf (W64 ((i : Int) + 1))) else none)

/-- A configuration as the binding's `Conf` (`Types.lean`: `cin`, `cout`; the binding has no
learners). -/
def confView (N : Nat) (cs : CCState) : AntCheck.Conf :=
  { cin := idsView N cs.cfg.incoming, cout := idsView N cs.cfg.outgoing }

/-- The binding's `LastConf(l, k)` (R 160) over raft's entries: the position (from 1) of the last
conf entry among `l`'s first `k`, `0` for none. -/
def lastConfIdx (l : List EntryM) (k : Nat) : Nat :=
  (List.range k).foldl (fun last (i : Nat) =>
    match l[i]? with
    | some e => if IsConfEnt e then i + 1 else last
    | none => last) 0

/-! ## A node's view -/

/-- What the binding holds as a node's disk: the last announced write (`currentTerm`, `voteFor`,
`log`, `commitIndex`, B 290-436). `log` is the full log, from index 1. -/
structure DurW where
  term : w64
  vote : w64
  commit : w64
  log : List EntryM
  deriving Inhabited

/-- Async (parity B2): an announced in-memory state whose write comes later (the binding's
`queue[n]`, B 450-459), with what its `mem` report said. -/
structure MemRec where
  role : Role
  pre : Bool
  term : w64
  vote : w64
  commit : w64
  ents : List EntryM
  snap : Option entryID
  cause : Option Msg
  byE : AntCheck.Str

/-- What the relation knows of a node (the invariant's view fragment, `γ.view`): raft's state `r`
between inputs, or at its last `Ready` in a drain (`toRState`); the committed entries it handed out
(`delivered`, `RNState.delivered`); the binding's disk of it (`dur`, the last announced write), the
disk before that write while it is not made (`undo`, `made`: what a restart may revert to,
B 349-359, 496), the announced in-memory states not yet written (`mems`, async); the configuration
the binding counts with and its index (`conf`, `confAt`); whether the last reported role was
`precandidate` (`pre`); the read contexts asked and not given, with the committed length known when each was asked
(`reads`); whether it runs (`alive`,
false from a restart's stop to its `boot`); and, in a drain after a `Ready` (§3.2's drain phase),
what that `Ready` left: the self-addressed messages `Advance` will step (`qs`), its messages and
transfer messages not yet reported (`pend`, `xpend`, in the `Ready`'s order), its committed
entries not yet reported (`ce`) and its read states not yet reported (`rpend`). `byE` and `cause`
(`xcause` for a transfer message) are the drain's (`by`, and the message handled for `by = recv`); `told` says its `recv` was reported (`reportCause`), so that the binding's
`pending[n]` is that message. Between inputs `qs`, `pend`, `xpend`, `ce`, `rpend` are empty (`Idle`). -/
structure NodeView where
  r : RState
  delivered : List EntryM
  dur : DurW
  undo : Option DurW := none
  made : Bool := true
  mems : List MemRec := []
  conf : CCState
  confAt : Nat := 0
  pre : Bool := false
  reads : List (AntCheck.Str × Nat) := []
  alive : Bool := true
  qs : List Msg := []
  pend : List Msg := []
  xpend : List XMsg := []
  ce : List EntryM := []
  rpend : List ReadStateM := []
  byE : AntCheck.Str := []
  cause : Option Msg := none
  xcause : Option XMsg := none
  told : Bool := false

/-- The view's protocol state (the S4 view's `ps`, kept as a projection). -/
abbrev NodeView.ps (v : NodeView) : PState := v.r.p

/-- The disk a node in sync mode has between writes: its own hard state and full log. -/
def durOf (r : RState) : DurW := ⟨r.p.term, r.p.vote, r.p.commit, r.full⟩

/-- The role the binding has for the node (`roleOf`, `"precandidate"` if `pre`). -/
def roleS (v : NodeView) : AntCheck.Str := roleStr v.pre v.ps.role

/-- Between inputs: nothing of a `Ready` left (`Advance` done, `HasReady` false). -/
def NodeView.Idle (v : NodeView) : Prop :=
  v.qs = [] ∧ v.pend = [] ∧ v.xpend = [] ∧ v.ce = [] ∧ v.rpend = []

/-- A fresh node (`NewRawNode.emptyStartSpec`'s `pInit`): term 0, no vote, no leader, follower, no
tally, empty outbox, empty log from `base0`, commit 0, no `Match`. -/
def PInit (ps : PState) : Prop :=
  ps.term = W64 0 ∧ ps.vote = W64 0 ∧ ps.lead = W64 0 ∧ ps.role = .follower ∧ ps.votes = ∅ ∧
  ps.outbox = [] ∧ ps.base = base0 ∧ ps.log = [] ∧ ps.commit = W64 0 ∧ ps.matched = ∅

/-- **A node of the run `R` at its start** (`NewRawNode` on the fresh storage, or on the bootstrapped
one: `HardState{Term: 1}` and the boot entry): term 0 or 1, no vote, no leader, follower, no tally,
empty outbox, the log `bootLog R` from `base0`, commit 0, no `Match`; nothing applied, no pending
conf index, no snapshot, at the initial configuration, no ghost prefix, no deferred read request. -/
def PInitR (R : RunCfg) (r : RState) : Prop :=
  r.p.term = W64 (if R.boot then 1 else 0) ∧ r.p.vote = W64 0 ∧ r.p.lead = W64 0 ∧
  r.p.role = .follower ∧ r.p.votes = ∅ ∧ r.p.outbox = [] ∧ r.p.base = base0 ∧
  r.p.log = bootLog R ∧ r.p.commit = W64 0 ∧ r.p.matched = ∅ ∧
  r.applied = W64 0 ∧ r.pci = W64 0 ∧ r.snap = false ∧ r.cidx = 0 ∧ r.cfg = R.c0 ∧ r.fp = [] ∧
  r.p.rd.pend = []

/-- A log from index 1 whose entries carry their positions as indices (`PlogWf`'s index part): the
binding's positions (`TermAt`, `SubSeq`, an `apply`'s `first`) are raft's indices. -/
def LogIdx (l : List EntryM) : Prop := ∀ (k : Nat) (e : EntryM), l[k]? = some e → uint.Z e.Index' = (k : Int) + 1

/-- The binding's constants are the run's and its per-server lists are of its `N` servers. -/
def Shape (R : RunCfg) (S : AntCheck.State) : Prop :=
  S.cfg = R.cfg ∧ S.currentTerm.length = R.N ∧ S.voteTerm.length = R.N ∧ S.voteFor.length = R.N ∧
  S.log.length = R.N ∧ S.commitIndex.length = R.N ∧ S.role.length = R.N ∧
  S.lastApplied.length = R.N ∧ S.config.length = R.N ∧ S.confAt.length = R.N ∧
  S.confirmed.length = R.N ∧ S.undo.length = R.N ∧ S.pending.length = R.N ∧
  S.queue.length = R.N ∧ S.reads.length = R.N

/-- An ack fact `[type |-> "ack", src, dst, term |-> t, index |-> k']` with `k' ≥ k` is in `msgs`. -/
def AckIn (S : AntCheck.State) (src dst : AntCheck.Str) (t k : Int) : Prop :=
  ∃ a ∈ S.msgs, a.type = go!"ack" ∧ a.src = src ∧ a.dst = dst ∧ a.term = t ∧ k ≤ a.index

/-! ## C1-C2: the per-node part -/

/-- **C1, the node's disk** (`DiskIs`): the binding's term, vote, log and commit for `n` are the
view's disk's (every write is announced by its report before it is made). -/
def DiskIs (S : AntCheck.State) {N : Nat} (n : Fin N) (v : NodeView) : Prop :=
  S.currentTerm[n.val]! = uint.Z v.dur.term ∧ S.vote n.val = nameOf v.dur.vote ∧
  S.log[n.val]! = logOf v.dur.log ∧ S.commitIndex[n.val]! = uint.Z v.dur.commit

/-- **C1, the node's in-memory part** (`MemIs`): the binding's role (raft's role of the last reported
state: `inMemory` stores `"follower"` for a reported `"precandidate"`, B 248-249, so the pre flag is
not part of it), applied index (what was handed out), configuration and its index are the view's. -/
def MemIs (N : Nat) (S : AntCheck.State) (n : Fin N) (v : NodeView) : Prop :=
  S.role[n.val]! = roleOf v.ps.role ∧ S.lastApplied[n.val]! = (v.delivered.length : Int) ∧
  S.config[n.val]! = confView N v.conf ∧ S.confAt[n.val]! = (v.confAt : Int)

/-- **C1, sync mode's disk** (not batching, splitting or sending early: those are parity B2's): no
write queued (no `mem` report in sync mode), and the disk is raft's own state (what the last
`ready` announced and wrote), and an announced write is not `made` before its `send`s or its
`apply` end it (no `made` report in sync mode). -/
def SyncDisk (R : RunCfg) (v : NodeView) : Prop :=
  R.md.async = false → R.drv.batch = false → R.drv.split = 0 → R.drv.parallel = false →
    v.mems = [] ∧ v.dur = durOf v.r ∧ (v.undo ≠ none → v.made = false)

/-- **C1, the announced write** (`undo[n]`, B 349-359): there is one exactly when the view has the
disk before it; its `made` is the view's; and what it reverts to (term, vote, commit, the log's kept
prefix and the suffix the write replaced, B 170-181) is that disk. -/
def UndoIs (S : AntCheck.State) {N : Nat} (n : Fin N) (v : NodeView) : Prop :=
  ((S.undo[n.val]!).isNone ↔ v.undo = none) ∧
  ∀ p, S.undo[n.val]! = some p → p.made = v.made ∧ ∃ d, v.undo = some d ∧
    p.term = uint.Z d.term ∧ S.voteOf p.voteTerm p.voteFor p.term = nameOf d.vote ∧
    p.commit = uint.Z d.commit ∧ (S.log[n.val]!).take p.keep.toNat ++ p.suffix = logOf d.log

/-- A queued `mem` report as the binding keeps it (B 452): the report and the message handled. -/
def MemRec.item (id : w64) (m : MemRec) : AntCheck.QItem :=
  { ev := evMem id m.byE (roleStr m.pre m.role) m.term m.vote m.commit m.ents m.snap,
    m := (m.cause.map (fun c => msgOf c id)).toList }

/-- **C1, the queue** (async, B 450-459): the binding's `queue[n]` is the view's announced
in-memory states, in order. -/
def QueueIs (S : AntCheck.State) {N : Nat} (n : Fin N) (v : NodeView) : Prop :=
  S.queue[n.val]! = v.mems.map (MemRec.item (nodeId n))

/-- **C1, the reads** (B 657-667): the binding's `reads[n]` are the view's contexts asked and not
given, in order, each with its floor (the chain's length at its `readreq`) within the view's (the
committed log's length known then, `G.committed`, which the chain is a prefix of: C5). -/
def ReadsIs (S : AntCheck.State) {N : Nat} (n : Fin N) (v : NodeView) : Prop :=
  (S.reads[n.val]!).map (·.ctx) = v.reads.map (·.1) ∧
  ∀ (k : Nat) (a : AntCheck.ReadRec) (b : AntCheck.Str × Nat), (S.reads[n.val]!)[k]? = some a →
    v.reads[k]? = some b → a.floor ≤ (b.2 : Int)

/-- **C1, the configuration** (`ConfLag`): the binding's configuration is raft's applied one, but
after a snapshot restored and not yet applied, when the binding already switched to the
snapshot's (design §6.3). -/
def ConfLag (dec : CCDec) (R : RunCfg) (v : NodeView) : Prop :=
  (v.conf = v.r.cfg ∧ v.confAt = lastConfIdx v.r.full v.r.cidx) ∨
  (v.r.snap = true ∧ ∃ cs, cfgFold dec R.c0 v.r.fp = some cs ∧ v.conf = cs ∧
     v.confAt = lastConfIdx v.r.fp v.r.fp.length)

/-- Normal entries (`EntryNormal = 0`; `HarnessDefs.lean`'s `AllNormal`): a proposal's, a leader's
empty entry, the boot entry. Without conf changes every entry of the run is one. -/
def EntsNormal (es : List EntryM) : Prop := ∀ e ∈ es, e.Type' = W32 0

/-- The message types the harness's network carries under the mask `md` (`stepTypes md`'s protocol
types): `antStepTypes`, and pre-vote, read-index and snapshot messages when their features are on. -/
def NetTy (md : RnMode) (ty : MsgType) : Prop :=
  ty = .app ∨ ty = .appResp ∨ ty = .vote ∨ ty = .voteResp ∨ ty = .heartbeat ∨ ty = .heartbeatResp ∨
  (md.prevote = true ∧ (ty = .preVote ∨ ty = .preVoteResp)) ∨
  (md.reads = true ∧ (ty = .readIndex ∨ ty = .readIndexResp)) ∨ (md.snapshots = true ∧ ty = .snap)

/-- **A message under the run's mask** (`MsgMask`): without conf changes an append's or a
proposal's entries are normal; without snapshots it is no snapshot; it is of a type the network
carries under the run's features, or a (forwarded) proposal; without reads a heartbeat or its
response carries no context (a leader's queue is empty, `hbCtx`, and a response echoes it). -/
def MsgMask (R : RunCfg) (m : Msg) : Prop :=
  (R.md.confChanges = false → (m.ty = .app ∨ m.ty = .propose) → EntsNormal m.entries) ∧
  (R.md.snapshots = false → m.ty ≠ .snap) ∧ (NetTy R.md m.ty ∨ m.ty = .propose) ∧
  (R.md.reads = false → (m.ty = .heartbeat ∨ m.ty = .heartbeatResp) → m.ctx = [])

/-- **C1, raft's side**: the outbox empty between `Ready`s (taken by the last one); without
snapshots the log from `base0`, no ghost prefix and no snapshot restored; without conf changes the
initial configuration and only normal entries (raft's and the disk's); the disk's log's indices its
positions; what was handed out (`delivered`, and in a drain `ce`) a prefix of the disk's log within
its commit; the `Ready`'s messages not yet sent under the mask (`MsgMask`); the disk's term within
raft's (a write is of a state raft had, and terms only grow: what `GC` needs to keep a leader's and a
candidate's records at raft's term); a reported pre-candidate is a follower to raft (`toPState`), so
that a leader's binding role is `leader`; without reads no read request is deferred (`rd.pend`, which only `MsgReadIndex` fills) and a leader has none pending (it
becomes leader with the read-only queue reset, `pbecomeLeader`, and none is queued without reads:
a tick's heartbeats carry no context, `hbCtx`); a reported pre-candidate is at a node with
pre-vote on (a `Ready` reports `PreCandidate` only when raft campaigned with pre-vote). -/
def NodeFacts (R : RunCfg) (n : Fin R.N) (v : NodeView) : Prop :=
  v.ps.outbox = [] ∧ (R.md.snapshots = false → v.ps.base = base0 ∧ v.r.fp = [] ∧ v.r.snap = false) ∧
  (R.md.confChanges = false →
    v.r.cfg.cfg = CfgM.simple R.voters0 ∅ ∧ EntsNormal v.r.full ∧ EntsNormal v.dur.log) ∧
  LogIdx v.dur.log ∧
  v.delivered ++ v.ce <+: v.dur.log ∧ (v.delivered ++ v.ce).length ≤ uint.nat v.dur.commit ∧
  (∀ q ∈ v.pend, MsgMask R q) ∧ uint.Z v.dur.term ≤ uint.Z v.ps.term ∧
  (v.pre = true → v.ps.role = .follower) ∧
  (R.md.reads = false → v.ps.rd.pend = [] ∧ (v.ps.role = .leader → v.ps.rd.ro.pending = [])) ∧
  (v.pre = true → (R.k n).prevote = true)

/-- **A leader's confirmation** (for `LeaderPart`): a leader's `confirmed` is at its term and covers
its whole log. `CommitBeyondConfirmed` (B 435) reads it for a leader's commit made without a write
(`conf1` keeps `confirmed[n]` then); the win and each proposal's store set it to `{T, last}`
(`conf1`'s `stores` arm), and an accepting acknowledgement's `send` only raises its index at the
same term. -/
def LeaderConfOk (S : AntCheck.State) {N : Nat} (n : Fin N) (v : NodeView) : Prop :=
  (S.confirmed[n.val]!).term = uint.Z v.ps.term ∧ (v.r.full.length : Int) ≤ (S.confirmed[n.val]!).index

/-- **C2, a leader's part**: it is in `leaders` at its term, `ledLog` at its term is its log; every
`Match` it holds is backed by acknowledgements in `msgs`: at any index of its term within a voter's
`Match` (what `cmt`'s `Acked` quorum needs, B 252; the node's own `Match` at its win, `reset`'s
`lastIndex`, is below every entry of its term), and for another voter at the `Match` itself (what a
heartbeat's commit `min(Match, committed)` needs, through C3's `confirmed`, B 435); its
`confirmed` at its term covering its log (`LeaderConfOk`). -/
def LeaderPart (S : AntCheck.State) {N : Nat} (n : Fin N) (v : NodeView) : Prop :=
  v.ps.role = .leader →
    S.leaders.contains { server := nameOf (nodeId n), term := uint.Z v.ps.term } ∧
    S.ledLog.get (uint.Z v.ps.term) = .ok (logOf v.r.full) ∧
    (∀ (j : Fin N) (k : w64), uint.Z k ≤ uint.Z (matchOf v.ps (nodeId j)) →
      plogTermAt v.ps.base v.ps.log k = some v.ps.term →
      AckIn S (nameOf (nodeId j)) (nameOf (nodeId n)) (uint.Z v.ps.term) (uint.Z k)) ∧
    (∀ j : Fin N, j ≠ n → matchOf v.ps (nodeId j) = W64 0 ∨
      AckIn S (nameOf (nodeId j)) (nameOf (nodeId n)) (uint.Z v.ps.term)
        (uint.Z (matchOf v.ps (nodeId j)))) ∧
    LeaderConfOk S n v

/-- **C2, a candidate's part**: its tally's grants are in the binding's `Granted(n)` (R 277: the
grant facts of its term sent to it, its own vote), and its campaign's vote request is in `msgs`
(`VoteRequest(n, currentTerm[n])`, R 217-219, recorded by the campaign's `ready`, B 418: what a
`send` of one of its requests checks, B 532). -/
def CandPart (S : AntCheck.State) {N : Nat} (n : Fin N) (v : NodeView) : Prop :=
  v.ps.role = .candidate →
    (∀ j : Fin N, v.ps.votes !! nodeId j = some true → (S.granted n.val).has (nameOf (nodeId j))) ∧
    S.voteRequest n.val (S.currentTerm[n.val]!) ∈ S.msgs

/-- What raft says of a message of a `Ready` that the harness has not reported yet, at the view's
state (the `Ready`'s; `InputEnd` queues only at the state after the preamble, and the outbox was
empty at the input, C1). Each is what the binding's `Send` (B 510-593) checks: a vote request is the
campaign's (its fact recorded by the campaign's `ready`), a vote response is at the node's term (a grant for its vote), an
append or heartbeat is the leader's (`AppOk`: its commit at most the leader's, which `Sendable`
reads, not `AppSendOk`'s equal one, since an `Advance` stepping two self-messages may leave a first
batch with a stale commit; `HeartbeatOk`), an acknowledgement answers the
handled `MsgApp` (accepting: its last index, the log after the write matching it, B 571-575; stale:
the commit index, B 577-580; or a stale `MsgApp`/`MsgHeartbeat`'s empty answer at the node's term,
`StaleEnd`), a heartbeat response is at the node's term; a forwarded proposal is
unchecked (B 524, 586), from the node at term `0` (`ProposeEnd`'s forward); a pre-vote request or
response, a read-index request (local, forwarded) or response is unchecked (`isUnmodelled`, B 702)
but for its sender, and a pre-vote request is a voter's (`PreCampaignEnd`), a granted pre-vote
response answers the handled `MsgPreVote` (so that its receiver, which may campaign on it with no
promotability test, `CampaignSends`, is a voter: the binding's `Unpromotable`); a snapshot is a leader's (parity B3 states what `snapOk` needs). A heartbeat
carries no index, term or entries (`sendHeartbeat`), which the binding's `Sendable` reads (B 120-124).
An acknowledgement is of a drain caused by a `recv` (`by = "recv"`, whose `pending[n]` it reads). -/
def PendOk (N : Nat) (id : w64) (v : NodeView) (q : Msg) : Prop :=
  q.dst ≠ id ∧ (∃ j : Fin N, q.dst = nodeId j) ∧
  match q.ty with
  | .vote => q.src = id ∧ v.ps.role = .candidate ∧ q.term = v.ps.term ∧ v.ps.vote = id ∧
      q.index = (plogLast v.ps.base v.ps.log).index' ∧ q.logterm = (plogLast v.ps.base v.ps.log).term'
  | .voteResp => q.src = id ∧ q.term = v.ps.term ∧ (q.reject = false → v.ps.vote = q.dst)
  | .app => v.ps.role = .leader ∧ AppOk id v.ps q
  | .heartbeat => v.ps.role = .leader ∧ HeartbeatOk id v.ps q ∧
      q.index = W64 0 ∧ q.logterm = W64 0 ∧ q.entries = []
  | .appResp => q.src = id ∧ v.byE = go!"recv" ∧
      ((∃ m, v.cause = some m ∧ m.ty = .app ∧ q.dst = m.src ∧
        q.term = m.term ∧ q.term = v.ps.term ∧
        (q.reject = false →
          (uint.Z q.index = uint.Z m.index + m.entries.length ∧
            plogTermAt v.ps.base v.ps.log m.index = some m.logterm ∧
            ∀ (k : Nat) (e : EntryM), m.entries[k]? = some e →
              plogTermAt v.ps.base v.ps.log (m.index + W64 ((k : Int) + 1)) = some e.Term') ∨
          (uint.Z m.index < uint.Z v.ps.commit ∧ q.index = v.ps.commit))) ∨
       (∃ m, v.cause = some m ∧ (m.ty = .app ∨ m.ty = .heartbeat) ∧ q.dst = m.src ∧
        uint.Z m.term < uint.Z v.ps.term ∧
        q = Msg.mk .appResp id m.src v.ps.term false (W64 0) (W64 0) (W64 0) (W64 0) []))
  | .heartbeatResp => q.src = id ∧ q.term = v.ps.term
  | .propose => q.src = id ∧ q.term = W64 0
  | .preVote => q.src = id ∧ id ∈ v.r.cfg.cfg.voters
  | .preVoteResp => q.src = id ∧ (q.reject = false → ∃ m, v.cause = some m ∧ m.ty = .preVote ∧ q.dst = m.src)
  | .readIndex => q.src = id
  | .readIndexResp => q.src = id
  | .snap => q.src = id ∧ v.ps.role = .leader

/-- The self-addressed messages `Advance` steps (`stepsOnAdvance`): a leader's self-acknowledgement
(queued only while it leads: a node that steps down drops its outbox), its ack fact already recorded
by the `ready` of its write (B 407), a candidate's self-vote, recorded by the campaign's (B 418), or
a pre-candidate's self pre-vote at the next term (`PreCampaignEnd`, a voter's with pre-vote on: its win campaigns,
`CampaignSends`, with no promotability test; unrecorded, `isUnmodelled`), in a queue of self pre-votes only
(one `Ready`'s queue is one input's, and a pre-campaign queues only its own pre-vote). -/
def QsOk (R : RunCfg) (S : AntCheck.State) (n : Fin R.N) (v : NodeView) (q : Msg) : Prop :=
  q.src = nodeId n ∧ q.dst = nodeId n ∧ q.reject = false ∧
  ((q.term = v.ps.term ∧
    ((q.ty = .appResp ∧ v.ps.role = .leader ∧
        AckIn S (nameOf (nodeId n)) (nameOf (nodeId n)) (uint.Z v.ps.term) (uint.Z q.index)) ∨
     (q.ty = .voteResp ∧
        { voter := nameOf (nodeId n), term := uint.Z v.ps.term, cand := nameOf (nodeId n) } ∈ S.votes))) ∨
   (q.ty = .preVoteResp ∧ q.term = v.ps.term + W64 1 ∧ nodeId n ∈ v.r.cfg.cfg.voters ∧
      (R.k n).prevote = true ∧ ∀ q' ∈ v.qs, q'.ty = .preVoteResp))

/-- **C1, the leader hint**: a node that does not lead does not name itself as leader (raft's
`LeadOk`): every step that sets `lead` to the node itself makes it leader, and a leader that steps
down resets `lead` (`becomeFollower`), or sets it to the sender of a message, never itself (D:
`m.src ≠ m.dst`). And the hint is no node or one of the three (`LeadIn`): `lead` is set only to a
sender of a leader's message (a node: the network carries only theirs) or to the node itself. A
follower forwards a proposal to it (`ProposeEnd`), so a `Ready`'s forwarded proposal is to a node. -/
def LeadIn (N : Nat) (s : PState) : Prop := s.lead = W64 0 ∨ ∃ j : Fin N, s.lead = nodeId j

def LeadOk {N : Nat} (n : Fin N) (v : NodeView) : Prop :=
  (v.ps.role ≠ .leader → v.ps.lead ≠ nodeId n) ∧ LeadIn N v.ps

/-- **C1, a non-follower's vote is its own** (raft's `GhostState` fact `s.role ≠ .follower →
s.vote = id`): a campaign votes for the node itself (`TickEnd`'s `elect`), a win and a leader's
steps keep the vote, and every step that changes the vote otherwise makes the node a follower
(`voteSelf_ready`). -/
def VoteSelf {N : Nat} (n : Fin N) (v : NodeView) : Prop := v.ps.role ≠ .follower → v.ps.vote = nodeId n

/-- **A transfer message of a `Ready`** taken at the protocol state `p` (`XPendOk`; raft's
`XReadyOk`): to another server, of a term at most the node's; a `MsgTimeoutNow` the node's own;
otherwise a forwarded `MsgTransferLeader` (whose sender is the transferee). The drain keeps the
view's protocol state, so a message not yet reported keeps these facts at the view's. (A
`MsgTimeoutNow`'s transferee acknowledged at its term, design §6.4: raft's `isAcked`, `G.acks`, read
at its `send`, `XMsgFacts`.) -/
def XPendOk (N : Nat) (id : w64) (p : PState) (x : XMsg) : Prop :=
  x.dst ≠ id ∧ (∃ j : Fin N, x.dst = nodeId j) ∧ uint.Z x.term ≤ uint.Z p.term ∧
  (x.ty = .timeoutNow → x.src = id)

/-- C1, C2 and the drain's facts for node `n`: its disk, in-memory part, sync disk, announced write,
queue, reads and configuration (`DiskIs`, `MemIs`, `SyncDisk`, `UndoIs`, `QueueIs`, `ReadsIs`,
`ConfLag`), raft's side (`NodeFacts`), its pending messages (`PendOk`, `XPendOk`), its queued
self-messages (`QsOk`), once its drain's `recv` is reported, `pending[n]` (B 201), and the message
its drain handles was sent to it (an acknowledgement's `send` reads its `Sendable`, kept by C4);
the leader hint (`LeadOk`); a non-follower's vote its own (`VoteSelf`). -/
def NodeOk (R : RunCfg) (dec : CCDec) (S : AntCheck.State) (net : List Msg) (n : Fin R.N)
    (v : NodeView) : Prop :=
  DiskIs S n v ∧ MemIs R.N S n v ∧ SyncDisk R v ∧ UndoIs S n v ∧ QueueIs S n v ∧ ReadsIs S n v ∧
  ConfLag dec R v ∧ NodeFacts R n v ∧ LeaderPart S n v ∧ CandPart S n v ∧
  (∀ q ∈ v.pend, PendOk R.N (nodeId n) v q) ∧ (∀ x ∈ v.xpend, XPendOk R.N (nodeId n) v.ps x) ∧
  (∀ q ∈ v.qs, QsOk R S n v q) ∧
  (v.told = true → (∃ m, v.cause = some m ∧ S.pending[n.val]! = [msgOf m (nodeId n)]) ∨
    (∃ x, v.xcause = some x ∧ S.pending[n.val]! = [xmsgOf x])) ∧
  (∀ m, v.cause = some m → m ∈ net ∧ m.dst = nodeId n) ∧
  (∀ x, v.xcause = some x → x.dst = nodeId n ∧ v.cause = none) ∧
  LeadOk n v ∧ VoteSelf n v


/-! The conjuncts of `NodeOk` and `NodeFacts` by name. -/

theorem NodeOk.disk {R : RunCfg} {dec : CCDec} {S : AntCheck.State} {net : List Msg} {n : Fin R.N} {v : NodeView}
    (h : NodeOk R dec S net n v) :
    DiskIs S n v :=
  h.1

theorem NodeOk.mem {R : RunCfg} {dec : CCDec} {S : AntCheck.State} {net : List Msg} {n : Fin R.N} {v : NodeView}
    (h : NodeOk R dec S net n v) :
    MemIs R.N S n v :=
  h.2.1

theorem NodeOk.sync {R : RunCfg} {dec : CCDec} {S : AntCheck.State} {net : List Msg} {n : Fin R.N} {v : NodeView}
    (h : NodeOk R dec S net n v) :
    SyncDisk R v :=
  h.2.2.1

theorem NodeOk.undo {R : RunCfg} {dec : CCDec} {S : AntCheck.State} {net : List Msg} {n : Fin R.N} {v : NodeView}
    (h : NodeOk R dec S net n v) :
    UndoIs S n v :=
  h.2.2.2.1

theorem NodeOk.queue {R : RunCfg} {dec : CCDec} {S : AntCheck.State} {net : List Msg} {n : Fin R.N} {v : NodeView}
    (h : NodeOk R dec S net n v) :
    QueueIs S n v :=
  h.2.2.2.2.1

theorem NodeOk.reads {R : RunCfg} {dec : CCDec} {S : AntCheck.State} {net : List Msg} {n : Fin R.N} {v : NodeView}
    (h : NodeOk R dec S net n v) :
    ReadsIs S n v :=
  h.2.2.2.2.2.1

theorem NodeOk.confLag {R : RunCfg} {dec : CCDec} {S : AntCheck.State} {net : List Msg} {n : Fin R.N} {v : NodeView}
    (h : NodeOk R dec S net n v) :
    ConfLag dec R v :=
  h.2.2.2.2.2.2.1

theorem NodeOk.facts {R : RunCfg} {dec : CCDec} {S : AntCheck.State} {net : List Msg} {n : Fin R.N} {v : NodeView}
    (h : NodeOk R dec S net n v) :
    NodeFacts R n v :=
  h.2.2.2.2.2.2.2.1

theorem NodeOk.leader {R : RunCfg} {dec : CCDec} {S : AntCheck.State} {net : List Msg} {n : Fin R.N} {v : NodeView}
    (h : NodeOk R dec S net n v) :
    LeaderPart S n v :=
  h.2.2.2.2.2.2.2.2.1

theorem NodeOk.cand {R : RunCfg} {dec : CCDec} {S : AntCheck.State} {net : List Msg} {n : Fin R.N} {v : NodeView}
    (h : NodeOk R dec S net n v) :
    CandPart S n v :=
  h.2.2.2.2.2.2.2.2.2.1

theorem NodeOk.pend {R : RunCfg} {dec : CCDec} {S : AntCheck.State} {net : List Msg} {n : Fin R.N} {v : NodeView}
    (h : NodeOk R dec S net n v) :
    ∀ q ∈ v.pend, PendOk R.N (nodeId n) v q :=
  h.2.2.2.2.2.2.2.2.2.2.1

theorem NodeOk.xpend {R : RunCfg} {dec : CCDec} {S : AntCheck.State} {net : List Msg} {n : Fin R.N} {v : NodeView}
    (h : NodeOk R dec S net n v) :
    ∀ x ∈ v.xpend, XPendOk R.N (nodeId n) v.ps x :=
  h.2.2.2.2.2.2.2.2.2.2.2.1

theorem NodeOk.qs {R : RunCfg} {dec : CCDec} {S : AntCheck.State} {net : List Msg} {n : Fin R.N} {v : NodeView}
    (h : NodeOk R dec S net n v) :
    ∀ q ∈ v.qs, QsOk R S n v q :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem NodeOk.told {R : RunCfg} {dec : CCDec} {S : AntCheck.State} {net : List Msg} {n : Fin R.N} {v : NodeView}
    (h : NodeOk R dec S net n v) :
    v.told = true → (∃ m, v.cause = some m ∧ S.pending[n.val]! = [msgOf m (nodeId n)]) ∨
      (∃ x, v.xcause = some x ∧ S.pending[n.val]! = [xmsgOf x]) :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem NodeOk.cause {R : RunCfg} {dec : CCDec} {S : AntCheck.State} {net : List Msg} {n : Fin R.N} {v : NodeView}
    (h : NodeOk R dec S net n v) :
    ∀ m, v.cause = some m → m ∈ net ∧ m.dst = nodeId n :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem NodeOk.xcause {R : RunCfg} {dec : CCDec} {S : AntCheck.State} {net : List Msg} {n : Fin R.N} {v : NodeView}
    (h : NodeOk R dec S net n v) :
    ∀ x, v.xcause = some x → x.dst = nodeId n ∧ v.cause = none :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem NodeOk.leadOk {R : RunCfg} {dec : CCDec} {S : AntCheck.State} {net : List Msg} {n : Fin R.N} {v : NodeView}
    (h : NodeOk R dec S net n v) :
    LeadOk n v :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem NodeOk.voteSelf {R : RunCfg} {dec : CCDec} {S : AntCheck.State} {net : List Msg} {n : Fin R.N} {v : NodeView}
    (h : NodeOk R dec S net n v) :
    VoteSelf n v :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem NodeFacts.outbox {R : RunCfg} {n : Fin R.N} {v : NodeView}
    (h : NodeFacts R n v) :
    v.ps.outbox = [] :=
  h.1

theorem NodeFacts.snap0 {R : RunCfg} {n : Fin R.N} {v : NodeView}
    (h : NodeFacts R n v) :
    R.md.snapshots = false → v.ps.base = base0 ∧ v.r.fp = [] ∧ v.r.snap = false :=
  h.2.1

theorem NodeFacts.conf0 {R : RunCfg} {n : Fin R.N} {v : NodeView}
    (h : NodeFacts R n v) :
    R.md.confChanges = false →
      v.r.cfg.cfg = CfgM.simple R.voters0 ∅ ∧ EntsNormal v.r.full ∧ EntsNormal v.dur.log :=
  h.2.2.1

theorem NodeFacts.logIdx {R : RunCfg} {n : Fin R.N} {v : NodeView}
    (h : NodeFacts R n v) :
    LogIdx v.dur.log :=
  h.2.2.2.1

theorem NodeFacts.prefix {R : RunCfg} {n : Fin R.N} {v : NodeView}
    (h : NodeFacts R n v) :
    v.delivered ++ v.ce <+: v.dur.log :=
  h.2.2.2.2.1

theorem NodeFacts.len {R : RunCfg} {n : Fin R.N} {v : NodeView}
    (h : NodeFacts R n v) :
    (v.delivered ++ v.ce).length ≤ uint.nat v.dur.commit :=
  h.2.2.2.2.2.1

theorem NodeFacts.pendMask {R : RunCfg} {n : Fin R.N} {v : NodeView}
    (h : NodeFacts R n v) :
    ∀ q ∈ v.pend, MsgMask R q :=
  h.2.2.2.2.2.2.1

theorem NodeFacts.durTerm {R : RunCfg} {n : Fin R.N} {v : NodeView}
    (h : NodeFacts R n v) :
    uint.Z v.dur.term ≤ uint.Z v.ps.term :=
  h.2.2.2.2.2.2.2.1

theorem NodeFacts.preRole {R : RunCfg} {n : Fin R.N} {v : NodeView}
    (h : NodeFacts R n v) :
    v.pre = true → v.ps.role = .follower :=
  h.2.2.2.2.2.2.2.2.1

theorem NodeFacts.roPend {R : RunCfg} {n : Fin R.N} {v : NodeView}
    (h : NodeFacts R n v) :
    R.md.reads = false → v.ps.role = .leader → v.ps.rd.ro.pending = [] :=
  fun hr => (h.2.2.2.2.2.2.2.2.2.1 hr).2

theorem NodeFacts.pend0 {R : RunCfg} {n : Fin R.N} {v : NodeView}
    (h : NodeFacts R n v) : R.md.reads = false → v.ps.rd.pend = [] :=
  fun hr => (h.2.2.2.2.2.2.2.2.2.1 hr).1

theorem NodeFacts.preVote {R : RunCfg} {n : Fin R.N} {v : NodeView}
    (h : NodeFacts R n v) :
    v.pre = true → (R.k n).prevote = true :=
  h.2.2.2.2.2.2.2.2.2.2

/-! ## C3: the binding's own invariants -/

/-- **C3, the acks' terms**: every ack fact from node `i` is at most `currentTerm[i]`. Acks are
recorded only at the recorder's current term (`OnDisk`'s `t1`, B 407; a `send`'s `cm.term`, which
it checks is `currentTerm[n]`, B 571-580), and terms only grow. With `HbCommitOk`'s derivation at a
heartbeat's `send`, it makes a leader's ack fact from `j` at the leader's term be at `currentTerm[j]`
(C3's ack conjunct then applies). -/
def AckTermsOk (N : Nat) (S : AntCheck.State) : Prop :=
  ∀ n : Fin N, ∀ a ∈ S.msgs, a.type = go!"ack" → a.src = nameOf (nodeId n) →
    a.term ≤ S.currentTerm[n.val]!

/-- **C3, the vote's term**: `voteTerm[i] ≤ currentTerm[i]` (`OnDisk` sets `voteTerm` to the new
term `t1` only). So a term change that writes no vote leaves `Vote(n)` empty (`VoteOf`'s
`vt = t`, B 99), what `ready`'s `S'.vote n = []` needs. -/
def VoteTermOk (N : Nat) (S : AntCheck.State) : Prop :=
  ∀ n : Fin N, S.voteTerm[n.val]! ≤ S.currentTerm[n.val]!

/-- **C3, the confirmed records**: each `confirmed[j]` is at a term `j` has reached (`conf1` sets it at
`t1`; an accepting ack's `send` at `currentTerm[n]`, B 571-575), and either empty, at a term
`ledLog` has, or at a term every node has passed. At a win the leader's log enters `ledLog` at a
term `T` that was missing (`inMemory`'s check), and this excludes any `j` already confirmed at `T` with a
nonzero index (whose `confirmed[j]` would otherwise have to be a prefix of the new `ledLog[T]`,
C3's confirmed conjunct). `GC` removes from `ledLog` only terms every node has passed (`StaleLed`:
`Over`, `EffTerm ≤ currentTerm`, B 153, 709); a `ready` or a `send` confirms only at a term in
`ledLog` (`Sendable`, B 117-126, or the leader's own term). -/
def ConfirmedOk (N : Nat) (S : AntCheck.State) : Prop :=
  ∀ j : Fin N,
    ((S.confirmed[j.val]!).index = 0 ∨ S.ledLog.has (S.confirmed[j.val]!).term = true ∨
      ∀ i : Fin N, (S.confirmed[j.val]!).term < S.currentTerm[i.val]!) ∧
    (S.confirmed[j.val]!).term ≤ S.currentTerm[j.val]!

/-- `old` (B 346) as a value: the commit `termLen` records for term `t` (`0` if none). -/
def tlOld (tl : AntCheck.TermFn Int) (t : Int) : Int :=
  match tl.find? (fun p => p.1 == t) with
  | some p => p.2
  | none => 0

/-- **C3, the terms' recorded commits**: a term with a positive recorded commit is led (in
`leaders`) or every node has passed it (a node commits at a term only on its leader's message, or
as its leader, and `GC` drops a leader only once every node has passed its term, B 709); and a
leader's commit is what its term records once it is at an entry of the term (the leader records it
at its commit, `InMemory`'s `cmt`, B 252-258), and never below it (a follower records at most the
commit of its leader's message, C4's `LeadCommitMsgOk`). `InMemory`'s guards on a leader's commit
(`cmt`: beyond the recorded one) and a proposal (no new commit) read it. -/
def TermLenOk (N : Nat) (S : AntCheck.State) : Prop :=
  (∀ T, 0 < tlOld S.termLen T →
    (∃ l ∈ S.leaders, l.term = T) ∨ ∀ i : Fin N, T < S.currentTerm[i.val]!) ∧
  ∀ n : Fin N, S.role[n.val]! = AntCheck.leader →
    (AntCheck.termAt (S.log[n.val]!) (S.commitIndex[n.val]!) = S.currentTerm[n.val]! →
      S.commitIndex[n.val]! ≤ tlOld S.termLen (S.currentTerm[n.val]!)) ∧
    tlOld S.termLen (S.currentTerm[n.val]!) ≤ S.commitIndex[n.val]!

/-- **C3, the leader configurations**: every term with a leader log has as its leader configuration
the one the conf entries of that log's first `ledAt` entries make from the initial one (`InMemory`'s
`lc1` records `config[n]` at a win, B 260, and a leader's applied change moves it, B 627; `GC` drops a
term from `ledLog`, `ledConf` and `ledAt` together, B 717). `cmt`'s `Acked` quorum (B 252) reads
`ledConf` at the leader's term. With conf changes off the leader log has no conf entry (a
proposal's entries are normal), so that configuration is the initial one. -/
def LedConfOk (R : RunCfg) (dec : CCDec) (S : AntCheck.State) : Prop :=
  ∀ T, S.ledLog.has T = true → ∃ (l : List EntryM) (a : Nat) (cs : CCState),
    S.ledLog.get T = .ok (logOf l) ∧ S.ledAt.get T = .ok (a : Int) ∧
    cfgFold dec R.c0 (l.take a) = some cs ∧ S.ledConf.get T = .ok (confView R.N cs) ∧
    (R.md.confChanges = false → EntsNormal l)

/-- **C3, `termLen` sorted by term**: `TermFn.with` inserts a term in order (replacing its entry),
and `GC` leaves `termLen` alone; so a term's entry is the one `tlOld` finds (`tlOld_mem`). A
candidate's commit recorded under its own term is then within `tlOld` at that term, which C3's
`TermLenOk` bounds (a win's `cmt` guard, B 252). -/
def TlSorted (S : AntCheck.State) : Prop := S.termLen.Pairwise (fun a b => a.1 < b.1)

/-- **C3, the boot term**: every node's term at least `bootTerm`, every vote request's term above it.
The nodes start at `bootTerm` (`BootInit`, B 733-753) and terms only grow; a vote request is
`elect`'s, at its candidate's `currentTerm + 1`. `State.voteOf` ignores a vote at a term not above
`bootTerm`, so a vote recorded at a campaign or a grant needs its term above it. -/
def BootTermOk (N : Nat) (S : AntCheck.State) : Prop :=
  (∀ n : Fin N, S.bootTerm ≤ S.currentTerm[n.val]!) ∧
  ∀ f ∈ S.msgs, f.type = go!"vote" → S.bootTerm < f.term

/-- **C3**: facts about `S` alone, kept by every step and by `GC` (§3.2): no violation (the queue, the reads and the announced write
are per node: `QueueIs`, `ReadsIs`, `UndoIs`); `termLen` within `chain`; each node's commit within `chain`
and agreeing with it (`subSeq`'s domain, B 434, 600), recorded under a term it has reached
(`RecordedIn`, B 109-112, at a win and a request's commit); `confirmed` a prefix of its term's leader
log while that is kept; every ack of a node at its term within its `confirmed` or its commit (what
`CommitBeyondConfirmed`, B 435, needs); `ledLog`'s terms led; a node in `leaders` at its current term
only while it leads it (but `BootInit`'s leader of term 1, B 733-753, a follower at its start); the grants' and acks' senders and receivers and the votes' voters servers
(`GC` looks them up, B 699-708: an evaluation error otherwise); a node's vote at its term in
`votes` (recorded by the write that made it, B 410: what a `send` of its grant checks, B 540);
the acks' terms (`AckTermsOk`), the votes' terms (`VoteTermOk`) and the `confirmed` records'
(`ConfirmedOk`) within the nodes' terms; the terms' recorded commits (`TermLenOk`); the leader configurations (`LedConfOk`); `termLen` sorted
(`TlSorted`); the nodes' terms and the vote requests' within the boot term (`BootTermOk`). -/
def BindingOk (R : RunCfg) (dec : CCDec) (S : AntCheck.State) : Prop :=
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
      (l.term = S.currentTerm[n.val]! ∧ (S.role[n.val]! = AntCheck.leader ∨ (R.boot = true ∧ l.term = 1)))) ∧
  (∀ f ∈ S.msgs, f.type ≠ go!"vote" →
    (∃ i : Fin R.N, f.src = nameOf (nodeId i)) ∧ ∃ j : Fin R.N, f.dst = nameOf (nodeId j)) ∧
  (∀ v ∈ S.votes, ∃ i : Fin R.N, v.voter = nameOf (nodeId i)) ∧
  (∀ n : Fin R.N, S.vote n.val ≠ [] →
    { voter := nameOf (nodeId n), term := S.currentTerm[n.val]!, cand := S.vote n.val } ∈ S.votes) ∧
  AckTermsOk R.N S ∧ VoteTermOk R.N S ∧ ConfirmedOk R.N S ∧ TermLenOk R.N S ∧ LedConfOk R dec S ∧
  TlSorted S ∧ BootTermOk R.N S

theorem BindingOk.termLenOk {R : RunCfg} {dec : CCDec} {S : AntCheck.State} (h : BindingOk R dec S) :
    TermLenOk R.N S :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem BindingOk.ledConfOk {R : RunCfg} {dec : CCDec} {S : AntCheck.State} (h : BindingOk R dec S) :
    LedConfOk R dec S :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem BindingOk.tlSorted {R : RunCfg} {dec : CCDec} {S : AntCheck.State} (h : BindingOk R dec S) :
    TlSorted S :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem BindingOk.bootTermOk {R : RunCfg} {dec : CCDec} {S : AntCheck.State} (h : BindingOk R dec S) :
    BootTermOk R.N S :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

/-! ## C4: the network -/

/-- **C4, a heartbeat's commit**: a heartbeat to `j` whose term `j` has not passed carries a commit
within `j`'s confirmation at its term, or within `j`'s commit. `CommitBeyondConfirmed` (B 435) reads
it when `j` commits on the heartbeat. `GC` can drop the leader's ack from `j` once `j` moves on
(`Garbage`, B 696-706), so the fact is recorded with the message: `antSim_send` establishes it from
`HeartbeatOk` (`commit ≤ Match[j]`), `LeaderPart`'s ack at `Match[j]`, `AckTermsOk` (that ack is at
`currentTerm[j]`) and C3's ack conjunct; it is kept since `confirmed[j]` moves only to a later term
or a larger index at its term (`ConfirmedOk`'s `term ≤ currentTerm[j]`) and commits only grow. -/
def HbCommitOk (N : Nat) (S : AntCheck.State) (net : List Msg) : Prop :=
  ∀ m ∈ net, m.ty = .heartbeat → ∀ j : Fin N, m.dst = nodeId j →
    S.currentTerm[j.val]! ≤ uint.Z m.term →
    ((S.confirmed[j.val]!).term = uint.Z m.term ∧ uint.Z m.commit ≤ (S.confirmed[j.val]!).index) ∨
      uint.Z m.commit ≤ S.commitIndex[j.val]!

/-- **C4, a leader's message's commit**: an append or heartbeat from node `i` at the term `i` is at,
while `i` is not a follower, carries at most `i`'s commit (`AppOk`/`HeartbeatOk` at its `send`:
`commit` the sender's; commits only grow, and a node is a non-follower at a term only after
campaigning to it, when it had sent nothing at it). With election safety, a follower's commit on it
stays within its term's leader's commit (`TermLenOk`). -/
def LeadCommitMsgOk (N : Nat) (S : AntCheck.State) (net : List Msg) : Prop :=
  ∀ m ∈ net, (m.ty = .app ∨ m.ty = .heartbeat) → ∀ i : Fin N, m.src = nodeId i →
    S.role[i.val]! ≠ AntCheck.follower → S.currentTerm[i.val]! = uint.Z m.term →
    uint.Z m.commit ≤ S.commitIndex[i.val]!

/-- **C4, a message's shape**: an append carries a well-formed payload that does not wrap
(`AppPayloadOk`, what `RecvEnd` reads of a received `MsgApp`), no message is to its sender, and a
forwarded proposal is at term `0` (`ProposeEnd`'s forward). `send` keeps them from `PendOk`
(`AppOk`'s `AppPayloadOk` and `dst ≠ id`); with `Reach.input`'s `m.term ≠ 0`, a received message is
never a proposal. -/
def MsgShape (m : Msg) : Prop :=
  (m.ty = .app → AppPayloadOk m) ∧ m.src ≠ m.dst ∧ (m.ty = .propose → m.term = W64 0)

/-- Every message sent has `MsgShape`. -/
def NetShape (net : List Msg) : Prop := ∀ m ∈ net, MsgShape m

/-- **C4, the pre-vote messages' voters** (without conf changes): a pre-vote request is from a voter
(`PreCampaignEnd`'s guard) and a granted pre-vote response to one (it answers a request), so that a
node campaigning on one (`HandleEnd`'s `CampaignSends`, no promotability test) is promotable (the
binding's `Unpromotable`). -/
def PreVoterOk (R : RunCfg) (m : Msg) : Prop :=
  R.md.confChanges = false →
    (m.ty = .preVote → m.src ∈ R.voters0) ∧
    (m.ty = .preVoteResp → m.reject = false → m.dst ∈ R.voters0)

/-- **C4**: every message sent (`net`: every `send` so far, delivered, dropped or in flight) is
between two of the nodes, of a type in scope, of a term its sender has reached (but a pre-vote
request or a granted pre-vote response, at the next term or the request's: `PreTermKeep`, which
keeps the receiver's term), and what the
binding checks at its receipt or of its answer was recorded by its sender's reports (B 546: the
`send` of a request checked `Sendable`; B 418, 540, 573: the facts of a vote request, a grant, an
ack) and is kept while its receiver has not passed its term (GC drops only what a term has
passed, B 696-709); a heartbeat's commit within its receiver's confirmation or commit
(`HbCommitOk`); every message's shape (`NetShape`); a leader's message's commit within its own
(`LeadCommitMsgOk`); every message under the run's mask (`MsgMask`); the pre-vote messages'
voters (`PreVoterOk`). -/
def NetOk (R : RunCfg) (S : AntCheck.State) (net : List Msg) : Prop :=
  (∀ m ∈ net,
    (m.ty = .vote ∨ m.ty = .voteResp ∨ m.ty = .app ∨ m.ty = .appResp ∨ m.ty = .heartbeat ∨
      m.ty = .heartbeatResp ∨ m.ty = .propose ∨ m.ty = .preVote ∨ m.ty = .preVoteResp ∨
      m.ty = .readIndex ∨ m.ty = .readIndexResp ∨ m.ty = .snap) ∧
    (∃ i : Fin R.N, m.src = nodeId i ∧ (PreTermKeep m ∨ uint.Z m.term ≤ S.currentTerm[i.val]!)) ∧
    ∃ j : Fin R.N, m.dst = nodeId j ∧
      (S.currentTerm[j.val]! ≤ uint.Z m.term →
        ((m.ty = .app ∨ m.ty = .heartbeat) →
          (AntCheck.toAppendFact (msgOf m m.dst) >>= S.sendable) = .ok true) ∧
        (m.ty = .vote → ∃ f, AntCheck.voteFact (msgOf m m.dst) = .ok f ∧ f ∈ S.msgs) ∧
        ((m.ty = .voteResp ∧ m.reject = false) →
          ({ type := go!"grant", src := nameOf m.src, dst := nameOf m.dst, term := uint.Z m.term } :
            AntCheck.Fact) ∈ S.msgs) ∧
        ((m.ty = .appResp ∧ m.reject = false ∧ m.index ≠ W64 0) →
          AckIn S (nameOf m.src) (nameOf m.dst) (uint.Z m.term) (uint.Z m.index)))) ∧
  HbCommitOk R.N S net ∧ NetShape net ∧ LeadCommitMsgOk R.N S net ∧ (∀ m ∈ net, MsgMask R m) ∧
  ∀ m ∈ net, PreVoterOk R m

/-- **C4, the transfer messages**: every `MsgTransferLeader`/`MsgTimeoutNow` sent (`xnet`) is of a
term some server has reached (its sender's, at the send: what `OnDisk`'s `adopt` asks of a higher
term, B 371-373), and a `MsgTimeoutNow` of a term its receiver has reached (design §6.4: the
transferee acknowledged at the leader's term, so its campaign is `elect`'s `T0 + 1`, B 366). The
binding checks nothing more of them (`isUnmodelled`, B 702; a receipt checks only the receiver,
which the network routes to, B 201). -/
def XNetOk (R : RunCfg) (S : AntCheck.State) (xnet : List XMsg) : Prop :=
  ∀ x ∈ xnet, (∃ i : Fin R.N, uint.Z x.term ≤ S.currentTerm[i.val]!) ∧
    (x.ty = .timeoutNow → ∀ j : Fin R.N, x.dst = nodeId j → uint.Z x.term ≤ S.currentTerm[j.val]!)

set_option linter.iris.dupNamespace false in
/-- **The refinement relation** (§3.3: C1-C4), over the run's `N` servers. -/
def AntSim (R : RunCfg) (dec : CCDec) (S : AntCheck.State) (V : Fin R.N → NodeView)
    (net : List Msg) (xnet : List XMsg) : Prop :=
  Shape R S ∧ BindingOk R dec S ∧ NetOk R S net ∧ XNetOk R S xnet ∧ ∀ n, NodeOk R dec S net n (V n)

/-! ## C5: raft's global facts -/

/-- Raft's global facts, as pure data (the persistent ghost facts the harness's invariant keeps for
everything in `S`, §3.4): leaders (`isLeader γ j t`), votes (`isVote γ v t c`), certified logs
(`logRecs`, full logs from `base0`), each leader's log at its win (`isCamp`), the longest committed
log known (`isCommitted`), and the commits recorded in a term (`commitIn γ committed c x`: the first
`c` entries are committed by term `x`). -/
structure RaftFacts where
  leaders : List (w64 × w64)
  votes : List (w64 × w64 × w64)
  logs : List (List EntryM)
  camps : List (w64 × List EntryM)
  committed : List EntryM
  commits : List (w64 × Nat)
  /-- parity B3: the committed prefixes snapshots stand for (`raftSnapCert`), with their lengths -/
  snaps : List (Nat × List EntryM) := []
  /-- parity B3: the configuration fold's admissible pairs (`Adm`: a full log prefix, the
  configuration it makes) -/
  confs : List (List EntryM × CCState) := []
  /-- (parity B1) the acknowledgements raft certifies (`isAcked`): node `a.1` acknowledged at term
  `a.2.1` up to index `a.2.2` -/
  acks : List (w64 × w64 × w64) := []

/-- **A campaign log's terms are below its term** (raft's `isCamp γ c T F`, the log when the node
became a candidate at `T`, carries `CampOk T F`: every entry of an earlier term). With it a win's
log `l0 ++ [entry at T]` has `l0` the campaign log, and a candidate's commit is at no entry of its
term. -/
def CampTermsOk (G : RaftFacts) : Prop :=
  ∀ p ∈ G.camps, ∀ e ∈ p.2, uint.Z e.Term' < uint.Z p.1

/-- What raft proves of its global facts (election safety `isLeader_unique`, one vote per term
`isVote_agree`, log matching `logRecs_agree`, leader completeness `commitIn_camp`, a campaign log's
terms below its term `CampTermsOk`): the laws a
`RaftFacts` the harness builds satisfies. -/
def RaftLaws (G : RaftFacts) : Prop :=
  (∀ a ∈ G.leaders, ∀ b ∈ G.leaders, a.2 = b.2 → a.1 = b.1) ∧
  (∀ a ∈ G.votes, ∀ b ∈ G.votes, a.1 = b.1 → a.2.1 = b.2.1 → a.2.2 = b.2.2) ∧
  (∀ a ∈ G.logs, ∀ b ∈ G.logs, ∀ (k : Nat) (e f : EntryM), a[k]? = some e → b[k]? = some f →
    e.Term' = f.Term' → a.take (k + 1) = b.take (k + 1)) ∧
  G.committed ∈ G.logs ∧
  (∀ p ∈ G.camps, p.2 ∈ G.logs) ∧
  (∀ x ∈ G.commits, x.2 ≤ G.committed.length ∧
    ∀ p ∈ G.camps, uint.Z x.1 < uint.Z p.1 → G.committed.take x.2 <+: p.2) ∧
  CampTermsOk G

/-- The raft facts a bootstrapped run starts with and keeps (`BootInit`, B 733-753): the boot log
certified and, bootstrapped, no raft leader of term `1` (raft's campaigns are past the boot term:
`isCampK`'s `reBoot ≠ [] → 2 ≤ T`; the binding's leader of term `1`, node 1, is its own record, which
`GlobalOk` exempts). -/
def BootFacts (R : RunCfg) (G : RaftFacts) : Prop :=
  bootLog R ∈ G.logs ∧ (R.boot = true → ∀ j t, (j, t) ∈ G.leaders → 2 ≤ uint.Z t)

/-- **C5, `GlobalOk`**: everything `S` and `net` hold is certified by `G` -- its leaders and votes
are raft's, its logs (`log[·]`, `ledLog[·]`, each starting with its term's campaign log) certified,
`chain` a committed prefix, each `termLen` a commit recorded in its term, each append's entries a
slice of a certified log; bootstrapped, the binding's own boot record (node 1 the leader of term
`1`, the boot log its leader log, `BootInit`, B 733-753) is exempt; `BootFacts`; every acknowledgement raft certifies at a term its node has reached (sent
after its write, sync). With
`RaftLaws G`: `ElectionSafety`, `OneVotePerTerm` (R 581-586), any two logs `Matching` (B 132), and
leader completeness for the terms after a commit's. -/
def GlobalOk (R : RunCfg) (S : AntCheck.State) (net : List Msg) (G : RaftFacts) : Prop :=
  (∀ l ∈ S.leaders, (R.boot = true ∧ l.server = nameOf (W64 1) ∧ l.term = 1) ∨
    ∃ j t, (j, t) ∈ G.leaders ∧ l.server = nameOf j ∧ l.term = uint.Z t) ∧
  (∀ v ∈ S.votes, ∃ a t c, (a, t, c) ∈ G.votes ∧
    v.voter = nameOf a ∧ v.term = uint.Z t ∧ v.cand = nameOf c) ∧
  (∀ n : Fin R.N, ∃ l ∈ G.logs, S.log[n.val]! = logOf l) ∧
  (∀ p ∈ S.ledLog, (R.boot = true ∧ p = (1, logOf (bootLog R))) ∨ ∃ l ∈ G.logs, p.2 = logOf l ∧
    ∃ t l0, uint.Z t = p.1 ∧ (t, l0) ∈ G.camps ∧ l0 <+: l) ∧
  (∃ c ≤ G.committed.length, S.chain = logOf (G.committed.take c)) ∧
  (∀ p ∈ S.termLen, 0 ≤ p.2 ∧ ∃ x, uint.Z x = p.1 ∧ (x, p.2.toNat) ∈ G.commits) ∧
  (∀ m ∈ net, m.ty = .app →
    ∃ l ∈ G.logs, (l.drop (uint.nat m.index)).take m.entries.length = m.entries) ∧
  BootFacts R G ∧
  (∀ a ∈ G.acks, uint.Z a.2.2 ≠ 0 → ∀ j : Fin R.N, a.1 = nodeId j → uint.Z a.2.1 ≤ S.currentTerm[j.val]!)

/-- The raft facts a `ready` report needs of the node's new state `r` (at node `id`), already in
`G` (the harness adds them from `rawNode`'s laws before the report, §3.4): its full log certified,
its committed prefix the committed log's, its commit recorded in its term, its leadership raft's
with its campaign log, its vote raft's. -/
def ReadyFacts (G : RaftFacts) (id : w64) (r : RState) : Prop :=
  r.full ∈ G.logs ∧ uint.nat r.p.commit ≤ G.committed.length ∧
  r.full.take (uint.nat r.p.commit) = G.committed.take (uint.nat r.p.commit) ∧
  (r.p.term, uint.nat r.p.commit) ∈ G.commits ∧
  (r.p.role = .leader → (id, r.p.term) ∈ G.leaders ∧ ∃ l0, (r.p.term, l0) ∈ G.camps ∧ l0 <+: r.full) ∧
  (r.p.vote ≠ W64 0 → (id, r.p.term, r.p.vote) ∈ G.votes)

/-- The raft facts a `send` report needs of its message (`isMessage`'s): an append's entries a slice
of a certified log, a grant raft's vote. -/
def MsgFacts (G : RaftFacts) (q : Msg) : Prop :=
  (q.ty = .app → ∃ l ∈ G.logs, (l.drop (uint.nat q.index)).take q.entries.length = q.entries) ∧
  ((q.ty = .voteResp ∧ q.reject = false) → (q.src, q.term, q.dst) ∈ G.votes)

/-! ## The statements' frame -/

/-- What every statement assumes (§3.3): the checker's prefix at `S`, the relation, raft's laws, and
`S`, `net` certified by `G`. -/
def SimPre (R : RunCfg) (dec : CCDec) (S : AntCheck.State) (V : Fin R.N → NodeView) (net : List Msg)
    (xnet : List XMsg) (evs : List AntCheck.Event) (G : RaftFacts) : Prop :=
  Prefix R.cfg evs S ∧ AntSim R dec S V net xnet ∧ RaftLaws G ∧ GlobalOk R S net G

/-- What every report's statement concludes (§3.3): the checker takes `ev` (with the `GC` steps due
before it) to a state related to the new views and networks, certified by `G`. -/
def SimStep (R : RunCfg) (dec : CCDec) (evs : List AntCheck.Event) (G : RaftFacts)
    (ev : AntCheck.Event) (V' : Fin R.N → NodeView) (net' : List Msg) (xnet' : List XMsg) : Prop :=
  ∃ S', Prefix R.cfg (evs ++ [ev]) S' ∧ AntSim R dec S' V' net' xnet' ∧ GlobalOk R S' net' G

end rel

end AntSim
end EtcdGrove
end Perennial
