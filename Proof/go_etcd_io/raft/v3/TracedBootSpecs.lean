/-
Lean-first (no Rocq counterpart). **Step 5 of the trace-check design (2026-11-12): the traced
constructors' statements** (`notes/trace-check-design.md`, "Step 5 (2026-11-12): the constructors'
statements"; `notes/decisions.md`, "Step 5: the traced constructors"). Raft-internal (not on
`etc/api/raft.txt`). Statements only: nothing here is proved (the laws are stated as `abbrev ….statement
: Prop`), nothing imports this file yet.

Every statement is **one statement for both modes** ("Modes generalize, no twins",
`notes/spec-first-plan.md`): today's spec with its untraced premise (`TraceLoggerOk cv.TraceLogger'`,
`γ.reTrace = none`, `s.gh.tr = none`) replaced by gated content that is vacuous (`emp`, `True`, the nil
logger) at an untraced node. At proof time each `X.gatedSpec` below replaces `X.spec` in its `Spec/`
file in place (its callers are all raft-internal, counted in the design section); where a caller outside
the constructors still names today's statement, today's survives as a derived theorem (`applyConfChange`).

1. **The vocabulary** (`bootPhase`, `bootAt`, `bootNone`, `bootCfg`, `BootFresh`): the bootstrap's
   phase (the capability's share is the voter's bootstrap server, nothing pending, the voters `vs`),
   the last bootstrap event at position `k` (`BootEvAt`, A7), the voters' configuration, and a fresh
   node (what the bootstrap lines 0-2 need of `newRaft`'s inputs).
2. **`trCapStart`**: the capability before the `raft` struct exists (`trCapB` without the struct's
   `traceLogger` field, keyed by the `Config`'s logger instead): what `StartNode` makes of `startTrace`
   and `nodeBoot`, and `newRaft` turns into `trCapB` once it has written the field
   (`trCapStart_trCapB`). **`trNoCut`**: the storage never compacted past `1` at a traced node (the
   storage-level form of `TrNoSnap`, which reads the log state); `StartNode` makes it from the client's
   contract (`isStorage`'s gated `storBnd`) inside the `InitialState` answer, the only place the
   contract exists; `Bootstrap` turns it into `TrNoSnap` at the fresh log (`trNoCut_trNoSnap`).
   **`bootDoneG`**: A8.3's completion witness at raft's level (`startDoneB`'s body over a trace mode).
3. **`rawNodeAtT`, `rawNodeFreshT`**: `rawNodeAt`/`rawNodeFresh` (`InvBoot.lean`) with the node's trace
   mode free (`s.gh = { sn := s.gh.sn, tr := s.gh.tr }`, was `{ sn := s.gh.sn }`) and the `raft` struct's
   pointer `r` a parameter (`rnv.raft' = r`), so that the capability, which is keyed by `r`, can be
   stated beside them. They replace the two definitions in place at proof time (the old ones are the
   instances at `s.gh.tr = none`, `r` existential).
4. **`raft.switchToConfig.gatedSpec`, `raft.applyConfChange.gatedSpec`**: the hook in **gate form**, as
   `raft.becomeFollower.spec` has it since slice 3: the caller hands in the `ApplyConfChange` line's gate
   (`TraceFire`/`HookGate` for `CCEvOf id s c0 c`) and gets its `Q` back; the traced premise is only
   `s.role = .follower` (a follower's `switchToConfig` neither commits nor broadcasts, so its one line is
   the hook's). Today's capability form (step 4's `hCC`: a booted follower keeping its configuration) is
   the instance at `trCapB_hookGate_applyCC`'s gate (`raft.applyConfChange.tracedSpec_of_gatedSpec`, to
   write); `Bootstrap`'s per-peer call is the instance at `trCapB_hookGate_ccBoot`'s (unbooted, raft's
   configuration growing towards the capability's). **Why**: the step-4 statements cannot serve
   `Bootstrap`: they require `b = true`, `c'.cfg = c` and the capability at raft's own configuration,
   while during the bootstrap the flag is unset, each `AddNode` grows raft's configuration and the
   capability is at the voters' (`bootCfg`), apart from raft's (A1).
5. **`newRaft.gatedSpec`** (positions 0-2), **`NewRawNode.gatedSpec`**, **`RawNode.Bootstrap.gatedSpec`**
   (positions 3 to `|vs| + 3`, then the minting of `bootDone` by `trCapB_bootDone` and the packing of
   `rnTrace` inside `ownRawNode`), **`setupNode.gatedSpec`**.
6. **`startTraceF`, `StartNode.gatedSpecF`**: the Draft's `startTrace`/`StartNode.gatedSpec`
   (`TracedApiDraft.lean`) with the receipts' fit in `startTrace`'s traced branch (review
   `step4-r1.md`'s S1: `readyFits γ N` and `2 ≤ vs.length`, for `node.run.gatedSpec`'s `RunTracedOk`);
   they replace the Draft's in place at proof time, with `TracedNodeApi.lean`'s `startTraceC` (hence
   `HarnessOpen`) changed the same way. The laws `startTraceF_trCapStart` and `isStorage_trNoCut` are
   what `StartNode`'s proof needs of the cluster-level predicates.

**The intended theorems** (to be proved, not stated here):

    theorem raft.switchToConfig.wp_proof … : raft.switchToConfig.gatedSpec   -- replaces the Spec in place
    theorem raft.applyConfChange.wp_proof … : raft.applyConfChange.gatedSpec -- the one proof
    theorem raft.applyConfChange.spec_of_gatedSpec : gatedSpec → raft.applyConfChange.spec   -- untraced callers
    theorem raft.applyConfChange.tracedSpec_of_gatedSpec : gatedSpec → raft.applyConfChange.tracedSpec -- run's confc
    theorem newRaft.wp_proof … : newRaft.gatedSpec
    theorem NewRawNode.wp_proof (wp_newRaft : newRaft.gatedSpec) … : NewRawNode.gatedSpec
    theorem RawNode.Bootstrap.wp_proof (… wp_raft_applyConfChange : raft.applyConfChange.gatedSpec …) :
      RawNode.Bootstrap.gatedSpec
    theorem setupNode.wp_proof (wp_NewRawNode : NewRawNode.gatedSpec)
      (wp_RawNode_Bootstrap : RawNode.Bootstrap.gatedSpec) (wp_newNode : newNode.spec) : setupNode.gatedSpec
    theorem StartNode.gatedSpecF_of (wp_setupNode : setupNode.gatedSpec)
      (wp_node_run : node.run.gatedSpec) : StartNode.gatedSpecF
    theorem StartNode.spec_of_gatedSpecF : StartNode.gatedSpecF → StartNode.spec   -- the server's
    theorem RestartNode.wp_proof (wp_NewRawNode : NewRawNode.gatedSpec) … : RestartNode.spec  -- unchanged spec
-/
module

public import Spec.go_etcd_io.raft.v3.newRaft
public import Spec.go_etcd_io.raft.v3.NewRawNode
public import Spec.go_etcd_io.raft.v3.RawNode__Bootstrap
public import Spec.go_etcd_io.raft.v3.setupNode
public import Spec.go_etcd_io.raft.v3.raft__switchToConfig
public import Spec.go_etcd_io.raft.v3.raft__applyConfChange
public import Proof.go_etcd_io.raft.v3.TraceFits
public import Proof.go_etcd_io.raft.v3.TracedNodeBoot
public import Proof.go_etcd_io.raft.v3.TracedApiDraft
public import Proof.go_etcd_io.raft.v3.TracedSend
public import Proof.go_etcd_io.raft.v3.RaftReadLend

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3 TraceSim

/-! ## 1. The bootstrap's vocabulary (pure) -/

section vocab
variable [GooseExts]

/-- **The bootstrap's phase** (the capability's `Φ` from `StartNode` to the end of `Bootstrap`): the
voters are `vs`, the node's share is its bootstrap server (`simInit vs`'s, `startTrace`'s) with nothing
pending. The bootstrap lines keep the share (`trCap_fire_boot`), so the phase holds throughout; at the end
`simIdle_boot` turns it into `SimIdle C s` (the phase `rnTrace` holds). It fixes `C = vs`, which the
bootstrap gates' `BootNext C id o e` and `trCapB_bootDone`'s `hΛ` need. -/
def bootPhase (vs : List w64) (id : w64) : List w64 → ServerC → List Etcdraft.Msg → Prop :=
  fun C cs P => C = vs ∧ cs = toC (confAbs vs) ((simInit vs).s (idAbs id)) ∧ P = []

/-- **The node's last event is its bootstrap event at position `k`** (the capability's `Λ` between the
bootstrap lines: `BootEvAt`, A7; §5.1's table). -/
def bootAt (vs : List w64) (id : w64) (k : Nat) : Option TraceEv → Prop :=
  fun o => ∃ x, o = some x ∧ BootEvAt vs id k x

/-- **No event yet** (the capability's `Λ` at `StartNode`: `startTrace`'s `simBoot … false none`). -/
def bootNone : Option TraceEv → Prop := fun o => o = none

/-- **The voters' configuration** (`cC` of §5.2): what the capability is stated at during the bootstrap,
apart from raft's own (empty at positions 0-2, growing at positions `k + 4`); `Bootstrap`'s result's
(`cfgState (GMap.listToSet ps) ∅`). -/
def bootCfg (vs : List w64) : CfgM := (cfgState (GMap.listToSet vs) ∅).cfg

/-- **A fresh node** (`newRaft`'s traced scope): an empty storage (no hard state, the base `⟨0, 0⟩`, no
entry), nothing applied, the empty conf state. Then `traceInitState` logs term `0`, vote `0`, commit `0`,
log size `0` (position 0), `switchToConfig` the empty configuration (position 1) and `becomeFollower`
term `0` (position 2). `setupNode`'s premises imply it (`StartNode`'s storage, `restartStorage` of the
empty contents). -/
def BootFresh (cv : Config) (σ : StorState) (hs : HardStateM) (csm : ConfStateM) : Prop :=
  HsEmpty hs ∧ σ.prev = entryID.mk (W64 0) (W64 0) ∧ σ.ents = [] ∧ cv.Applied' = W64 0 ∧
  csm.Voters' = [] ∧ csm.VotersOutgoing' = [] ∧ csm.Learners' = [] ∧ csm.LearnersNext' = [] ∧
  csm.AutoLeave' = false

end vocab

/-! ## 2. The capability before the struct, the storage's no-compaction, the completion witness -/

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **The capability before the `raft` struct exists** (`newRaft`'s precondition): at an untraced node,
the nil logger (today's `TraceLoggerOk cv.TraceLogger'` premise); at a traced one, `trCapB`'s body
(`TracedCap.lean`) unbooted, with the logger `tl` (the `Config`'s `TraceLogger`) in place of the struct's
`traceLogger` field, which `newRaft` writes from it. `trCapB_intro`'s premises, bundled. -/
def trCapStart (tr : Option GName) (γ : RaftNames) (id : w64) (tl : GoInterface) (c : CfgM)
    (Φ : List w64 → ServerC → List Etcdraft.Msg → Prop) (Λ : Option TraceEv → Prop) : IProp GF :=
  match tr with
  | none => iprop(⌜TraceLoggerOk tl⌝)
  | some γd => iprop(∃ (tn : TraceNames) (C : List w64) (cs : ServerC) (P : List Etcdraft.Msg)
      (o : Option TraceEv),
      traceDir γd tn ∗ ⌜tn.voters = C ∧ (elements c.incoming).Perm C ∧ c.outgoing = ∅ ∧ id ∈ C ∧
        C.length ≤ γ.reBoot.length⌝ ∗
      isTraceLogger tn.tr tl ∗ ⌜tl ≠ interface.nil⌝ ∗ inv (simNS γ) (simInv C tn (simFx γ C)) ∗
      raftLogInv γ ∗ simNode tn id cs P ∗ simBoot tn id false o ∗ ⌜Λ o⌝ ∗ ⌜Φ C cs P⌝)

/-- **The storage is never compacted past `1` at a traced node** (persistent; the storage-level form of
`TrNoSnap`, `TracedSend.lean`, which reads it off a log state's `storage` and `prev`). Its source is the
client's storage contract at a traced cluster (`isStorage`'s `#Hbound` and the gated `storBnd`, traced
`⌜c = 0⌝`: `isStorage_trNoCut`), which exists only from `InitialState`'s answer on; so the boot bundle's
`InitialState` continuation returns it, and `newRaft`/`NewRawNode` hand it on to `Bootstrap`, which packs
`TrNoSnap` at the fresh log (`prev.index = 0`). Untraced it says nothing (`trNoCut_none`). -/
def trNoCut (tr : Option GName) (st : Storage) : IProp GF :=
  iprop(□ (⌜tr ≠ none⌝ -∗ storPast st 1 -∗ |={⊤}=> False))

/-- **A voter's completion witness at raft's level** (amendment A8.3's `startDoneB`, over the node's
trace mode): nothing untraced; traced, `bootDone` at the trace's names. `Bootstrap` returns it (minted by
`trCapB_bootDone` at its last line, while the capability's `Λ` still records it). -/
def bootDoneG (tr : Option GName) (id : w64) : IProp GF :=
  match tr with
  | none => iprop(True)
  | some γd => iprop(∃ tn : TraceNames, traceDir γd tn ∗ bootDone tn id)

/-! ## 3. The open `RawNode` with its trace mode free and the struct's pointer named -/

/-- **`rawNodeAt`, both modes** (`InvBoot.lean`; replaces it in place at proof time): word for word but
`"%Hgh"` (the trace mode free: `s.gh = { sn := s.gh.sn, tr := s.gh.tr }`, was `{ sn := s.gh.sn }`) and
`"%Hr"` (the `raft` struct is `r`, so that `NewRawNode`'s post can state the capability, keyed by `r`,
beside it). -/
def rawNodeAtT (rn r : Loc) (id : w64) (si : GoInterfaceOk) (cs : CCState) (sdr : Bool) (pre : Bool)
    (hs : HardStateM) (σ : StorState) (A : w64) (s : NState) : IProp GF :=
  iprop(∃ (rnv : RawNode) (sv : SoftState) (hprev : HardStateM),
    "Hrn" ∷ rawNodeOwn rn rnv ∗
    "%Hr" ∷ ⌜rnv.raft' = r⌝ ∗
    "Hphys" ∷ ownRaftPhysC cs.cfg rnv.raft' id s ∗
    "%Hasync" ∷ ⌜rnv.asyncStorageWrites' = false⌝ ∗
    "#Hsoft" ∷ rnv.prevSoftSt' ↦□ sv ∗
    "#Hhard" ∷ hsRO rnv.prevHardSt' hprev ∗
    "Hsteps" ∷ rnv.stepsOnAdvance' ↦* ([] : List Loc) ∗
    "Hsteps_cap" ∷ ownSliceCap Loc rnv.stepsOnAdvance' (DFrac.own 1) ∗
    "%Hrel" ∷ ⌜NStateRel s (restartPState hs σ)⌝ ∗
    "%Hterm" ∷ ⌜s.term = hs.Term' ∧ s.vote = hs.Vote' ∧ s.role = .follower ∧ s.outbox = [] ∧
      s.rd.states = [] ∧ s.rd.pend = []⌝ ∗
    "%Hlog" ∷ ⌜s.logst.prev = σ.prev ∧ s.logst.sents = σ.ents ∧
      s.logst.uents = [] ∧ s.logst.stored = σ.ents ∧ s.logst.committed = committedAfter σ.prev hs ∧
      s.logst.applied = s.logst.applying ∧
      s.logst.applying = w64Max σ.prev.index' (if A = W64 0 then σ.prev.index' else A) ∧
      s.logst.unpersisted = [] ∧ s.logst.snap = none ∧ s.logst.storage = interface.ok si ∧
      s.logst.dtk = uint.nat (committedAfter σ.prev hs)⌝ ∗
    "%Hgh" ∷ ⌜s.gh = { sn := s.gh.sn, tr := s.gh.tr }⌝ ∗
    "%Hpvoff" ∷ ⌜s.prevote = pre⌝ ∗
    "%Hsdr" ∷ ⌜s.sdr = sdr⌝ ∗
    "%Hdom" ∷ ⌜domSet s.progress = domSet cs.prs⌝ ∗
    "%Hhz" ∷ ⌜hprev = HardStateM.mk hs.Term' hs.Vote' (committedAfter σ.prev hs)⌝ ∗
    "%Hsvr" ∷ ⌜sv.RaftState' = W64 0 ∧
      uint.Z s.logst.inprogress = uint.Z σ.prev.index' + (σ.ents.length : Int) + 1⌝)

/-- **`rawNodeFresh`, both modes** (`InvBoot.lean`; replaces it in place at proof time): word for word
but `"%Hgh"` and `"%Hr"`, as `rawNodeAtT`. `Bootstrap` takes it; `rawNodeAt_fresh` carries over. -/
def rawNodeFreshT (rn r : Loc) (id : w64) (si : GoInterfaceOk) (V : GSet w64) (sdr : Bool)
    (pre : Bool) (s : NState) : IProp GF :=
  iprop(∃ (rnv : RawNode) (sv : SoftState) (hprev : HardStateM),
    "Hrn" ∷ rawNodeOwn rn rnv ∗
    "%Hr" ∷ ⌜rnv.raft' = r⌝ ∗
    "Hphys" ∷ ownRaftPhys V rnv.raft' id s ∗
    "%Hasync" ∷ ⌜rnv.asyncStorageWrites' = false⌝ ∗
    "#Hsoft" ∷ rnv.prevSoftSt' ↦□ sv ∗
    "#Hhard" ∷ hsRO rnv.prevHardSt' hprev ∗
    "Hsteps" ∷ rnv.stepsOnAdvance' ↦* ([] : List Loc) ∗
    "Hsteps_cap" ∷ ownSliceCap Loc rnv.stepsOnAdvance' (DFrac.own 1) ∗
    "%Hrel" ∷ ⌜NStateRel s initPState⌝ ∗
    "%Hterm0" ∷ ⌜s.term = W64 0 ∧ s.vote = W64 0 ∧ s.role = .follower ∧ s.outbox = [] ∧
      s.rd.states = [] ∧ s.rd.pend = []⌝ ∗
    "%Hlog" ∷ ⌜s.logst.prev = entryID.mk (W64 0) (W64 0) ∧ s.logst.sents = [] ∧
      s.logst.uents = [] ∧ s.logst.stored = [] ∧ s.logst.committed = W64 0 ∧
      s.logst.applied = W64 0 ∧ s.logst.applying = W64 0 ∧ s.logst.unpersisted = [] ∧
      s.logst.snap = none ∧ s.logst.storage = interface.ok si ∧ s.logst.dtk = 0⌝ ∗
    "%Hgh" ∷ ⌜s.gh = { sn := s.gh.sn, tr := s.gh.tr }⌝ ∗
    "%Hpvoff" ∷ ⌜s.prevote = pre⌝ ∗
    "%Hsdr" ∷ ⌜s.sdr = sdr⌝ ∗
    "%Hdom" ∷ ⌜domSet s.progress = V⌝ ∗
    "%Hhz" ∷ ⌜hprev = hsZero⌝ ∗
    "%Hsvr" ∷ ⌜sv.RaftState' = W64 0 ∧ s.logst.inprogress = W64 1⌝)

end defs

/-! ## 2'. The laws the constructors' proofs need (statements; the prover proves them) -/

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **The capability from its start and the struct's logger field** (`newRaft`, after `r := &raft{…,
traceLogger: c.TraceLogger}`): untraced the nil logger; traced `trCapB_intro`. -/
abbrev trCapStart_trCapB.statement : Prop :=
  ∀ (tr : Option GName) (γ : RaftNames) (r : Loc) (id : w64) (tl : GoInterface) (c : CfgM)
    (Φ : List w64 → ServerC → List Etcdraft.Msg → Prop) (Λ : Option TraceEv → Prop),
  (r.[raft, go!"traceLogger"] ↦□ tl ∗ trCapStart tr γ id tl c Φ Λ : IProp GF) ⊢
    ⌜tr = none → TraceLoggerOk tl⌝ ∗ trCapB tr γ r id c false Φ Λ

/-- **`TrNoSnap` at a log state of base `0`** over the storage's `trNoCut` (`Bootstrap`'s packing of
`rnTrace`: the fresh log's `prev.index = 0` refutes the first disjunct, `trNoCut` the second). -/
abbrev trNoCut_trNoSnap.statement : Prop :=
  ∀ (tr : Option GName) (ls : LogState), uint.Z ls.prev.index' = 0 →
  (trNoCut tr ls.storage : IProp GF) ⊢ TrNoSnap tr ls

/-- Untraced, `trNoCut` is free (`RestartNode`'s and the untraced `StartNode`'s `InitialState` answers). -/
abbrev trNoCut_none.statement : Prop :=
  ∀ (st : Storage), ⊢ (trNoCut none st : IProp GF)

/-- **The storage's no-compaction from the client's contract** (`StartNode`'s traced `InitialState`
answer, before `storBnd_raftBnd` converts the contract to raft's `raftBnd`): `#Hbound` at `c ≥ 1` gives
`storBnd γ K c`, whose traced arm is `⌜c = 0⌝` (`notes/decisions.md`, "Trace-check small items"). -/
abbrev isStorage_trNoCut.statement : Prop :=
  ∀ (γ : Cluster) (K : GName) (st : Storage),
  (isStorage γ K st : IProp GF) ⊢ trNoCut (Cluster.raftNames γ).reTrace st

end laws

/-! ## 4. `switchToConfig` and `applyConfChange` in gate form -/

section hooks
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **`r.switchToConfig(cfg, trk)` in both modes, the hook's gate the caller's** (replaces
`raft.switchToConfig.spec` in place; `raft.becomeFollower.spec`'s form): today's statement (step 4,
`hCC`) with its traced premise reduced to `s.role = .follower` (a follower neither commits nor
broadcasts, so the hook's is the one line) and its capability in/out (`trCapB … c0 true (SimIdle · s)`,
`… c true (SimIdle · s')`) replaced by the `ApplyConfChange` line's fire (`TraceFire s.gh.tr tl (CCEvOf
id s c0 c) Q`, which untraced is the nil logger and `Q`) and `Q` back; the old configuration's size bound
(`CfgSizeOk c0`, for `ownRaftReadT c0`, which the hook reads) joins its maps in the traced loan, since
`c0` is no longer `c`. The binder `γ` is gone. Instances: step 4's (`trCapB_hookGate_applyCC`, `c = c0`,
booted, `Q` the capability at `s`, then `simIdle_congr` through `SwitchOkC`'s follower arm) and the
bootstrap's (`trCapB_hookGate_ccBoot`, unbooted, `c0 ⊂ c`). -/
abbrev raft.switchToConfig.gatedSpec : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState) (tv0 : tracker.ProgressTracker)
    (cfgv : tracker.Config) (prsm : Loc) (prs : GMap w64 Loc) (pvs : GMap w64 Progress)
    (tl : GoInterface) (c0 : CfgM) (Q : IProp GF),
  (s.role = .leader → id ∈ c.voters → MatchKept s.prvals pvs) →
  (s.role = .leader → s.term ≠ W64 0) →
  (s.role = .candidate ∨ s.role = .preCandidate → id ∈ c.voters) →
  (s.role = .leader → ∀ v p, pvs !! v = some p → PrOkN s.gh.ns s.logst p) →
  -- (step 5) in place of step 4's traced premise: at a traced node, a follower
  (s.gh.tr ≠ none → s.role = .follower) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Htrkf" ∷ r.[raft, go!"trk"] ↦ tv0 ∗
      "Hcore" ∷ ownRaftCore r id s ∗
      "Hback" ∷ (∀ tv' prs' pvs', ownRaftCore r id s -∗ r.[raft, go!"trk"] ↦ tv' -∗
           ownTrackerC c tv' ⟨s.votes, prs', pvs'⟩ -∗
           ⌜PrvalsOk { s with progress := prs', prvals := pvs' }⌝ -∗
           ownRaftPhysCV c (c.voters ∪ {[id]}) r id { s with progress := prs', prvals := pvs' }) ∗
      "Hvotes" ∷ tv0.Votes' ↦$ s.votes ∗
      "%Hmi" ∷ ⌜0 ≤ sint.Z tv0.MaxInflight' ∧ sint.Z tv0.MaxInflight' < 2 ^ 62⌝ ∗
      "Hnew" ∷ ownConfigC c cfgv prsm prs pvs ∗
      "#Htl" ∷ r.[raft, go!"traceLogger"] ↦□ tl ∗
      -- traced, the old configuration's maps and size, which the hook reads (`ownRaftReadT c0`)
      "Hold" ∷ trOwn s.gh.tr iprop(ownCfgCC tv0.Config' (DFrac.own 1) c0 ∗ ⌜CfgSizeOk c0⌝) ∗
      -- (step 5) the `ApplyConfChange` line's fire, the caller's (untraced: the nil logger and `Q`)
      "Hfire" ∷ TraceFire s.gh.tr tl (CCEvOf id s c0 c) Q }}
    (App (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"switchToConfig"))
      (Val #cfgv)) (Val #prsm))
  {{ (cs : Loc) (xs os ls lns : List w64) (s' : NState), RET #cs;
      ownRaftPhysCV c c.voters r id s' ∗
      csPts cs (DFrac.own 1) (ConfStateM.mk xs ls os lns c.autoLeave) true ∗
      ⌜xs ≡ₚ elements c.incoming ∧ os ≡ₚ elements c.outgoing ∧ ls ≡ₚ elements c.learners ∧
        lns ≡ₚ elements c.learnersNext⌝ ∗
      ⌜SwitchOkC c id { s with progress := prs, prvals := pvs, isLearner := learnerOfC c id }
        s'⌝ ∗
      Q }}

/-- **`r.applyConfChange(cc)` in both modes, the hook's gate the caller's** (replaces
`raft.applyConfChange.spec` in place as the one proof; supersedes step 4's `tracedSpec` as a statement to
prove): today's statement with `s.gh.tr = none` replaced by `s.gh.tr ≠ none → s.role = .follower`, and the
`ApplyConfChange` line's gate (`HookGate s.gh.tr r (CCEvOf id s c c'.cfg) Q`: the state the hook reads is
`s`, the configuration before `c`, after `c'.cfg`) in, `Q` out. Its instances: today's untraced
`raft.applyConfChange.spec` (`Q := emp`, the gate from the struct's nil logger, `hookGate_none`; kept as a
derived theorem for its 4 untraced callers) and step 4's `raft.applyConfChange.tracedSpec` (the gate from
`trCapB_hookGate_applyCC` at `c'.cfg = c`, `Q` the capability at `s`, moved to `s'` by `simIdle_congr`
through `ApplyCCOkC`'s follower arm; kept as a derived theorem for `run`'s `confc` arm, unchanged).
`Bootstrap` calls it unbooted, per peer, with `trCapB_hookGate_ccBoot`'s gate. -/
abbrev raft.applyConfChange.gatedSpec : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState) (cc : Loc) (ccm : ConfChangeV2M) (dq : DFrac)
    (c' : CCState) (Q : IProp GF),
  ccApplyM ccm.transition ccm.changes (cfgStateC c) = some c' →
  (GMap.size c'.cfg.ids : Int) ≤ 2 ^ 62 →
  (s.role = .leader → s.term ≠ W64 0) →
  (s.role = .candidate ∨ s.role = .preCandidate → id ∈ c'.cfg.voters) →
  (s.gh.ns = true → s.role = .leader →
    2 ≤ plogLastIndexZ s.logst.prev (s.logst.sents ++ s.logst.uents)) →
  -- (step 5) in place of `s.gh.tr = none`: at a traced node, a follower
  (s.gh.tr ≠ none → s.role = .follower) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhysCV c c.voters r id s ∗
      "Hcc" ∷ ownConfChangeV2 cc dq ccm ∗
      -- (step 5) the `ApplyConfChange` line's gate, the caller's
      "Hgate" ∷ HookGate s.gh.tr r (CCEvOf id s c c'.cfg) Q }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"applyConfChange")) (Val #cc))
  {{ (cs : Loc) (xs os ls lns : List w64) (s' : NState), RET #cs;
      ownRaftPhysCV c'.cfg c'.cfg.voters r id s' ∗
      ownConfChangeV2 cc dq ccm ∗
      csPts cs (DFrac.own 1) (ConfStateM.mk xs ls os lns c'.cfg.autoLeave) true ∗
      ⌜xs ≡ₚ elements c'.cfg.incoming ∧ os ≡ₚ elements c'.cfg.outgoing ∧
        ls ≡ₚ elements c'.cfg.learners ∧ lns ≡ₚ elements c'.cfg.learnersNext⌝ ∗
      ⌜ApplyCCOkC c'.cfg id s s'⌝ ∗
      Q }}

end hooks

/-! ## 5. The constructors -/

section ctors
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **`newRaft(c)` in both modes** (replaces `newRaft.spec` in place; bootstrap positions 0-2 of §5.1):
today's statement with
- new binders `γ` (the cluster's raft names: the trace mode `γ.reTrace`, the capability's invariants) and
  `vs` (the voters: the capability's phase `bootPhase vs cv.ID'` at `bootCfg vs`);
- `TraceLoggerOk cv.TraceLogger'` replaced by the precondition's `trCapStart` (untraced exactly that
  premise) and the gated scope `BootFresh` (a traced node is a fresh one: the three lines' numbers are
  `BootEvAt`'s `0`s);
- the boot bundle's `InitialState` answer also giving `trNoCut γ.reTrace (interface.ok si)`, which the
  post hands on;
- the post's `s.gh = { sn := sn }` → `{ sn := sn, tr := γ.reTrace }`, plus `s.cq = cv.CheckQuorum'`
  (for `rnTrace`'s check-quorum field, true of the code today) and the capability, unbooted, after the
  three lines (`bootAt vs cv.ID' 2`: `trCapB_hookGate_init`, `traceConfChangeEvent.spec` with
  `trCapB_hookGate_ccBoot`, `raft.becomeFollower.traced` at `b = false`).
Untraced it is today's statement (`trCapStart none` is the nil logger, `trCapB none` is `emp`, `trNoCut
none` is free). -/
abbrev newRaft.gatedSpec : Prop :=
  ∀ (c : Loc) (cv : Config) (lok si : GoInterfaceOk)
    (sn : StorNames) (σ : StorState)
    (hs : HardStateM) (csm : ConfStateM) (R R' : IProp GF) (cs' : CCState)
    (γ : RaftNames) (vs : List w64),
  ConfigValid cv →
  cv.Logger' = interface.ok lok →
  cv.Storage' = interface.ok si →
  sint.Z cv.MaxInflightMsgs' < 2 ^ 62 →
  cv.DisableProposalForwarding' = false →
  cv.ReadOnlyOption' = W64 0 →
  cv.DisableConfChangeValidation' = false →
  (cv.MaxCommittedSizePerReady' ≠ W64 0 ∨ cv.MaxSizePerMsg' ≠ W64 0) →
  LogIndicesOk σ.prev σ.ents → σ.pend = [] →
  uint.nat σ.prev.index' ≤ σ.fr → σ.fr ≤ uint.nat (committedAfter σ.prev hs) →
  uint.Z σ.fl ≤ uint.Z σ.prev.index' → σ.sg ≤ uint.nat σ.prev.index' →
  σ.dt = ∅ →
  uint.Z σ.prev.index' + (σ.ents.length : Int) + 1 < 2 ^ 64 →
  AttachRec sn σ.prev σ.ents (uint.nat (committedAfter σ.prev hs))
    (max (uint.nat σ.prev.index') (uint.nat cv.Applied')) →
  (HsEmpty hs ∨ uint.Z σ.prev.index' ≤ uint.Z hs.Commit' ∧
    uint.Z hs.Commit' ≤ uint.Z σ.prev.index' + (σ.ents.length : Int)) →
  (cv.Applied' = W64 0 ∨ uint.Z σ.prev.index' ≤ uint.Z cv.Applied' ∧
    uint.Z cv.Applied' ≤ uint.Z (committedAfter σ.prev hs)) →
  restoreM csm.VotersOutgoing' csm.Voters' csm.Learners' csm.LearnersNext' csm.AutoLeave' =
    some cs' →
  (GMap.size (GMap.listToSet csm.Voters' ∪ GMap.listToSet csm.VotersOutgoing' ∪
    GMap.listToSet csm.Learners' ∪ GMap.listToSet csm.LearnersNext') : Int) ≤ 2 ^ 62 →
  ConfStateOk csm →
  -- (step 5) in place of `TraceLoggerOk cv.TraceLogger'` (now in `trCapStart`): a traced node is fresh
  (γ.reTrace ≠ none → BootFresh cv σ hs csm) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ c ↦ cv ∗ isLogger lok ∗ R ∗
      (□ {{ R }} (App (Val #(methods si.ty go!"FirstIndex" si.v)) (Val #()))
         {{ RET (PairV #(W64 (uint.nat σ.prev.index' + 1)) #interface.nil); R }}) ∗
      (□ {{ R }} (App (Val #(methods si.ty go!"LastIndex" si.v)) (Val #()))
         {{ RET (PairV #(W64 (uint.nat σ.prev.index' + σ.ents.length)) #interface.nil); R }}) ∗
      (□ {{ R }} (App (Val #(methods si.ty go!"InitialState" si.v)) (Val #()))
         {{ (hp cs : Loc) (al : Bool), RET (PairV (PairV #hp #cs) #interface.nil);
            hsOpt hp hs ∗ csPts cs DFrac.discard csm al ∗
            |={⊤}=> isStorageD sn (interface.ok si) ∗ ownStorage sn.unrec (interface.ok si) σ ∗
              -- (step 5) the storage's no-compaction, from the client's contract (traced)
              trNoCut γ.reTrace (interface.ok si) ∗ R' }}) ∗
      -- (step 5) the capability before the struct (untraced: the nil logger)
      trCapStart γ.reTrace γ cv.ID' cv.TraceLogger' (bootCfg vs) (bootPhase vs cv.ID') bootNone }}
    (App (Val #(functions newRaft [])) (Val #c))
  {{ (r : Loc) (s : NState) (cv' : Config), RET #r;
      R' ∗ ownRaftPhysC cs'.cfg r cv.ID' s ∗
      c ↦ cv' ∗ ⌜cv'.AsyncStorageWrites' = cv.AsyncStorageWrites'⌝ ∗
      ⌜NStateWf s ∧
        s.term = hs.Term' ∧
        s.vote = hs.Vote' ∧
        s.lead = W64 0 ∧ s.role = .follower ∧
        s.votes = ∅ ∧ s.outbox = [] ∧
        s.prevote = cv.PreVote' ∧
        -- (step 5) the check-quorum flag, for `rnTrace`
        s.cq = cv.CheckQuorum' ∧
        s.logst.prev = σ.prev ∧ s.logst.sents = σ.ents ∧ s.logst.uents = [] ∧
        s.logst.stored = σ.ents ∧
        s.logst.committed = committedAfter σ.prev hs ∧
        s.logst.applying = w64Max σ.prev.index'
          (if cv.Applied' = W64 0 then σ.prev.index' else cv.Applied') ∧
        s.logst.applied = s.logst.applying ∧
        s.logst.unpersisted = [] ∧ s.logst.snap = none ∧
        s.logst.storage = interface.ok si ∧
        s.logst.sn = sn ∧
        -- (step 5) the trace mode the cluster's (was `s.gh = { sn := sn }`)
        s.gh = { sn := sn, tr := γ.reTrace } ∧
        s.rd.states = [] ∧ s.rd.pend = [] ∧
        s.sdr = cv.StepDownOnRemoval' ∧ domSet s.progress = domSet cs'.prs ∧
        s.logst.dtk = uint.nat (committedAfter σ.prev hs)⌝ ∗
      -- (step 5) the storage's no-compaction, handed on, and the capability after positions 0-2
      trNoCut γ.reTrace (interface.ok si) ∗
      trCapB γ.reTrace γ r cv.ID' (bootCfg vs) false (bootPhase vs cv.ID') (bootAt vs cv.ID' 2) }}

/-- **`NewRawNode(c)` in both modes** (replaces `NewRawNode.spec` in place): today's with `newRaft`'s
changes (binders `γ`, `vs`; `trCapStart` and `BootFresh` for `TraceLoggerOk`; `trNoCut` in the
`InitialState` answer), the post's node `rawNodeAtT` at the struct `r` (the trace mode free), with the
mode, the check-quorum flag, `trNoCut` and the capability after positions 0-2 beside it. `RestartNode`
calls it untraced (its `Cluster.trace γ = none`): every addition vacuous. -/
abbrev NewRawNode.gatedSpec : Prop :=
  ∀ (c : Loc) (cv : Config) (lok si : GoInterfaceOk)
    (sn : StorNames) (σ : StorState)
    (hs : HardStateM) (csm : ConfStateM) (R R' : IProp GF) (cs' : CCState)
    (γ : RaftNames) (vs : List w64),
  ConfigValid cv →
  cv.Logger' = interface.ok lok →
  cv.Storage' = interface.ok si →
  sint.Z cv.MaxInflightMsgs' < 2 ^ 62 →
  cv.DisableProposalForwarding' = false →
  cv.ReadOnlyOption' = W64 0 →
  cv.DisableConfChangeValidation' = false →
  (cv.MaxCommittedSizePerReady' ≠ W64 0 ∨ cv.MaxSizePerMsg' ≠ W64 0) →
  cv.AsyncStorageWrites' = false →
  LogIndicesOk σ.prev σ.ents → σ.pend = [] →
  uint.nat σ.prev.index' ≤ σ.fr → σ.fr ≤ uint.nat (committedAfter σ.prev hs) →
  uint.Z σ.fl ≤ uint.Z σ.prev.index' → σ.sg ≤ uint.nat σ.prev.index' →
  σ.dt = ∅ →
  uint.Z σ.prev.index' + (σ.ents.length : Int) + 1 < 2 ^ 64 →
  AttachRec sn σ.prev σ.ents (uint.nat (committedAfter σ.prev hs))
    (max (uint.nat σ.prev.index') (uint.nat cv.Applied')) →
  (HsEmpty hs ∨ uint.Z σ.prev.index' ≤ uint.Z hs.Commit' ∧
    uint.Z hs.Commit' ≤ uint.Z σ.prev.index' + (σ.ents.length : Int)) →
  (cv.Applied' = W64 0 ∨ uint.Z σ.prev.index' ≤ uint.Z cv.Applied' ∧
    uint.Z cv.Applied' ≤ uint.Z (committedAfter σ.prev hs)) →
  restoreM csm.VotersOutgoing' csm.Voters' csm.Learners' csm.LearnersNext' csm.AutoLeave' =
    some cs' →
  (GMap.size (GMap.listToSet csm.Voters' ∪ GMap.listToSet csm.VotersOutgoing' ∪
    GMap.listToSet csm.Learners' ∪ GMap.listToSet csm.LearnersNext') : Int) ≤ 2 ^ 62 →
  ConfStateOk csm →
  -- (step 5) in place of `TraceLoggerOk cv.TraceLogger'`: a traced node is fresh
  (γ.reTrace ≠ none → BootFresh cv σ hs csm) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ c ↦ cv ∗ isLogger lok ∗ R ∗
      (□ {{ R }} (App (Val #(methods si.ty go!"FirstIndex" si.v)) (Val #()))
         {{ RET (PairV #(W64 (uint.nat σ.prev.index' + 1)) #interface.nil); R }}) ∗
      (□ {{ R }} (App (Val #(methods si.ty go!"LastIndex" si.v)) (Val #()))
         {{ RET (PairV #(W64 (uint.nat σ.prev.index' + σ.ents.length)) #interface.nil); R }}) ∗
      (□ {{ R }} (App (Val #(methods si.ty go!"InitialState" si.v)) (Val #()))
         {{ (hp cs : Loc) (al : Bool), RET (PairV (PairV #hp #cs) #interface.nil);
            hsOpt hp hs ∗ csPts cs DFrac.discard csm al ∗
            |={⊤}=> isStorageD sn (interface.ok si) ∗ ownStorage sn.unrec (interface.ok si) σ ∗
              trNoCut γ.reTrace (interface.ok si) ∗ R' }}) ∗
      trCapStart γ.reTrace γ cv.ID' cv.TraceLogger' (bootCfg vs) (bootPhase vs cv.ID') bootNone }}
    (App (Val #(functions NewRawNode [])) (Val #c))
  {{ (rn : Loc) (err : GoInterface), RET (PairV #rn #err);
      R' ∗ trNoCut γ.reTrace (interface.ok si) ∗
      ∃ (s : NState) (r : Loc),
        rawNodeAtT rn r cv.ID' si cs' cv.StepDownOnRemoval' cv.PreVote' hs σ cv.Applied' s ∗
        ⌜err = interface.nil⌝ ∗
        ⌜s.logst.sn = sn ∧ s.gh.sn = sn ∧ s.gh.tr = γ.reTrace ∧ s.cq = cv.CheckQuorum'⌝ ∗
        trCapB γ.reTrace γ r cv.ID' (bootCfg vs) false (bootPhase vs cv.ID') (bootAt vs cv.ID' 2) }}

/-- **`rn.Bootstrap(peers)` in both modes** (replaces `RawNode.Bootstrap.spec` in place; bootstrap
positions 3 to `|ps| + 3` of §5.1): today's with
- `γ.reTrace = none` replaced by `s.gh.tr = γ.reTrace` (the node's mode the cluster's, `ownRawNode`'s
  `Hgtr`) and the gated scope: pre-vote and check-quorum off (`rnTrace`'s `s.prevote = false` and
  `checkQuorum ↦□ false`), fewer than `2^40` peers (the bootstrap lines' `TraceEv.OkBoot`);
- the node `rawNodeFreshT` at the struct `r`, and the capability after positions 0-2 (`newRaft`'s) and
  the storage's `trNoCut` in the precondition;
- the post also giving the completion witness `bootDoneG γ.reTrace id`.
The proof: `becomeFollower(1, None)` by `raft.becomeFollower.traced` at `b = false` (position 3); per
peer `k`, `raft.applyConfChange.gatedSpec` with `trCapB_hookGate_ccBoot`'s gate (raft's configuration the
first `k` peers before, `k + 1` after; the capability at `bootCfg ps`; position `k + 4`); at the end
`trCapB_bootDone` (its `hΛ` from `bootPhase`'s `C = ps` and `bootAt ps id (|ps| + 3)`) mints the witness,
then `rnTrace` is packed inside `ownRawNode`: the capability re-keyed to the struct's configuration
(`trCapB_cfg`), its `Λ` weakened to the default and its phase moved to `SimIdle · s` (`simIdle_boot`, at
term `1`, the bootstrap log committed, nothing queued); `TrNoSnap` from `trNoCut` (`trNoCut_trNoSnap`,
`prev.index = 0`); clauses 1(a) (nothing delivered, any flag), 1(b) (`lt = 0`, no read, the outbox
empty), 1(c) (a follower), 1(d) (a simple configuration, `autoLeave = false`; the bootstrap log's
entries conf entries, `BootLogOk`). -/
abbrev RawNode.Bootstrap.gatedSpec : Prop :=
  ∀ (γ : RaftNames) (md : RNMode) (rn r : Loc) (id : w64) (si : GoInterfaceOk) (sdr pre : Bool)
    (s : NState)
    (peers : GoSlice) (dq : DFrac) (pv : List Peer) (ps : List w64) (ctxs : List (List w8))
    (bootLog : List EntryM),
  ps = pv.map Peer.ID' →
  ps ≠ [] → ps.Nodup → W64 0 ∉ ps →
  (ps.length : Int) ≤ 2 ^ 62 →
  id ∈ ps →
  γ.reCfg = GMap.listToSet ps →
  γ.reBoot = bootLog →
  BootLogOk ps bootLog →
  γ.reNoSnap = false →
  -- (step 5) in place of `γ.reTrace = none`: the node's mode the cluster's, and the traced scope
  s.gh.tr = γ.reTrace →
  (γ.reTrace ≠ none → pre = false ∧ s.cq = false ∧ ps.length < 2 ^ 40) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      rawNodeFreshT rn r id si ∅ sdr pre s ∗
      peers ↦*{dq} pv ∗ peersCtx pv ctxs ∗ bootMarshal ps ctxs bootLog ∗
      bootInit γ md id (GMap.listToSet ps) bootLog ∗ isCommitted γ bootLog ∗
      certLink γ s.gh.sn ∗
      -- (step 5) the capability after positions 0-2, and the storage's no-compaction
      trCapB γ.reTrace γ r id (bootCfg ps) false (bootPhase ps id) (bootAt ps id 2) ∗
      trNoCut γ.reTrace (interface.ok si) }}
    (App (Val (rn @!! go.GoType.PointerType RawNode.ty @!! go!"Bootstrap")) (Val #peers))
  {{ (err : GoInterface), RET #err;
      ⌜err = interface.nil⌝ ∗
      ownRawNode γ rn id
        { delivered := [], unpersisted := [], steps := [], term := W64 1,
          storage := interface.ok si, sn := s.gh.sn, mode := md,
          cfg := cfgState (GMap.listToSet ps) ∅, tc := W64 1 } ∗
      peers ↦*{dq} pv ∗
      -- (step 5, A8.3) the completion witness
      bootDoneG γ.reTrace id }}

/-- **`setupNode(c, peers)` in both modes** (replaces `setupNode.spec` in place): today's with
`TraceLoggerOk cv.TraceLogger'` and `γ.reTrace = none` replaced by the capability's start (`trCapStart`
at the peers' bootstrap phase) and the gated scope (pre-vote and check-quorum off, fewer than `2^40`
peers; `BootFresh` follows from today's premises), `trNoCut` in the `InitialState` answer, and the
completion witness in the post. Its proof threads `NewRawNode.gatedSpec`'s capability, `trNoCut` and mode
into `RawNode.Bootstrap.gatedSpec` (`rawNodeAtT` to `rawNodeFreshT` as `rawNodeAt_fresh` does). -/
abbrev setupNode.gatedSpec : Prop :=
  ∀ (γ : RaftNames) (md : RNMode) (c : Loc) (cv : Config) (lok si : GoInterfaceOk)
    (sn : StorNames) (σ : StorState) (hs : HardStateM) (csm : ConfStateM) (R R' : IProp GF)
    (peers : GoSlice) (dq : DFrac) (pv : List Peer) (ps : List w64) (ctxs : List (List w8))
    (bootLog : List EntryM),
  ConfigValid cv →
  cv.Logger' = interface.ok lok →
  cv.Storage' = interface.ok si →
  sint.Z cv.MaxInflightMsgs' < 2 ^ 62 →
  cv.DisableProposalForwarding' = false →
  cv.ReadOnlyOption' = W64 0 →
  cv.DisableConfChangeValidation' = false →
  (cv.MaxCommittedSizePerReady' ≠ W64 0 ∨ cv.MaxSizePerMsg' ≠ W64 0) →
  cv.AsyncStorageWrites' = false →
  cv.Applied' = W64 0 →
  σ.prev = entryID.mk (W64 0) (W64 0) → σ.ents = [] → σ.pend = [] →
  σ.fr = 0 → σ.sg = 0 → σ.dt = ∅ →
  HsEmpty hs →
  csm.Voters' = [] →
  csm.VotersOutgoing' = [] →
  csm.Learners' = [] →
  csm.LearnersNext' = [] →
  csm.AutoLeave' = false →
  σ.fl = W64 0 →
  sn.unrec = sn →
  ps = pv.map Peer.ID' →
  ps ≠ [] → ps.Nodup → W64 0 ∉ ps →
  (ps.length : Int) ≤ 2 ^ 62 →
  cv.ID' ∈ ps →
  γ.reCfg = GMap.listToSet ps →
  γ.reBoot = bootLog →
  BootLogOk ps bootLog →
  γ.reNoSnap = false →
  -- (step 5) in place of `TraceLoggerOk cv.TraceLogger'` (now in `trCapStart`) and `γ.reTrace = none`
  (γ.reTrace ≠ none → cv.PreVote' = false ∧ cv.CheckQuorum' = false ∧ ps.length < 2 ^ 40) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ c ↦ cv ∗ isLogger lok ∗ R ∗
      (□ {{ R }} (App (Val #(methods si.ty go!"FirstIndex" si.v)) (Val #()))
         {{ RET (PairV #(W64 1) #interface.nil); R }}) ∗
      (□ {{ R }} (App (Val #(methods si.ty go!"LastIndex" si.v)) (Val #()))
         {{ RET (PairV #(W64 0) #interface.nil); R }}) ∗
      (□ {{ R }} (App (Val #(methods si.ty go!"InitialState" si.v)) (Val #()))
         {{ (hp cs : Loc) (al : Bool), RET (PairV (PairV #hp #cs) #interface.nil);
            hsOpt hp hs ∗ csPts cs DFrac.discard csm al ∗
            |={⊤}=> isStorageD sn (interface.ok si) ∗ ownStorage sn (interface.ok si) σ ∗
              -- (step 5) the storage's no-compaction (traced: from the client's contract)
              trNoCut γ.reTrace (interface.ok si) ∗ R' }}) ∗
      peers ↦*{dq} pv ∗ peersCtx pv ctxs ∗ bootMarshal ps ctxs bootLog ∗
      bootInit γ md cv.ID' (GMap.listToSet ps) bootLog ∗ isCommitted γ bootLog ∗
      certLink γ sn ∗
      -- (step 5) the capability's start (untraced: the nil logger)
      trCapStart γ.reTrace γ cv.ID' cv.TraceLogger' (bootCfg ps) (bootPhase ps cv.ID') bootNone }}
    (App (App (Val #(functions setupNode [])) (Val #c)) (Val #peers))
  {{ (n : Loc), RET #n;
      R' ∗ ∃ (nv : node) (rn : Loc),
        n ↦ nv ∗ ⌜nv.rn' = rn⌝ ∗ newNodeChans nv ∗
        ownRawNode γ rn cv.ID'
          { delivered := [], unpersisted := [], steps := [], term := W64 1,
            storage := interface.ok si, sn := sn, mode := md,
            cfg := cfgState (GMap.listToSet ps) ∅, tc := W64 1 } ∗
        peers ↦*{dq} pv ∗
        -- (step 5, A8.3) the completion witness
        bootDoneG γ.reTrace cv.ID' }}

end ctors

/-! ## 6. `StartNode`: the fit in `startTrace` (review step4-r1's S1) -/

section start
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **What a node brings of the trace to `StartNode`, with the receipts' fit** (replaces the Draft's
`startTrace` in place, and `TracedNodeApi.lean`'s `startTraceC` the same way; review `step4-r1.md`'s S1):
the Draft's, with the cluster's namespace `N` (for `readyFits γ N`, the node API's sealed fit) and, in
the traced branch, `readyFits γ N` and `2 ≤ vs.length`. Together (`|γ.raft.reBoot| = |vs|` by
`BootLogOk`) they give `node.run.gatedSpec`'s `RunTracedOk` but its first conjunct (which is `StartNode`'s
`HdynOk`): `traceReadyFits GF γ.raft` (`readyFits`' body at raft's names) and `receiptBound GF + 2 ≤
traceNumBound` (the fit at `|vs| ≥ 2`; the ceiling `rs.tc ≤ receiptBound GF` raised by one, by a tick or
`Campaign`'s `MsgHup`, stays below the bound). Untraced, unchanged (the nil logger). -/
def startTraceF (γ : Cluster) (N : Namespace) (vs : List w64) (cv : Config) : IProp GF :=
  match Cluster.trace γ with
  | none => iprop(⌜cv.TraceLogger' = interface.nil⌝)
  | some γd => iprop(∃ tn : TraceNames, traceDir γd tn ∗
      ⌜TracedConfigOk cv ∧ tn.voters = vs ∧ vs.length < 2 ^ 40 ∧ 2 ≤ vs.length ∧
        cv.TraceLogger' ≠ interface.nil⌝ ∗
      readyFits γ N ∗
      isTraceLogger tn.tr cv.TraceLogger' ∗ Cluster.traceSimInv γ vs tn ∗
      simNode tn cv.ID' (toC (confAbs vs) ((simInit vs).s (idAbs cv.ID'))) [] ∗
      simBoot tn cv.ID' false none)

/-- **`StartNode`, gated, with the fit** (replaces the Draft's `StartNode.gatedSpec` in place, and
`TracedNodeApi.lean`'s `StartNode.tracedSpec`, hence `HarnessOpen`, the same way): word for word the
Draft's but `startTraceF γ N vs cv` for `startTrace γ vs cv`. Proved from `setupNode.gatedSpec` and
`node.run.gatedSpec` (`StartNode.gatedSpecF_of`); `StartNode.spec` (the server's) its instance. -/
abbrev StartNode.gatedSpecF : Prop :=
  ∀ (γ : Cluster) (N : Namespace) (vs : List w64) (ctxs : List (List w8)) (c : Loc) (cv : Config)
    (lok si : GoInterfaceOk) (csm : ConfStateM) (Q : IProp GF) (F : GName → IProp GF)
    (peers : GoSlice) (dq : DFrac) (pv : List Peer),
  ConfigValid cv →
  cv.Logger' = interface.ok lok →
  cv.Storage' = interface.ok si →
  sint.Z cv.MaxInflightMsgs' < 2 ^ 62 →
  cv.DisableProposalForwarding' = false →
  cv.ReadOnlyOption' = W64 0 →
  cv.DisableConfChangeValidation' = false →
  (cv.MaxCommittedSizePerReady' ≠ W64 0 ∨ cv.MaxSizePerMsg' ≠ W64 0) →
  cv.AsyncStorageWrites' = false →
  cv.Applied' = W64 0 →
  csm.Voters' = [] → csm.VotersOutgoing' = [] → csm.Learners' = [] → csm.LearnersNext' = [] →
  csm.AutoLeave' = false →
  vs = pv.map Peer.ID' →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ c ↦ cv ∗ isLogger lok ∗
      nodeBoot γ N vs ctxs cv.ID' ∗ nodeVacant γ cv.ID' ∗
      AU <{ ∃∃ (S : RaftState), raftState γ cv.ID' S ∗ ⌜S = RaftState.init⌝ }> @ ⊤ \ ↑N, ∅
         <{ raftState γ cv.ID' S, COMM Q }> ∗
      restartStorage γ (interface.ok si) ⟨hsZero, none, entryID.mk (W64 0) (W64 0), []⟩ csm 0 F ∗
      peers ↦*{dq} pv ∗ peersCtx pv ctxs ∗ startTraceF γ N vs cv }}
    (App (App (Val #(functions StartNode [])) (Val #c)) (Val #peers))
  {{ (nd : GoInterface), RET #nd;
      ∃ (n : Loc) (K : GName), ⌜nd = interface.mkOk (go.GoType.PointerType node.ty) #n⌝ ∗
        nodeStartedFresh n γ N vs ctxs cv.ID' ∗
        isNode n γ N cv.ID' ∗ nodeDriver n γ N (NodeDriverState.init (interface.ok si) K) ∗
        nodeConfig n γ N ⟨0, Membership.simple (GMap.listToSet vs)⟩ ∗
        nodeRunning n γ N 1 ∗ Q ∗ F K ∗ peers ↦*{dq} pv ∗ startDoneB γ cv.ID' }}

/-- **What `StartNode`'s proof reads off `startTraceF` and `nodeBoot`** (the replacement of
`startTrace_trCapB`, which needed the struct): the capability's start for `setupNode` (at raft's names,
the peers' bootstrap phase, nothing logged yet), and, traced, `setupNode`'s scope (`TracedConfigOk`, fewer
than `2^40` voters) and `node.run.gatedSpec`'s fit (`RunTracedOk`'s second and third conjuncts). -/
abbrev startTraceF_trCapStart.statement : Prop :=
  ∀ (γ : Cluster) (N : Namespace) (vs : List w64) (ctxs : List (List w8)) (cv : Config),
  (startTraceF γ N vs cv ∗ nodeBoot γ N vs ctxs cv.ID' : IProp GF) ⊢
    ⌜(Cluster.raftNames γ).reTrace ≠ none → TracedConfigOk cv ∧ vs.length < 2 ^ 40 ∧
      traceReadyFits GF (Cluster.raftNames γ) ∧ receiptBound GF + 2 ≤ traceNumBound⌝ ∗
    trCapStart (Cluster.raftNames γ).reTrace (Cluster.raftNames γ) cv.ID' cv.TraceLogger' (bootCfg vs)
      (bootPhase vs cv.ID') bootNone

/-- Untraced, `startTraceF` is today's premise (`startTrace_untraced`'s form): what makes
`StartNode.spec` an instance of `StartNode.gatedSpecF`. -/
abbrev startTraceF_untraced.statement : Prop :=
  ∀ (γ : Cluster) (N : Namespace) (vs : List w64) (cv : Config), Cluster.trace γ = none →
  (startTraceF γ N vs cv : IProp GF) ⊣⊢ iprop(⌜TraceLoggerOk cv.TraceLogger'⌝)

end start

end EtcdGrove
end Perennial
