-- The copy for the part `RaftNoAx/` of `Proof/go_etcd_io/raft/v3/RawNodeAt.lean` (etc/copy-part.py; rerun it, do not edit).
/-
Lean-first (#33 S3c step 3, `notes/antithesis-rawnode-design.md` §2.1, §2.5, §2.6). **A `RawNode` at
its protocol state**: `ownRawNodeAt γ rn id rs r qs ip sc` is `ownRawNode γ rn id rs` with the
node's `RState` reading named (`toRState rs fp s = r`; antithesis parity stage 3: until then its
protocol reading `toPState s = ps`), the protocol messages of the queue `Advance` will
step named (`qs`, `PendAbs`), the in-progress boundary named (`ip`: the entries the last `Ready`s
handed out, `unstable.offsetInProgress - 1`), and, at a scope `sc = some md`, the Antithesis
harness's scope (`RnScope`, `storCapF … 0`). Statements only: the two entailments with `ownRawNode` are `.law`s,
proved with the strengthened specs (phase 2).

Deviations from the design's sketch (§2.6 of the design lists them with the reasons):
* the scope `sc : Option RnMode` (antithesis parity, design §2: was a flag `sc : Bool`, `none` its
  `false` and `some {}` its `true`; the design had the scope conjuncts unconditionally): with them unconditional,
  `ownRawNode ⊢ ∃ ps qs, ownRawNodeAt …` is false (an `ownRawNode` with pre-vote on has no
  `ownRawNodeAt`), and so is every corollary `RawNode.<F>.spec_of_abs`; at `sc = none` the entailment
  holds and the strengthened specs have the old ones as corollaries;
* the queue: `ownRawNode`'s `"Hpend"` (`pendList`, each message's state existential) is restated with
  the states named (`pendAt`), not a persistent `pendAbs` beside it: `msgIn` owns the message's
  struct, so no persistent fact pins a queued message's state;
* the no-snapshot conjunct is stated directly (the `nc`/`NoSnapG` machinery of §2.5's option (b) does
  not exist yet): the log's boundary `prev = base0`, no snapshot pending or lent, no queued `MsgSnap`,
  and the storage never compacted past `0` (`storCapF … 0`), which refutes `maybeSendAppend`'s
  snapshot fallback (`prev ≠ 0 ∨ storPast … 1`, `TrNoSnap`'s form);
* the scope conjunct has `s.rd.pend = []` too (no read-index request pending: `LiftScope`'s, which the
  `InputEnd` lifting lemmas need);
* (2026-11-24, the coordinator's decision 3) the in-progress boundary `ip`, which the sketch did not
  have: `Ready`'s first entry is at `ip + 1`, and the binding's "first reported entry is the first
  conflict with the durable log" (B 378, 387) follows from it under the harness's discipline (one
  input from an idle node, where `ip` is the log's length), not of `ps` alone (design §2.6).
-/
module

public import RaftNoAx.Proof.go_etcd_io.raft.v3.InvRawnode
public import Proof.go_etcd_io.raft.v3.Protocol.RnMode
import all RaftNoAx.Proof.go_etcd_io.raft.v3.InvRawnode

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- The protocol reading of a physical message's state (`msgAbs`'s, total on the types `mtypeOf`
names): `absMsg` at its type, `absSnap` for a `MsgSnap` with its snapshot; `none` otherwise. -/
def absMsgOf (st : MsgSt) : Option Msg :=
  match mtypeOf st.msg.Type' with
  | none => none
  | some .snap => st.snap.map fun sv => absSnap st.msg sv sv.Metadata'.ConfState'.lists
  | some ty => some (absMsg ty st.msg st.ents st.ctx)

/-- A protocol role as Go's `StateType` (`Ready.SoftState.RaftState`): what the harness reports. -/
def roleGo : Role → StateType
  | .follower => StateFollower
  | .candidate => StateCandidate
  | .leader => StateLeader

/-- **The `RState` reading of a node** (antithesis parity, design §1.1; `ownRawNodeAt`'s `"%Hps"`):
the protocol reading `toPState`, raft's `applied`, `pendingConfIndex` as the dynamic model reads it
(`pciR`: the code's at a leader, `0` elsewhere -- Go clears it in `reset`, and the model reads it only at
a leader; design §1.1 has `s.pci`, which would need the code invariant "a non-leader's
`pendingConfIndex` is `0`"), whether a restored snapshot is pending, and the `RawNode`'s configuration
index and configuration (`rs.capplied`, `rs.cfg`) with the ghost prefix `fp`. It is `rOf` at the
`RawNode`'s ghost part (`toRState_eq_rOf`). -/
def toRState (rs : RNState) (fp : List EntryM) (s : NState) : RState :=
  { p := toPState s, applied := s.logst.applied, pci := pciR s, snap := s.logst.snap.isSome,
    cidx := rs.capplied, cfg := rs.cfg, fp := fp }

theorem toRState_eq_rOf (rs : RNState) (fp : List EntryM) (s : NState) (ds : DecMap) :
    toRState rs fp s = rOf s ⟨rs.capplied, rs.cfg, fp, ds⟩ := rfl

@[simp] theorem toRState_p (rs : RNState) (fp : List EntryM) (s : NState) :
    (toRState rs fp s).p = toPState s := rfl
@[simp] theorem toRState_applied (rs : RNState) (fp : List EntryM) (s : NState) :
    (toRState rs fp s).applied = s.logst.applied := rfl
@[simp] theorem toRState_pci (rs : RNState) (fp : List EntryM) (s : NState) :
    (toRState rs fp s).pci = pciR s := rfl
@[simp] theorem toRState_snap (rs : RNState) (fp : List EntryM) (s : NState) :
    (toRState rs fp s).snap = s.logst.snap.isSome := rfl
@[simp] theorem toRState_cidx (rs : RNState) (fp : List EntryM) (s : NState) :
    (toRState rs fp s).cidx = rs.capplied := rfl
@[simp] theorem toRState_cfg (rs : RNState) (fp : List EntryM) (s : NState) :
    (toRState rs fp s).cfg = rs.cfg := rfl
@[simp] theorem toRState_fp (rs : RNState) (fp : List EntryM) (s : NState) :
    (toRState rs fp s).fp = fp := rfl

/-- **The node constant tied to the raft state** (antithesis parity B1, 2026-11-25; the lead's
decision): the `RawNode`'s `rs.k` is its raft state's `Config` flags (`preVote`, `checkQuorum`,
`stepDownOnRemoval`, which `newRaft` copies and nothing writes). -/
def KTie (rs : RNState) (s : NState) : Prop := NodeK.mk s.prevote s.cq s.sdr = rs.k

/-- **The queue's protocol messages** (design §2.1, F4): `qs` is, in the queue's order, the reading
(`absMsgOf`) of each queued self-addressed response (`Pending.self`: a leader's self-acknowledgement,
a candidate's self-vote), the queued messages' states being `sts`; the storage acknowledgements
(`appendAck`, `applyAck`) carry no protocol message. -/
def PendAbs (sts : List MsgSt) (ps : List Pending) (qs : List Msg) : Prop :=
  sts.length = ps.length ∧
  qs = (sts.zip ps).filterMap fun x =>
    match x.2 with
    | .self _ _ => absMsgOf x.1
    | _ => none

/-- **The Antithesis harness's scope at the mode `md`** (antithesis parity, design §2; each conjunct
is today's, guarded by the mode flag that lifts it): without `confChanges`, no outgoing half in the
dynamic mode (the configuration never changes); without `prevote`/`cq`, the `Config`'s flags off
(copied by `newRaft`, never written); without `reads`, no read-index request pending and a leader's
read-only queue empty (its heartbeats carry no context, `hbCtx`); without `snapshots`, the log's
boundary at `base0` (never compacted), no snapshot pending or lent, no `MsgSnap` queued; without
`transfer`, no transfer request stepped (`NGhost.xs`: every queued message is of a type the model
describes, `XfOk`). `RnScope {}` is the first harness's scope (`RnScopeBasic`, `RnScope_empty`). -/
def RnScope (md : RnMode) (rs : RNState) (s : NState) : Prop :=
  (md.confChanges = false → rs.mode.isDyn = true → rs.cfg.cfg.outgoing = ∅) ∧
  (md.prevote = false → s.prevote = false) ∧ (md.cq = false → s.cq = false) ∧
  (md.reads = false → s.rd.pend = [] ∧ (s.role = .leader → s.rd.ro.pending = [])) ∧
  (md.snapshots = false → rs.slent = none ∧ s.logst.prev = base0 ∧ s.logst.snap = none ∧
     ∀ m ∈ s.outbox, m.ty ≠ .snap) ∧
  (md.transfer = false → s.gh.xs = false)

/-- **The first harness's scope, flat** (`RnScope {}`, `RnScope_empty`; the conjunction the proofs of
the basic scope read by position): a simple configuration (in the dynamic mode no outgoing half),
pre-vote and check-quorum off, no read-index request pending; the log's boundary at `base0`, no
snapshot pending or lent, no `MsgSnap` queued; a leader's read-only queue empty; no transfer request
stepped. -/
def RnScopeBasic (rs : RNState) (s : NState) : Prop :=
  (rs.mode.isDyn = true → rs.cfg.cfg.outgoing = ∅) ∧ s.prevote = false ∧ s.cq = false ∧
  s.rd.pend = [] ∧ rs.slent = none ∧ s.logst.prev = base0 ∧ s.logst.snap = none ∧
  (∀ m ∈ s.outbox, m.ty ≠ .snap) ∧ (s.role = .leader → s.rd.ro.pending = []) ∧ s.gh.xs = false

theorem RnScope_empty (rs : RNState) (s : NState) : RnScope {} rs s ↔ RnScopeBasic rs s := by
  unfold RnScope RnScopeBasic
  simp only [forall_const]
  constructor
  · rintro ⟨h1, h2, h3, ⟨h4, h5⟩, ⟨h6, h7, h8, h9⟩, h10⟩
    exact ⟨h1, h2, h3, h4, h6, h7, h8, h9, h5, h10⟩
  · rintro ⟨h1, h2, h3, h4, h6, h7, h8, h9, h5, h10⟩
    exact ⟨h1, h2, h3, ⟨h4, h5⟩, ⟨h6, h7, h8, h9⟩, h10⟩

/-- **The first harness's scope as a scope option** (`none` outside the scope, `some {}` in it): the
statements of the basic scope quantify over a `Bool`. -/
abbrev basicScope : Bool → Option RnMode
  | true => some {}
  | false => none

open Classical in
/-- **The length of the longest common prefix of two logs.** An input that truncates the log from
the index `k + 1` and appends keeps `k` entries in common (`unstable.truncateAndAppend` writes from
the first conflict, whose term differs); one that only appends keeps the whole old log. The input
forms state the in-progress boundary after an input with it (`RawNodeAbsSpecs.lean`). -/
def lcpLen : List EntryM → List EntryM → Nat
  | a :: xs, b :: ys => if a = b then lcpLen xs ys + 1 else 0
  | _, _ => 0

end pure

section rawnode_at
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **The queue with its messages' states named** (`ownRawNode`'s `"Hpend"`, `lentPend` of
`pendList`, with the states `sts` out of the big separating conjunction): with no snapshot lent, the
queued messages owned at the states `sts`, each with its `pendingRel`, and `qs` their protocol
messages (`PendAbs`); with one lent, `ownRawNode`'s conjunct as it is and `qs` unconstrained (a
snapshot `Ready` is outside the harness's scope, `RnScope`). -/
def pendAt (γ : RaftNames) (id : w64) (W : DurMaps) :
    Option SnapLoan → List Loc → List Pending → List Msg → IProp GF
  | none, steps, ps, qs => iprop(∃ sts : List MsgSt, ⌜PendAbs sts ps qs⌝ ∗
      [∗list] l;x ∈ steps;sts.zip ps, msgIn l DFrac.discard x.1 ∗ pendingRel γ id W x.1 x.2)
  | some lo, steps, ps, _ => lentPend (some lo) (pendList γ id W steps ps)

/-- **The node in the harness's configuration at the mode `md`** (design §2): without `nonVoters`, among
the names' voters; without `confChanges`, in the dynamic mode the configuration's incoming voters
the names' and no learners (so the progress map's ids, `ownTrackerC`'s `CfgM.ids`, are the voters and
a leader's sends go to voters); the cluster untraced (the harness's, `NewRawNode.emptyStartForm`'s
`Cluster.trace γ = none`) and the dynamic mode (`NewRawNode.restartAtSpec`'s). -/
def RnCfgIn (md : RnMode) (γ : RaftNames) (id : w64) (rs : RNState) : Prop :=
  (md.nonVoters = false → id ∈ γ.reCfg) ∧
  (md.confChanges = false → (rs.mode.isDyn = true → rs.cfg.cfg.incoming = γ.reCfg) ∧
     rs.cfg.cfg.learners = ∅) ∧
  γ.reTrace = none ∧ rs.mode.isDyn = true

/-- **The node in the first harness's configuration, flat** (`RnCfgIn {}`, `RnCfgIn_empty`). -/
def RnCfgInBasic (γ : RaftNames) (id : w64) (rs : RNState) : Prop :=
  id ∈ γ.reCfg ∧ (rs.mode.isDyn = true → rs.cfg.cfg.incoming = γ.reCfg) ∧ γ.reTrace = none ∧
  rs.mode.isDyn = true ∧ rs.cfg.cfg.learners = ∅

theorem RnCfgIn_empty (γ : RaftNames) (id : w64) (rs : RNState) :
    RnCfgIn {} γ id rs ↔ RnCfgInBasic γ id rs := by
  unfold RnCfgIn RnCfgInBasic
  simp only [forall_const]
  constructor
  · rintro ⟨h1, ⟨h2, h5⟩, h3, h4⟩; exact ⟨h1, h2, h3, h4, h5⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩; exact ⟨h1, ⟨h2, h5⟩, h3, h4⟩

/-- `RnCfgIn` reads only the mode and the configuration of the `RNState`. -/
theorem RnCfgIn.keep {md : RnMode} {γ : RaftNames} {id : w64} {rs rs' : RNState}
    (hcf : rs'.mode = rs.mode ∧ rs'.cfg = rs.cfg) (H : RnCfgIn md γ id rs) : RnCfgIn md γ id rs' := by
  unfold RnCfgIn at *; rw [hcf.1, hcf.2]; exact H

/-- **The harness's scope, owned part**: at `some md` `RnScope md`, the node in the harness's
configuration (`RnCfgIn md`) and, without `snapshots`, the storage never compacted past `0`
(`storCapF`, persistent), and the node constant `rs.k` the raft state's flags (`KTie`: outside the
scope an `ownRawNode`'s `rs.k` is unconstrained, `ownRawNode_at`); nothing at `none`. -/
def rnScopeAt (γ : RaftNames) (id : w64) (sc : Option RnMode) (rs : RNState) (s : NState) :
    IProp GF :=
  match sc with
  | none => iprop(emp)
  | some md => iprop(⌜RnScope md rs s ∧ RnCfgIn md γ id rs ∧ KTie rs s⌝ ∗
                     □ (⌜md.snapshots = false⌝ -∗ storCapF s.logst.storage 0))

/-- **A `RawNode` at its protocol state** (see the file header): `ownRawNode`'s body, conjunct for
conjunct, but `"Hpend"` with the queued states named (`pendAt`), and three conjuncts more: the
`RState` reading `toRState rs fp s = r`, the in-progress boundary `ip + 1 = offsetInProgress`, and the
harness's scope at `sc` (`rnScopeAt`). -/
def ownRawNodeAt (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (r : RState) (qs : List Msg)
    (ip : Nat) (sc : Option RnMode) : IProp GF :=
  iprop(∃ (s : NState) (cf : CfgM) (fp : List EntryM) (ds : DecMap) (rnv : RawNode) (sv : SoftState)
      (hprev : HardStateM) (steps : List Loc),
  "Hrn" ∷ rawNodeOwn rn rnv ∗
  "Hphys" ∷ ownRaftPhysCV cf cf.voters rnv.raft' id s ∗
  "Hghost" ∷ ownStepGhost γ (rs.mode.toG ⟨rs.capplied, rs.cfg, fp, ds⟩) cf id s ∗
  "#Hsdrf" ∷ sdrOk rnv.raft' rs.mode ∗
  "%Hwf" ∷ ⌜NStateWf s⌝ ∗
  "%Hin" ∷ ⌜rs.mode = .static → id ∈ γ.reCfg⌝ ∗
  "%Hasync" ∷ ⌜rnv.asyncStorageWrites' = false⌝ ∗
  "#Hsoft" ∷ rnv.prevSoftSt' ↦□ sv ∗
  "#Hhard" ∷ prevHS γ rnv.prevHardSt' hprev rs.phs ∗
  "Hsteps" ∷ rnv.stepsOnAdvance' ↦* steps ∗
  "Hsteps_cap" ∷ ownSliceCap Loc rnv.stepsOnAdvance' (DFrac.own 1) ∗
  -- (#33 S3c) `ownRawNode`'s `lentPend rs.slent (pendList …)`, the states named
  "Hpend" ∷ pendAt γ id rs.bw rs.slent steps rs.steps qs ∗
  "#Hdeliv" ∷ isCommitted γ rs.delivered ∗
  "#Hstrecs" ∷ ackInv γ rs s ∗
  "#Hloanc" ∷ loanCom γ rs.slent ∗
  "%Hdlen" ∷ ⌜rs.delivered.length = (uint.Z s.logst.applying).toNat⌝ ∗
  "%Hunp" ∷ ⌜rs.unpersisted = s.logst.unpersisted⌝ ∗
  "%Hsnap" ∷ ⌜rs.psnap = false ∧ rs.slent = none → s.logst.snap = none⌝ ∗
  "%Hstok" ∷ ⌜StepsOk s rs.steps⌝ ∗
  "%Htrm" ∷ ⌜rs.term = s.term⌝ ∗
  "%Hstor" ∷ ⌜rs.storage = s.logst.storage ∧ rs.sn = s.logst.sn⌝ ∗
  "%Hpvoff" ∷ ⌜RNPv rs fp s⌝ ∗
  "%Hrs_out" ∷ ⌜rs.outlb = s.gh.outlb⌝ ∗
  "%Hrs_unst" ∷ ⌜rs.unst = s.gh.unst⌝ ∗
  "%Hrs_clb" ∷ ⌜uint.Z rs.clb ≤ uint.Z s.logst.committed⌝ ∗
  "%Hrnfl" ∷ ⌜RNFl rs s⌝ ∗
  "%Hloan" ∷ ⌜LoanOk rs s⌝ ∗
  "#Hsloc" ∷ snapLocOk γ id s.logst.snap ∗
  "#Hhist" ∷ restoredSnapHistory γ id s.logst.ksn ∗
  "Hledger" ∷ restoreLedger γ id rs.sn s ∗
  "%Hsdt" ∷ ⌜SdtTie rs s⌝ ∗
  "%Hrole" ∷ ⌜rs.role = sv.RaftState'⌝ ∗
  "#Hdur" ∷ durTie γ rs s ∗
  "%Hphs" ∷ ⌜PhsOk rs s⌝ ∗
  "%Hgtr" ∷ ⌜s.gh.tr = γ.reTrace⌝ ∗
  "%Hglq" ∷ ⌜s.gh.lq = []⌝ ∗
  "Hrntr" ∷ rnTrace γ rnv.raft' id cf rs.delivered s ∗
  -- (#33 S3c) the protocol reading, and the harness's scope at `sc`
  "%Hps" ∷ ⌜toRState rs fp s = r⌝ ∗
  "%Hip" ∷ ⌜uint.nat s.logst.inprogress = ip + 1⌝ ∗
  "Hsc" ∷ rnScopeAt γ id sc rs s)

/-- **Forgetting the protocol state** (design §2.1, `ownRawNodeAt_ownRawNode`): at any scope.
By unfolding: `pendAt` gives `pendList`, the rest is `ownRawNode`'s body. -/
abbrev ownRawNodeAt_ownRawNode.law : Prop :=
  ∀ (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (r : RState) (qs : List Msg) (ip : Nat)
    (sc : Option RnMode),
    ownRawNodeAt (GF := GF) γ rn id rs r qs ip sc ⊢ ownRawNode γ rn id rs

/-- **Naming the protocol state** (design §2.1, `ownRawNode_at`): every `ownRawNode` is an
`ownRawNodeAt` outside the harness's scope (`sc = none`), at its node's `RState` reading, its
queue's messages and its in-progress boundary (`offsetInProgress ≥ 1`: `Hipb`'s `offset ≤`). -/
abbrev ownRawNode_at.law : Prop :=
  ∀ (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState),
    ownRawNode (GF := GF) γ rn id rs ⊢
      ∃ (r : RState) (qs : List Msg) (ip : Nat), ownRawNodeAt γ rn id rs r qs ip none

end rawnode_at

end EtcdGrove
end Perennial
