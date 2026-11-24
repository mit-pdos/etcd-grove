-- The copy for the part `KvNet/` of `RaftNoAx/Proof/go_etcd_io/raft/v3/RawNodeAt.lean` (etc/copy-part.py; rerun it, do not edit).
/-
Lean-first (#33 S3c step 3, `notes/antithesis-rawnode-design.md` §2.1, §2.5, §2.6). **A `RawNode` at
its protocol state**: `ownRawNodeAt γ rn id rs ps qs ip sc` is `ownRawNode γ rn id rs` with the
node's protocol reading named (`toPState s = ps`), the protocol messages of the queue `Advance` will
step named (`qs`, `PendAbs`), the in-progress boundary named (`ip`: the entries the last `Ready`s
handed out, `unstable.offsetInProgress - 1`), and, at the scope flag `sc = true`, the Antithesis
harness's scope (`RnScope`, `storCapF … 0`). Statements only: the two entailments with `ownRawNode` are `.law`s,
proved with the strengthened specs (phase 2).

Deviations from the design's sketch (§2.6 of the design lists them with the reasons):
* the scope flag `sc` (the design had the scope conjuncts unconditionally): with them unconditional,
  `ownRawNode ⊢ ∃ ps qs, ownRawNodeAt …` is false (an `ownRawNode` with pre-vote on has no
  `ownRawNodeAt`), and so is every corollary `RawNode.<F>.spec_of_abs`; at `sc = false` the entailment
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

public import KvNet.Proof.go_etcd_io.raft.v3.InvRawnode
import all KvNet.Proof.go_etcd_io.raft.v3.InvRawnode

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

/-- **The Antithesis harness's scope** (design §2.1's scope conjunct, F6, and §2.5's no-snapshot
conjunct, option (b) stated directly): the static mode, pre-vote and check-quorum off (the
`Config`'s, copied by `newRaft`, never written), no read-index request pending; the log's boundary at
`base0` (never compacted), no snapshot pending or lent, no `MsgSnap` queued. -/
def RnScope (rs : RNState) (s : NState) : Prop :=
  rs.mode = .static ∧ s.prevote = false ∧ s.cq = false ∧ s.rd.pend = [] ∧
  rs.slent = none ∧ s.logst.prev = base0 ∧ s.logst.snap = none ∧
  ∀ m ∈ s.outbox, m.ty ≠ .snap

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

/-- **The harness's scope, owned part**: at `sc = true` `RnScope` and the storage never compacted past
`0` (`storCapF`, persistent); nothing at `sc = false`. -/
def rnScopeAt (sc : Bool) (rs : RNState) (s : NState) : IProp GF :=
  if sc then iprop(⌜RnScope rs s⌝ ∗ storCapF s.logst.storage 0) else iprop(emp)

/-- **A `RawNode` at its protocol state** (see the file header): `ownRawNode`'s body, conjunct for
conjunct, but `"Hpend"` with the queued states named (`pendAt`), and three conjuncts more: the
protocol reading `toPState s = ps`, the in-progress boundary `ip + 1 = offsetInProgress`, and the
harness's scope at `sc` (`rnScopeAt`). -/
def ownRawNodeAt (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (ps : PState) (qs : List Msg)
    (ip : Nat) (sc : Bool) : IProp GF :=
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
  "%Hps" ∷ ⌜toPState s = ps⌝ ∗
  "%Hip" ∷ ⌜uint.nat s.logst.inprogress = ip + 1⌝ ∗
  "Hsc" ∷ rnScopeAt sc rs s)

/-- **Forgetting the protocol state** (design §2.1, `ownRawNodeAt_ownRawNode`): at any scope flag.
By unfolding: `pendAt` gives `pendList`, the rest is `ownRawNode`'s body. -/
abbrev ownRawNodeAt_ownRawNode.law : Prop :=
  ∀ (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (ps : PState) (qs : List Msg) (ip : Nat)
    (sc : Bool),
    ownRawNodeAt (GF := GF) γ rn id rs ps qs ip sc ⊢ ownRawNode γ rn id rs

/-- **Naming the protocol state** (design §2.1, `ownRawNode_at`): every `ownRawNode` is an
`ownRawNodeAt` outside the harness's scope (`sc = false`), at its node's protocol reading, its
queue's messages and its in-progress boundary (`offsetInProgress ≥ 1`: `Hipb`'s `offset ≤`). -/
abbrev ownRawNode_at.law : Prop :=
  ∀ (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState),
    ownRawNode (GF := GF) γ rn id rs ⊢
      ∃ (ps : PState) (qs : List Msg) (ip : Nat), ownRawNodeAt γ rn id rs ps qs ip false

end rawnode_at

end EtcdGrove
end Perennial
