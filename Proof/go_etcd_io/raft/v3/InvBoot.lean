/-
The predicates of a new cluster's start (raft v3.7 retarget, stage R8b, D12: `notes/decisions.md`,
"The new cluster's start: the bootstrap log in raft's model"): what `RawNode.Bootstrap`,
`setupNode` and `StartNode` are specified over, beside the protocol side's `bootPState`,
`BootLogOk` and `ownRaftGhost_alloc_boot` (`Protocol/Facts.lean`).

* `rawNodeFresh rn id si V sdr pre s`: the `RawNode` `NewRawNode` builds on an empty storage, left
  open (`NewRawNode.spec`'s result since 2026-10-16, at any conf state, the voters `V`; a new
  cluster's is **empty**, `V = ∅`): the struct's fields as `ownRawNode` keeps them, the raft
  struct as `ownRaftPhys V` at a state `s` refining the protocol's initial state, nothing
  applied, handed out or pending. Not `ownRawNode`, which demands the ghost state (and, in the
  static mode, its configuration with the node among the voters): `RestartNode` closes it with
  the ghost state; `Bootstrap` installs the peers first.
* `peersCtx pv ctxs`: the `Context` bytes of the `Peer` values, read-only (the `ConfChange`
  literal shares the slice, and `ownCCV1` holds the bytes at `□`).
* `bootMarshal ps ctxs bootLog`: `proto.Marshal` of the `k`-th peer's `ConfChange`
  (`{Type: AddNode, NodeId: ps[k], Context: ctxs[k]}`, `Id` unset) returns the bytes of
  `bootLog[k]` -- the premise of `Bootstrap`/`StartNode` that ties the bytes the Go code
  computes to the log `RaftNames.reBoot` fixes before the call. `proto.MarshalConfChange.spec`
  (the trust boundary) says only that the bytes decode back to the change, with no pure
  encoder: the determinism of `Marshal` at these inputs is a fact of protobuf discharged where
  the node is composed (every member marshals the same changes), in the style of
  `RestartNode.spec`'s `InitialState` premise.
-/
module

public import Proof.go_etcd_io.raft.v3.ApiVocab
public import Proof.go_etcd_io.raft.v3.InvRawnode
public import Proof.go_etcd_io.raft.v3.Protocol.Facts
public import Spec.go_etcd_io.raft.v3.raft__applyConfChange
-- (2026-10-25, T-M M2a) `rboot`, `ownRaftGhostR`: a new cluster in the dynamic mode
public import Proof.go_etcd_io.raft.v3.Protocol.ResultsDyn

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The `RawNode` at `rn` of the node `id` that `NewRawNode` built on an empty storage (see the
file header; since 2026-10-16, stage R8b, `NewRawNode.spec`'s result at any conf state, the voters
`V`): the raft struct at the state `s`, which refines the protocol's initial state, over the
voters `V` (which it tracks, and no learner); its log empty, nothing applied (`applied = applying
= 0`), nothing handed out, no snapshot pending, the storage `si`; no ghost lower bound, pre-vote as
the `Config` says (`pre`; until 2026-10-17 off), `StepDownOnRemoval` as the `Config` says (`sdr`). The `RawNode`'s own fields as `ownRawNode`
keeps them: `asyncStorageWrites` unset, `prevSoftSt` and `prevHardSt` read-only, `stepsOnAdvance`
empty. `RestartNode` closes it (`ownRawNode`, with the ghost state); `Bootstrap` installs the
peers first. (2026-10-19, D21 M2r) Leader transfer `xf` (`NGhost.xf`): off as `newRaft` builds
it (`true`, the default), on after `rawNodeFresh_xf_off` (`RestartNode`'s). -/
def rawNodeFresh (rn : Loc) (id : w64) (si : GoInterfaceOk) (V : GSet w64) (sdr : Bool)
    (pre : Bool) (s : NState) (xf : Bool := true) : IProp GF :=
  iprop(∃ (rnv : RawNode) (sv : SoftState) (hprev : HardStateM),
    "Hrn" ∷ rawNodeOwn rn rnv ∗
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
      s.logst.snap = none ∧ s.logst.storage = interface.ok si⌝ ∗
    "%Hgh" ∷ ⌜s.gh = { xf := xf }⌝ ∗
    "%Hpvoff" ∷ ⌜s.prevote = pre⌝ ∗
    "%Hsdr" ∷ ⌜s.sdr = sdr⌝ ∗
    "%Hdom" ∷ ⌜domSet s.progress = V⌝ ∗
    -- (D22l) `prevHardSt` the zero record (`r.hardState()` at term `0`, nothing committed)
    "%Hhz" ∷ ⌜hprev = hsZero⌝)

/-- Closing `rawNodeFresh`: the pure facts first, the resources in the order of the definition. -/
theorem rawNodeFresh_intro (rn : Loc) (id : w64) (si : GoInterfaceOk) (V : GSet w64) (sdr : Bool)
    (pre : Bool) (s : NState) (rnv : RawNode) (sv : SoftState) (hprev : HardStateM)
    (Hasync : rnv.asyncStorageWrites' = false) (Hrel : NStateRel s initPState)
    (Hterm0 : s.term = W64 0 ∧ s.vote = W64 0 ∧ s.role = .follower ∧ s.outbox = [] ∧
      s.rd.states = [] ∧ s.rd.pend = [])
    (Hlog : s.logst.prev = entryID.mk (W64 0) (W64 0) ∧ s.logst.sents = [] ∧
      s.logst.uents = [] ∧ s.logst.stored = [] ∧ s.logst.committed = W64 0 ∧
      s.logst.applied = W64 0 ∧ s.logst.applying = W64 0 ∧ s.logst.unpersisted = [] ∧
      s.logst.snap = none ∧ s.logst.storage = interface.ok si)
    (Hgh : s.gh = {}) (Hpvoff : s.prevote = pre) (Hsdr : s.sdr = sdr)
    (Hdom : domSet s.progress = V) (Hhz : hprev = hsZero) :
    ⊢ rawNodeOwn (GF := GF) rn rnv -∗ ownRaftPhys V rnv.raft' id s -∗
      rnv.prevSoftSt' ↦□ sv -∗ hsRO rnv.prevHardSt' hprev -∗
      rnv.stepsOnAdvance' ↦* ([] : List Loc) -∗
      ownSliceCap Loc rnv.stepsOnAdvance' (DFrac.own 1) -∗
      rawNodeFresh rn id si V sdr pre s := by
  iintro Hrn Hphys #Hsoft #Hhard Hsteps Hcap
  unfold rawNodeFresh
  iexists rnv, sv, hprev
  simp only [named]
  iframe Hrn Hphys Hsoft Hhard Hsteps Hcap
  ipureintro
  exact ⟨Hasync, Hrel, Hterm0, Hlog, Hgh, Hpvoff, Hsdr, Hdom, Hhz⟩

/-- (2026-10-19, D21 M2r) Leader transfer turned on in a fresh node (a ghost step,
`ownRaftPhys_xf_off`): `RestartNode`'s, out of the no-snapshot mode. (2026-10-19, D22 S-a) Set to
`b`, the cluster's no-transfer mode (`RaftNames.reNoXfer`): kept off, or turned on. -/
theorem rawNodeFresh_set_xf (rn : Loc) (id : w64) (si : GoInterfaceOk) (V : GSet w64) (sdr : Bool)
    (pre : Bool) (s : NState) (b : Bool) :
    rawNodeFresh (GF := GF) rn id si V sdr pre s ⊢
      ∃ s', rawNodeFresh rn id si V sdr pre s' b := by
  iintro H
  cases b with
  | true => iexists s; iexact H
  | false =>
    iunfold rawNodeFresh at H
    icases H with ⟨%rnv, %sv, %hprev, H⟩
    iNamed H
    ihave Hphys := ownRaftPhys_xf_off V rnv.raft' id s $$ Hphys
    iexists { s with gh := { s.gh with xf := false } }
    iunfold rawNodeFresh
    iexists rnv, sv, hprev
    simp only [named]
    iframe Hrn Hphys Hsoft Hhard Hsteps Hsteps_cap
    ipureintro
    exact ⟨Hasync, Hrel, Hterm0, Hlog, by show { s.gh with xf := false } = _; rw [Hgh], Hpvoff, Hsdr, Hdom, Hhz⟩

-- (2026-10-26, raft's signature, stage 1) `peersCtx` moved to `Proof.go_etcd_io.raft.v3.ApiVocab`.

-- (2026-10-26, raft's signature, stage 1) `peersCtx_persistent` moved to `Proof.go_etcd_io.raft.v3.ApiVocab`.

-- (2026-10-26, raft's signature, stage 1) `bootMarshal` moved to `Proof.go_etcd_io.raft.v3.ApiVocab`.

-- (2026-10-26, raft's signature, stage 1) `bootMarshal_persistent` moved to `Proof.go_etcd_io.raft.v3.ApiVocab`.

-- (2026-10-26, raft's signature, stage 1) `bootInit` moved to `Proof.go_etcd_io.raft.v3.ApiVocab`.

/-- The commit invariant, from the boot ghost state in either mode. -/
theorem bootInit_inv (γ : RaftNames) (md : RNMode) (id : w64) (V : GSet w64)
    (bootLog : List EntryM) : ⊢ bootInit (GF := GF) γ md id V bootLog -∗ raftCommitInv γ := by
  cases md with
  | static =>
    unfold bootInit
    iintro Hg
    iapply ownRaftGhost_inv γ id (bootPState bootLog) $$ Hg
  | dyn dec c0 h0 _ =>
    unfold bootInit ownRaftGhostR
    iintro ⟨-, Hg, -⟩
    iapply ownRaftGhost_inv_md γ id _ $$ Hg

end defs

/-! ## The pure side of `Bootstrap` (2026-10-16, stage R8b) -/

section pure
variable [ext : FfiSyntax] [go_gctx : GoGlobalContext] [GoSemanticsFunctions]

/-- `Bootstrap`'s change of the peer `p` (`AddNode p` as `(&pb.ConfChange{...}).AsV2()` renders
it) at the voters `V`, `p` not a voter yet: `p` joins the voters, no learner. -/
theorem bootCC_apply (V : GSet w64) (p : w64) (hp : p ≠ W64 0) :
    ccApplyM (W32 0) [addNodeCC p] (cfgStateC (CfgM.simple V ∅)) =
      some (cfgState (<[p := ()]> V) ∅) := by
  rw [cfgStateC_simple, ccApplyM_single_simple]
  exact simpleM_cfgState_addNode V ∅ p hp (GMap.not_elem_of_empty _)
    (fun k hk => absurd hk (GMap.not_elem_of_empty _))

/-- The configuration `applyConfChange` returns for the voters `V` and no learner, as a `CfgM`. -/
theorem cfgState_cfg (V : GSet w64) : (cfgState V ∅).cfg = CfgM.simple V ∅ := rfl

/-- Its tracked ids: the voters. -/
theorem cfgState_ids (V : GSet w64) : (cfgState V ∅).cfg.ids = V := by
  rw [cfgState_cfg]; unfold CfgM.ids; rw [CfgM.voters_simple]
  exact GMap.map_union_empty _

/-- The voters after the `k`-th peer: the previous ones and `ps[k]`. -/
theorem listToSet_take_succ (ps : List w64) (k : Nat) (p : w64) (h : ps[k]? = some p) :
    GMap.listToSet (ps.take (k + 1)) = <[p := ()]> (GMap.listToSet (ps.take k)) := by
  have Ht : ps.take (k + 1) = ps.take k ++ [p] := by
    rw [List.take_succ, h]; rfl
  apply GMap.set_eq; intro x
  rw [Ht, GMap.elem_of_list_to_set, List.mem_append, List.mem_singleton, gset_mem_insert,
    GMap.elem_of_list_to_set]
  exact Or.comm

/-- `applyConfChange` at a non-leader (2026-10-16, stage R8b, for `Bootstrap`'s loop): only the
progress map, the `Progress` values and `isLearner` change -- the protocol state, the log and
`r.step`/`r.tick` do not. -/
theorem applyCCOkC_nonleader (c' : CfgM) (id : w64) (s s' : NState) (H : ApplyCCOkC c' id s s')
    (Hr : s.role ≠ .leader) :
    ∃ (prs : GMap w64 Loc) (pvs : GMap w64 Progress),
      s' = { s with progress := prs, prvals := pvs, isLearner := learnerOfC c' id } := by
  obtain ⟨prs, pvs, -, -, Hsw⟩ := H
  unfold SwitchOkC at Hsw
  rw [ite_eq_right (show ¬ ({ s with progress := prs, prvals := pvs, isLearner := learnerOfC c' id } :
    NState).role = .leader from Hr)] at Hsw
  exact ⟨prs, pvs, Hsw⟩

/-- The state `Bootstrap` leaves refines the bootstrap state `bootPState bootLog`
(`Protocol/Facts.lean`): a follower at term `1` with no vote, no leader, an empty tally and
outbox, the log `bootLog` from the empty base, committed through it, and a fresh read-only
object. -/
theorem boot_post_rel (bootLog : List EntryM) (s : NState) :
    NStateWf s →
    s.term = W64 1 → s.vote = W64 0 → s.lead = W64 0 → s.role = .follower →
    s.votes = ∅ → s.outbox = [] →
    s.logst.prev = entryID.mk (W64 0) (W64 0) → s.logst.sents = [] → s.logst.uents = bootLog →
    s.logst.committed = W64 bootLog.length →
    s.rd.states = [] → s.rd.pend = [] →
    NStateRel s (bootPState bootLog) := by
  intro Hwf Ht Hv Hl Hr Hvs Ho Hp Hse Hue Hc Hst Hpd
  refine ⟨?_, Hwf⟩
  simp [toPState, bootPState, initPState, Ht, Hv, Hl, Hr, Hvs, Ho, Hp, Hse, Hue, Hc, proleRole, rdNL]
  cases h : s.rd
  simp_all

end pure

end EtcdGrove
end Perennial
