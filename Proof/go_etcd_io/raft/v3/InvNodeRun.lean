/-
Lean-first (no Rocq counterpart).

# `node.run`'s lemmas (2026-10-10)

What `run` (`Proof/node__run.lean`) needs of the `RawNode` it owns, beyond the `RawNode`
methods' specs: `run` also reads the raft struct directly (`r := n.rn.raft`): the leader
(`r.lead`, `r.Term` for its log line: `ownRawNode_lead` and the like, for each of the three
forms the node is in), the tracker's progress map (`ownRawNode_borrow`); and it calls
`r.Step` itself (`wp_rn_raft_Step_net`, `wp_rn_raft_Step_prop`, `RawNode.Step`'s and
`RawNode.Propose`'s calls of `raft.Step` on `ownRawNode`). A `Ready` it abandons stays
armed (`ownRawNodeReady_abandon_keep`: what of it `ownRawNodeIdle_ready` takes again), and
the tick channel's receive hands over a credit (`tick_rcv_au`).

**Raft v3.7 (2026-10-16, stage R5 of the retarget, `notes/decisions.md`, "The node layer over
pointer messages").** Ported from the old proof's file. What changed: `ownRawNode`'s conjuncts
(`Hhard`, the queue `pendList`, no `pendingOwn`); `ownRawNodeReady`'s handed-out messages are
`List QMsg` (D8) and `ownRawNodeReady_abandon_keep` takes them back at `readyDq`; `r.Step` takes
a message pointer, owned (`msgIn`), with the facts over its state (`wp_rn_raft_Step_net`: `NetMsgOk
id st`; `wp_rn_raft_Step_prop`: a stamped proposal, `st.msg.From' = id`, no proposed slices'
invariant: a conf-change entry's bytes are on the record, `propData_ccEnts` pure);
`r.applyConfChange` takes a `*pb.ConfChangeV2` (`ownCCV2`, given back) and returns a fresh
`*pb.ConfState` (`csPts cs 1 … true`); the run loop's states over the new `Ready` fields
(`staleOk`/`freshOk`: `hsOpt`, `entsRO`, `readStatesPts`, `rd.Snapshot' = null`, the messages
handed out owned).
-/
module

public import Proof.go_etcd_io.raft.v3.InvNode
public import Spec.go_etcd_io.raft.v3.raft__Step
public import Spec.go_etcd_io.raft.v3.raft__applyConfChange
public import Proof.go_etcd_io.raft.v3.InvRawnodeC
-- `Step.commit_mono`
public import Proof.go_etcd_io.raft.v3.Protocol.Facts

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3
open RawNodeOwnAccess

/-! ## Slices of length zero -/

section slices
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]

/-- What a slice's points-to says of the slice value alone: enough to make it again at
length zero (`ownSlice_of_shape`). -/
def SliceShape (s : GoSlice) (k : Nat) : Prop :=
  (s = slice.nil ∧ k = 0) ∨
  (s.ptr ≠ null ∧ sint.Z s.len = k ∧ sint.Z s.len ≤ sint.Z s.cap)

theorem ownSlice_shape (s : GoSlice) (dq : DFrac) (vs : List V) :
    (s ↦*{dq} vs : IProp GF) ⊢ ⌜SliceShape s vs.length⌝ := by
  iintro H
  ihave %Hlen := ownSlice_len s dq vs $$ H
  rw [ownSlice_unseal]; unfold ownSliceDef
  icases H with (%H | ⟨H, %Hc⟩)
  · ipureintro; left; exact ⟨H.1, by rw [H.2]; rfl⟩
  · ihave %Hnn := typedPointsto_not_null _ _ _ $$ H
    ipureintro
    right
    refine ⟨Hnn, ?_, Hc⟩
    rw [Hlen.1, show sint.nat s.len = (sint.Z s.len).toNat from rfl]
    have := Hlen.2
    omega

theorem ownSlice_of_shape (s : GoSlice) (dq : DFrac) (h : SliceShape s 0) :
    ⊢ (s ↦*{dq} ([] : List V) : IProp GF) := by
  rcases h with ⟨rfl, -⟩ | ⟨Hnn, Hl, Hc⟩
  · iapply ownSlice_nil
  · iapply ownSlice_empty dq s (by omega) (by omega)
    rw [show sint.Z s.len = 0 by omega] at *
    iapply array_empty _ _ Hnn

end slices

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-! ## The leader fields -/

/-- `r.lead` and `r.Term`, out of the raft struct and back. -/
theorem ownRaftPhys_lead (c : CfgM) (r : Loc) (id : w64) (s : NState) :
    ⊢ ownRaftPhysCV (GF := GF) c c.voters r id s -∗
      r.[raft, go!"lead"] ↦ s.lead ∗ r.[raft, go!"Term"] ↦ s.term ∗
      (r.[raft, go!"lead"] ↦ s.lead -∗ r.[raft, go!"Term"] ↦ s.term -∗
        ownRaftPhysCV c c.voters r id s) := by
  iintro H
  -- STAGED: no witness yet (`ownRaftPhysC_wit0`)
  icases ownRaftPhysC_wit0 c _ _ _ $$ H with ⟨%hw, H⟩
  icases ownRaftPhysC_view c r id s hw $$ H with ⟨%rss, %sl1, %sl2, %ms1, %ms2, Hv⟩
  iNamed Hv
  isplitl [Hf_lead]
  · iexact Hf_lead
  isplitl [Hf_Term]
  · iexact Hf_Term
  iintro Hl Ht
  ihave H := Hclose $$ %sl1 %sl2 %ms1 %ms2 %s.outbox %s.logst %s.gh %rss %s.rd Ht Hf_Vote
    Hf_readStates HreadStates HreadStates_cap %(And.intro rfl rfl) Hf_raftLog Hf_state Hl Hf_witnessMsgs Hf_msgs Hmsgs Hmsgs_cap Hf_msgsAA HmsgsAA HmsgsAA_cap Houtbox
    %HmsgsAA_ok %Hout_term %Hgh_out %(Hgh_unst.1) %(⟨rfl, Hgh_unst.2, fun _ h => h⟩) %(fun _ => Int.le_refl _) %Hxf Hlog
  iapply ownRaftPhysC_eq c r id _ _ (by cases s; rfl) $$ H

/-- The raft struct out of the node (`r` is the node's raft pointer), and back. -/
theorem ownRawNode_borrow (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (r : Loc) :
    ⊢ ownRawNode (GF := GF) γ rn id rs -∗ rn.[RawNode, go!"raft"] ↦□ r -∗
      ∃ (c : CfgM) (s : NState), ownRaftPhysCV c c.voters r id s ∗
        (ownRaftPhysCV c c.voters r id s -∗ ownRawNode γ rn id rs) := by
  iintro H #Hr
  iNamed H
  ihave #Hr' := rawNodeOwn_raft rn rnv $$ Hrn
  icombine Hr Hr' gives %Heq
  subst Heq
  iexists cf, s
  isplitl [Hphys]
  · iexact Hphys
  iintro Hphys
  iapply ownRawNode_intro γ rn id rs s cf fp rnv sv hprev steps Hwf Hin Hal Hasync Hdlen Hunp Hsnap
    Hstok Htrm Hstor Hpvoff Hrs_out Hrs_unst Hrs_clb Hrnfl
    $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hsteps_cap Hpend Hdeliv Hstrecs

theorem ownRawNodeIdle_borrow (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (r : Loc) :
    ⊢ ownRawNodeIdle (GF := GF) γ rn id rs -∗ rn.[RawNode, go!"raft"] ↦□ r -∗
      ∃ (c : CfgM) (s : NState), ownRaftPhysCV c c.voters r id s ∗
        (ownRaftPhysCV c c.voters r id s -∗ ownRawNodeIdle γ rn id rs) := by
  iintro H #Hr
  iNamed H
  ihave #Hr' := rawNodeOwn_raft rn rnv $$ Hrn
  icombine Hr Hr' gives %Heq
  subst Heq
  iexists cf, s
  isplitl [Hphys]
  · iexact Hphys
  iintro Hphys
  iapply ownRawNodeIdle_intro γ rn id rs s cf fp rnv sv hprev steps Hwf Hin Hal Hasync Hdlen Hunp
    Hsnap Hstok Htrm Hstor Hpvoff Hrs_out Hrs_unst Hrs_clb Hrnfl Hidle
    $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hsteps_cap Hpend Hdeliv Hstrecs

/-- The fields of the raft struct `isNode` shares, out of a node. -/
theorem ownRawNode_shared (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) :
    ⊢ ownRawNode (GF := GF) γ rn id rs -∗
      ∃ (r : Loc) (lok : GoInterfaceOk), rn.[RawNode, go!"raft"] ↦□ r ∗
        r.[raft, go!"id"] ↦□ id ∗ r.[raft, go!"logger"] ↦□ (interface.ok lok : GoInterface) ∗
        isLogger lok ∗ ownRawNode γ rn id rs := by
  iintro H
  iNamed H
  ihave #Hr := rawNodeOwn_raft rn rnv $$ Hrn
  icases ownRaftPhysC_shared cf rnv.raft' id s $$ Hphys with
    ⟨%lok, #Hid, #Hlg, #Hlogger, Hphys⟩
  iexists rnv.raft', lok
  iframe Hr Hid Hlg Hlogger
  iapply ownRawNode_intro γ rn id rs s cf fp rnv sv hprev steps Hwf Hin Hal Hasync Hdlen Hunp Hsnap
    Hstok Htrm Hstor Hpvoff Hrs_out Hrs_unst Hrs_clb Hrnfl
    $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hsteps_cap Hpend Hdeliv Hstrecs

/-- The leader fields, for `run`'s check (any values: the check only logs and arms the
proposal channel). -/
def leadFields (r : Loc) (X : IProp GF) : IProp GF :=
  iprop(∃ (ld t : w64), r.[raft, go!"lead"] ↦ ld ∗ r.[raft, go!"Term"] ↦ t ∗
    (r.[raft, go!"lead"] ↦ ld -∗ r.[raft, go!"Term"] ↦ t -∗ X))

theorem ownRawNode_lead (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (r : Loc) :
    ⊢ ownRawNode (GF := GF) γ rn id rs -∗ rn.[RawNode, go!"raft"] ↦□ r -∗
      leadFields r (ownRawNode γ rn id rs) := by
  iintro H #Hr
  icases ownRawNode_borrow γ rn id rs r $$ H Hr with ⟨%c, %s, Hphys, Hback⟩
  icases ownRaftPhys_lead c r id s $$ Hphys with ⟨Hl, Ht, Hclose⟩
  unfold leadFields
  iexists s.lead, s.term
  iframe Hl Ht
  iintro Hl Ht
  iapply Hback
  iapply Hclose $$ Hl Ht

theorem ownRawNodeIdle_lead (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (r : Loc) :
    ⊢ ownRawNodeIdle (GF := GF) γ rn id rs -∗ rn.[RawNode, go!"raft"] ↦□ r -∗
      leadFields r (ownRawNodeIdle γ rn id rs) := by
  iintro H #Hr
  icases ownRawNodeIdle_borrow γ rn id rs r $$ H Hr with ⟨%c, %s, Hphys, Hback⟩
  icases ownRaftPhys_lead c r id s $$ Hphys with ⟨Hl, Ht, Hclose⟩
  unfold leadFields
  iexists s.lead, s.term
  iframe Hl Ht
  iintro Hl Ht
  iapply Hback
  iapply Hclose $$ Hl Ht

theorem ownRawNodeReady_lead (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (rd : Ready)
    (ce es : List EntryM) (ms : List QMsg) (h : Bool) (r : Loc) :
    ⊢ ownRawNodeReady (GF := GF) γ rn id rs rd ce es ms h -∗ rn.[RawNode, go!"raft"] ↦□ r -∗
      leadFields r (ownRawNodeReady γ rn id rs rd ce es ms h) := by
  iintro H #Hr
  iunfold ownRawNodeReady at H
  icases H with ⟨%s, %cf, %fp, %rnv, %sv, %hprev, H⟩
  iNamed H
  ihave #Hr' := rawNodeOwn_raft rn rnv $$ Hrn
  icombine Hr Hr' gives %Heq
  subst Heq
  iunfold ownRaftPhysReady at Hphys
  icases Hphys with ⟨%rsl, %sl1, %sl2, %ms1, %ms2, Hphys⟩
  iNamed Hphys
  unfold leadFields
  iexists s.lead, s.term
  isplitl [Hf_lead]
  · iexact Hf_lead
  isplitl [Hf_Term]
  · iexact Hf_Term
  iintro Hf_lead Hf_Term
  iunfold ownRawNodeReady
  iexists s, cf, fp, rnv, sv, hprev
  simp only [named]
  iframe Hrn Hghost Hsdrf Hout Hsoft Hhard Hsteps Hsteps_cap Hcommitted Hstrecs Hrdsoft Hrdhard
    Hrdrs Hce Hce_cap Hents
  isplitl
  · iunfold ownRaftPhysReady
    iexists rsl, sl1, sl2, ms1, ms2
    simp only [named]
    iframe Hf_id Hf_Term Hf_Vote Hf_readStates HreadStates HreadStates_cap Hf_raftLog Hf_state
      Hf_lead Hf_witnessMsgs Hf_msgs Hf_msgsAA HmsgsAA HmsgsAA_cap Hself Hother Hlog Hundo Hclose
    ipureintro
    exact ⟨Houtbox, HmsgsAA_ok, Hout_term, Hgh_out, Hgh_unst, Hxf, Hmslen⟩
  ipureintro
  exact ⟨Hwf, Hin, Hal, Hasync, Hdlen, Hunp, Hsnap, Htrm, Hstor, Hpvoff, Hrs_out, Hrs_unst,
    Hrs_clb, Hrnfl, Hrdz, Hceok, Hes, Hrdc, Hprc, Hnsout⟩

/-! ## Abandoning a `Ready`, keeping it armed -/

/-- `ownRawNodeReady_abandon`, also giving back what of the `Ready` `ownRawNodeIdle_ready`
takes should `run` send it after all: its committed entries' capacity and its soft
state. (2026-10-16, stage R5: and its hard state; the messages handed out come back at
`readyDq` with `rd.Messages`' slice and capacity.) -/
theorem ownRawNodeReady_abandon_keep (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState)
    (rd : Ready) (ce es : List EntryM) (ms : List QMsg)
    (Hsteps0 : rs.steps = []) (Hunp0 : rs.unpersisted = []) :
    ⊢ rd.Messages' ↦* ms.map QMsg.loc -∗ ownSliceCap Loc rd.Messages' (DFrac.own 1) -∗
      ([∗list] q ∈ ms, msgOwn q.loc (readyDq q.st) q.st) -∗
      ownRawNodeReady (GF := GF) γ rn id rs rd ce es ms -∗
      ownSliceCap Loc rd.CommittedEntries' (DFrac.own 1) ∗
      (⌜rd.SoftState' = null⌝ ∨ ∃ v : SoftState, rd.SoftState' ↦□ v) ∗
      (∃ hrd : HardStateM, hsOpt rd.HardState' hrd) ∗
      ∃ (n : Nat) (u : Bool) (c : w64),
        ⌜ms.length ≤ n ∧ (es ≠ [] → u = true) ∧
         (∀ e, ce.getLast? = some e → uint.Z e.Index' ≤ uint.Z c ∧
           uint.Z e.Index' = (rs.delivered.length : Int) + (ce.length : Int))⌝ ∗
        ownRawNode γ rn id { rs with outlb := n, unst := u, clb := c } := by
  iintro Hmsgs Hmsgs_cap Hown H
  iunfold ownRawNodeReady at H
  icases H with ⟨%s, %cf, %fp, %rnv, %sv, %hprev, H⟩
  iNamed H
  isplitl [Hce_cap]
  · iexact Hce_cap
  isplitr
  · iexact Hrdsoft
  isplitr
  · iexact Hrdhard
  iunfold ownRaftPhysReady at Hphys
  icases Hphys with ⟨%rsl, %sl1, %sl2, %ms1, %ms2, Hphys⟩
  iNamed Hphys
  icases Hundo $$ Hmsgs Hmsgs_cap Hown with ⟨Hm1, Hc1, Hown1, Hhalf⟩
  ihave Hoth := (qOwns_other_halves id ms2).1 $$ [Hhalf Hother]
  · iframe Hhalf Hother
  ihave Hown2 := (qOwns_self_split id ms2).2 $$ [Hself Hoth]
  · iframe Hself Hoth
  ihave Hob := outboxRel_join s.outbox ms1 ms2 $$ [Hown1 Hown2]
  · iframe Hown1 Hown2; ipureintro; exact Houtbox
  simp only [Bool.false_eq_true, ↓reduceIte]
  let g : NGhost := { outlb := ms1.length + ms2.length,
                      unst := decide (nextUnstable s.logst ≠ []), tc := s.gh.tc, ns := s.gh.ns, xf := s.gh.xf }
  ihave Hphys := Hclose $$ %sl1 %sl2 %ms1 %ms2 %s.outbox %s.logst %g %rsl %s.rd Hf_Term Hf_Vote
    Hf_readStates HreadStates HreadStates_cap %(And.intro rfl rfl)
    Hf_raftLog Hf_state Hf_lead Hf_witnessMsgs Hf_msgs Hm1 Hc1 Hf_msgsAA HmsgsAA HmsgsAA_cap
    Hob %HmsgsAA_ok %Hout_term %(Nat.le_refl _)
    %(fun h => .inl (of_decide_eq_true h))
    %(⟨rfl, fun _ => ⟨rfl, rfl, rfl, Int.le_refl _⟩, fun _ h => h⟩ :
      g.ns = s.gh.ns ∧ LogNsKeep s s.logst ∧ ∀ m ∈ s.outbox, m ∈ s.outbox)
    %(fun _ => Int.le_refl _) %(Hxf.of_fields rfl rfl rfl rfl) Hlog
  ihave #Hdeliv : isCommitted γ rs.delivered $$ []
  · iapply isCommitted_mono γ rs.delivered (rs.delivered ++ ce) (List.prefix_append _ _)
      $$ Hcommitted
  ihave Hpend : pendList γ id ([] : List Loc) rs.steps $$ []
  · rw [Hsteps0]; iapply pendList_nil
  iexists ms1.length + ms2.length, decide (nextUnstable s.logst ≠ []), s.logst.committed
  isplitr
  · ipureintro
    refine ⟨Hmslen, fun h => by rw [Hes] at h; exact decide_eq_true h, fun e He => ?_⟩
    obtain ⟨-, H2, H3⟩ := Hceok e He
    refine ⟨H2, ?_⟩
    rw [H3, Hdlen]
    have := uint_Z_nonneg s.logst.applying
    omega
  let rs' : RNState :=
    { rs with outlb := ms1.length + ms2.length, unst := decide (nextUnstable s.logst ≠ []),
              clb := s.logst.committed }
  let s' : NState := { s with outbox := s.outbox, logst := s.logst, gh := g }
  ihave Hghost := ownStepGhost_congr γ _ cf id (s := s) (s' := s') rfl rfl rfl rfl $$ Hghost
  iapply ownRawNode_intro γ rn id rs' s' cf fp rnv sv hprev [] Hwf Hin Hal Hasync Hdlen
    (Hunp0.trans Hunp.symm) Hsnap (by show StepsOk _ rs.steps; rw [Hsteps0]; trivial) Htrm
    Hstor Hpvoff rfl rfl
    (Int.le_refl _) ⟨Hrnfl.1, fun h => absurd Hrnfl.2 (Int.not_le.2 h)⟩
    $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hsteps_cap Hpend Hdeliv Hstrecs

/-! ## The tick channel -/

/-- A receive on `tickc` takes a buffered tick and its credit (`tickInv`). -/
theorem tick_rcv_au (γ : NodeNames) (Φ : Unit → Bool → IProp GF) :
    ⊢ inv tickN (tickInv (GF := GF) γ) -∗ £ 1 -∗ ▷ (tickCred γ.bud 1 -∗ Φ () true) -∗
      recvAu γ.tick Unit Φ := by
  iintro #Hinv Hlc Hcont
  unfold recvAu
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later $$ Hlc Hi with Hi
  unfold tickInv
  icases Hi with ⟨%l, Hoc, Hcr⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists .Buffered l
  iframe Hoc
  rcases l with _ | ⟨u, rest⟩
  · itrivial
  · iintro Hoc
    simp only [List.length_cons]
    icases (tickCred_split γ.bud rest.length 1).1 $$ Hcr with ⟨Hcr, H1⟩
    imod Hmask with -
    imod Hclose $$ [Hoc Hcr] with -
    · inext
      iexists rest
      iframe
    imodintro
    iapply Hcont $$ H1

end lemmas

/-! ## `r.Step`, on the node -/

section step
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

set_option hygiene false in
/-- A premise of `raft.Step` about a type a network message is not: vacuous. -/
local macro "not_net" : tactic => `(tactic| (intro h; first
  | (obtain h | h := h <;> (first | exact h.elim | (rw [h] at Hty; simp [netStepTypes,
  MsgApp, MsgAppResp, MsgVote, MsgVoteResp, MsgHeartbeat, MsgHeartbeatResp,MsgCheckQuorum, MsgHup,
  MsgPreVote, MsgPreVoteResp, MsgSnap, MsgBeat, MsgProp, MsgStorageAppendResp,
  MsgStorageApplyResp, MsgReadIndex, MsgReadIndexResp, MsgForgetLeader, MsgUnreachable, MsgSnapStatus, MsgTimeoutNow, MsgTransferLeader] at Hty)))
  | (first | exact h.elim | (rw [h] at Hty; simp [netStepTypes,
  MsgApp, MsgAppResp, MsgVote, MsgVoteResp, MsgHeartbeat, MsgHeartbeatResp,MsgCheckQuorum, MsgHup,
  MsgPreVote, MsgPreVoteResp, MsgSnap, MsgBeat, MsgProp, MsgStorageAppendResp,
  MsgStorageApplyResp, MsgReadIndex, MsgReadIndexResp, MsgForgetLeader, MsgUnreachable, MsgSnapStatus, MsgTimeoutNow, MsgTransferLeader] at Hty))))

/-- `r.Step(m)` on a message from the network, `r` the node's raft struct: the tail of
`RawNode.Step` (its guards are `run`'s own code). (2026-10-16, stage R5: the message is the
pointer `ml`, given for good as `raft.Step` takes it (`msgIn ml □ st`); the facts over its state
`st`.) -/
theorem wp_rn_raft_Step_net (wp_raft_Step : raft.Step.spec (GF := GF) (hG := hG))
    (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (r : Loc) (ml : Loc) (st : MsgSt)
    (Hok : NetMsgOk id st)
    -- (2026-10-17) as `RawNode.Step`'s: the ceiling covers the message's term and a transfer's
    -- campaign; a pre-vote request only after a bootstrap
    (Hmtc : uint.Z st.msg.Term' ≤ uint.Z rs.tc)
    (Htn : st.msg.Type' = MsgTimeoutNow →
      max (uint.Z rs.term) (uint.Z st.msg.Term') + 1 ≤ uint.Z rs.tc)
    (Hpvb : st.msg.Type' = MsgPreVote → γ.reBoot ≠ [])
    -- (D19i part 1) the floor not raised (a `MsgTimeoutNow` campaigns)
    (Hflw : rs.flw = false)
    -- (2026-10-19, D21 M2r) a transfer request only outside the cluster's no-snapshot mode
    (Hxt : st.msg.Type' = MsgTransferLeader → γ.reNoSnap = false) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        ownRawNode γ rn id rs ∗ rn.[RawNode, go!"raft"] ↦□ r ∗
        msgIn ml DFrac.discard st ∗
        □ (∀ ty, ⌜mtypeOf st.msg.Type' = some ty⌝ -∗
          isMessage γ (absMsg ty st.msg st.ents st.ctx)) ∗
        rdCred γ (if st.msg.Type' = MsgReadIndex then 1 else 0) ∗ £ 1 }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #ml))
    {{ (err : GoInterface) (t : w64), RET #err;
        ownRawNode γ rn id { rs with term := t } ∗
        ⌜uint.Z rs.term ≤ uint.Z t ∧ uint.Z t ≤ uint.Z rs.tc ∧
          (st.msg.Type' ≠ MsgPreVoteResp →
            uint.Z t ≤ max (uint.Z rs.term) (uint.Z st.msg.Term') +
              (if st.msg.Type' = MsgTimeoutNow then 1 else 0))⌝ }} := by
  rcases st with ⟨m, ents, sn, ctx, rsp⟩
  have Hok0 := Hok
  simp only [NetMsgOk] at Hok0 Htn Hmtc Hpvb Hxt ⊢
  obtain ⟨Hty, -⟩ := Hok0
  iintro %Φ ⟨#Hpkg, Hrn, #Hr, Hmin, #Hmsg, Hcred, Hlc⟩ HΦ
  iNamed Hrn
  ihave #Hr' := rawNodeOwn_raft rn rnv $$ Hrn
  icombine Hr Hr' gives %Heq
  subst Heq
  icases ownStepGhost_boot_term γ _ cf id s (m.Type' = MsgPreVote) Hpvb $$ Hghost
    with ⟨%Hb1, Hghost⟩
  icases ownStepGhost_nsLink γ _ cf id s $$ Hghost with ⟨%Hnl, Hghost⟩
  have HnP : m.Type' ≠ MsgProp := by not_net
  icases ownRaftPhysC_preFacts cf rnv.raft' id s (Hpvoff.dyn ⟨rs.capplied, rs.cfg, fp⟩) $$ Hphys with ⟨%Hpf, Hphys⟩
  wp_apply Hok.raftStep Hpvoff Htrm Hmtc Htn Hb1 (Hrnfl.1 Hflw) (fun h => Hnl.2.trans (Hxt h)) (wp_raft_Step cf _ γ _ id s ml m ents ctx sn rsp)
      Hwf
    (GMode.Pre.of_facts Hpf (by not_net) (by not_net)) (fun h => absurd h (by not_net))
    $$ [$Hphys $Hghost $Hlc Hmin Hcred]
  · simp only [HnP, ↓reduceIte, named]
    isplitl [Hmin]
    · isplitl [Hmin]
      · iexact Hmin
      isplitr
      · iempintro
      isplitr
      · ipureintro; not_net
      isplitr
      · ipureintro; not_net
      imodintro
      iintro %ty %Hty' _
      iapply Hmsg $$ %ty %Hty'
    isplitl [Hcred]
    · iexact Hcred
    imodintro
    iintro %h
    exfalso
    revert h
    not_net
  simp only [HnP]
  iintro %err %s' %c' %md' ⟨Hphys, Hghost, %Hwf', %Href, %Hcc, -, %Hfr, %Htm, %Hresp, -⟩
  have Hc := Href.commit_mono
  have e1 := Href.keep (by not_net) (by not_net); subst e1
  have e2 := Hcc (by not_net); subst c'
  obtain ⟨Ha, Hsn, Hu, Hpv, Hsd, Hsg, Hpre, Hgh, Hfl', Hap'⟩ := Hfr (by not_net) (by not_net)
  obtain ⟨Ht1, -, Ht3, -, Ht5, Hpcs⟩ := Htm (by not_net)
  have Ht3' : m.Type' ≠ MsgPreVoteResp → uint.Z s'.term ≤ max (uint.Z s.term) (uint.Z m.Term') +
      (if m.Type' = MsgTimeoutNow then 1 else 0) := by
    intro hpr
    by_cases h : m.Type' = MsgTimeoutNow
    · rw [ite_eq_left h]; exact Ht5 h
    · rw [ite_eq_right h]; have := Ht3 (by not_net) hpr h; omega
  have Hmtc' : uint.Z m.Term' ≤ uint.Z s.gh.tc := by rw [← Hpvoff.2.1]; exact Hmtc
  have Htc0 := Hpvoff.2.2.1
  have Hle : uint.Z s'.term ≤ uint.Z s.gh.tc := by
    by_cases hpr : m.Type' = MsgPreVoteResp
    · rcases (Hresp.2 hpr).1 with h | ⟨hp, h⟩
      · have := Int.max_le.2 ⟨Htc0, Hmtc'⟩; omega
      · have := Hpvoff.2.2.2 hp; omega
    · have h1 := Ht3' hpr
      by_cases h : m.Type' = MsgTimeoutNow
      · rw [ite_eq_left h] at h1
        have := Htn h; rw [Hpvoff.2.1, Htrm] at this; omega
      · rw [ite_eq_right h] at h1
        have := Int.max_le.2 ⟨Htc0, Hmtc'⟩; omega
  have Hstok' : StepsOk s' rs.steps := stepsOk_mono_le s s' _ Ht1 ⟨Hpv, Hsd⟩ Hc Ha (tc_le_of_gh Hgh) Hstok
  ihave #Hstr' := storedRecs_eq γ _ s'.logst.prev _ s'.logst.stored Hpv Hsd $$ Hstrecs
  iapply HΦ $$ %err %s'.term
  isplitl
  · iapply ownRawNode_intro γ rn id { rs with term := s'.term } s' cf fp rnv sv hprev steps Hwf'
      Hin Hal Hasync (by rw [Ha]; exact Hdlen) (by rw [Hu]; exact Hunp) (by rw [Hsn]; exact Hsnap)
      Hstok' rfl (by rw [Hsg]; exact Hstor)
      (Hpvoff.step rfl rfl Hpre Hgh Hle Hpcs (by not_net))
      (by rw [Hgh]; exact Hrs_out) (by rw [Hgh]; exact Hrs_unst) (Int.le_trans Hrs_clb Hc)
      (RNFl.keep Hrnfl Hfl' Hap' Ha)
      $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hsteps_cap Hpend Hdeliv Hstr'
  ipureintro
  rw [Htrm]
  exact ⟨Ht1, by rw [Hpvoff.2.1]; exact Hle, Ht3'⟩

/-- A premise of `Step` about another message type: `MsgProp` (`W32 2`) is not it. -/
local macro "msg_ne" : tactic => `(tactic| (intro Hc; simp [MsgHup, MsgVote, MsgVoteResp,
  MsgPreVote, MsgPreVoteResp, MsgApp, MsgHeartbeat, MsgAppResp, MsgHeartbeatResp,MsgCheckQuorum, MsgSnap,
  MsgBeat, MsgStorageAppendResp, MsgStorageApplyResp, propMsgM, MsgProp, MsgForgetLeader, MsgUnreachable, MsgSnapStatus, MsgTimeoutNow, MsgTransferLeader] at Hc))

set_option hygiene false in
/-- A premise of `Step` about another message type, for a message of type `MsgProp`
(`Hty` in context). -/
local macro "msg_ne'" : tactic => `(tactic| (intro Hc; rw [Hty] at Hc; simp [MsgHup, MsgVote,
  MsgVoteResp, MsgPreVote, MsgPreVoteResp, MsgApp, MsgHeartbeat, MsgAppResp, MsgHeartbeatResp,MsgCheckQuorum,
  MsgSnap, MsgBeat, MsgStorageAppendResp, MsgStorageApplyResp, MsgProp, MsgReadIndex,
  MsgReadIndexResp, MsgForgetLeader, MsgUnreachable, MsgSnapStatus, MsgTimeoutNow, MsgTransferLeader] at Hc))

/-- A proposal's abstraction is legitimately sent, from the node's: `isMessage` of a
proposal reads only its term and entries, not its sender (2026-10-10). (2026-10-16, stage R5:
on the message's scalars.) -/
theorem isMessage_propose_from (γ : RaftNames) (m : MessageM) (ents : List EntryM)
    (x : w64) :
    ⊢ isMessage (GF := GF) γ (absMsg .propose m ents) -∗
      isMessage γ (absMsg .propose { m with From' := x } ents) := by
  iintro H
  unfold isMessage absMsg absMsgFrom at *
  iexact H

/-- (2026-10-19, D21 M2r) A proposal's protocol fact ignores the message's context: a received
copy's (`isRaftMsg`, at its context) is `fwdP`'s (at none). -/
theorem isMessage_propose_ctx (γ : RaftNames) (m : MessageM) (ents : List EntryM) (ctx : List w8) :
    ⊢ isMessage (GF := GF) γ (absMsg .propose m ents ctx) -∗
      isMessage γ (absMsg .propose m ents) := by
  iintro H
  unfold isMessage absMsg absMsgFrom at *
  iexact H

theorem isMessage_propose_pure (γ : RaftNames) (m : MessageM) (ents : List EntryM) :
    ⊢ isMessage (GF := GF) γ (absMsg .propose m ents) -∗
      ⌜m.Term' = W64 0 ∧ ents ≠ [] ∧ (ents.length : Int) < 2 ^ 61⌝ := by
  unfold isMessage absMsg absMsgFrom
  iintro ⟨%H, -⟩
  ipureintro; exact H

/-- The proposal `Propose` builds is legitimately sent, given its entry's data. (2026-10-16,
stage R5: the records `propMsgM`, `propEntryM d`.) -/
theorem isMessage_propMsg (γ : RaftNames) (d : List w8) :
    ⊢ propData (GF := GF) γ (propEntryM d) -∗
      isMessage γ (absMsg .propose propMsgM [propEntryM d]) := by
  iintro #Hent
  unfold isMessage absMsg absMsgFrom
  isplitr
  · ipureintro
    exact ⟨rfl, List.cons_ne_nil _ _, by simp⟩
  iapply (BigSepL.bigSepL_singleton (Φ := fun _ e => propData (GF := GF) γ e)).2
  iexact Hent

-- (2026-10-16, stage R5, D6) `isNode_propDataInv` is gone with the proposed slices' invariant.

/-- A proposal's conf-change entries' bytes, from their data's records (2026-10-13): each
entry of a proposal has its data (`entData`), which for a conf-change entry are bytes that
decode as its type says (`CCDecodes`). What `raft.Step` needs of a proposal (`ccEntsOk`).
(2026-10-16, stage R5, D6: the bytes are the entry's, so no invariant and no update; until then
the proposed slices' invariant gave them.) -/
theorem propData_ccEnts (γ : RaftNames) (ents : List EntryM) :
    ([∗list] e ∈ ents, propData (GF := GF) γ e) ⊢ ∃ cs, ccEntsOk ents cs := by
  induction ents with
  | nil =>
    iintro -
    iexists []
    unfold ccEntsOk
    iapply (BigSepL2.bigSepL2_nil (Φ := fun _ e o => ccEntOk (GF := GF) e o)).2
    iempintro
  | cons e es ih =>
    iintro #Hes
    icases (BigSepL.bigSepL_cons (Φ := fun _ e => propData (GF := GF) γ e)).1 $$ Hes
      with ⟨#He, #Hes'⟩
    icases ih $$ Hes' with ⟨%cs, #Hcs⟩
    have Hone : ∀ o, (propDataIs (GF := GF) γ e o ⊢ ∃ c, ccEntOk e c) := by
      intro o
      cases o with
      | some d =>
        iintro He
        iunfold propDataIs at He
        icases He with ⟨%Hd, -⟩
        iexists none
        unfold ccEntOk
        ipureintro
        unfold IsConfEnt; rw [Hd.2.2]
        rintro (h | h) <;> revert h <;> word
      | none =>
        iintro He
        iunfold propDataIs at He
        icases He with (%Hz | %Hz)
        · iexists none
          unfold ccEntOk
          ipureintro
          unfold IsConfEnt; rw [Hz.1]
          rintro (h | h) <;> revert h <;> word
        · obtain ⟨-, Hdec, -⟩ := Hz
          by_cases H1 : e.Type' = W32 1
          · obtain ⟨m, Hm⟩ := Hdec.1 H1
            iexists some (.v1 m)
            simp only [ccEntOk]
            ipureintro; exact ⟨H1, Hm⟩
          by_cases H2 : e.Type' = W32 2
          · obtain ⟨m, Hm⟩ := Hdec.2 H2
            iexists some (.v2 m)
            simp only [ccEntOk]
            ipureintro; exact ⟨H2, Hm⟩
          iexists none
          unfold ccEntOk
          ipureintro
          rintro (h | h)
          · exact H1 h
          · exact H2 h
    iunfold propData at He
    icases He with ⟨%o, #He⟩
    icases (Hone o) $$ He with ⟨%c, #Hc⟩
    iexists c :: cs
    unfold ccEntsOk
    iapply (BigSepL2.bigSepL2_cons (Φ := fun _ e o => ccEntOk (GF := GF) e o)).2
    iframe Hc
    iexact Hcs

/-- `r.Step(m)` on a proposal (`m.From` set to the node's id, as `run` does), `r` the
node's raft struct: the batch owned, the proposal legitimately sent (its entries' data:
their updates deposited), its context. Either the one `Propose` built, or (2026-10-10)
one forwarded by a peer. (2026-10-16, stage R5: the message is the pointer `ml`, owned as
`raft.Step` takes a proposal (`msgIn ml 1 st`), already stamped (`Hfr`: `run` stores `From`
first, `msgPtsC_store_From`; `isMessage_propose_from` moves the abstraction); no proposed
slices' invariant (D6).) The error is `raft.Step`'s for a proposal (`"Herr"`): `nil` or
`ErrProposalDropped`, non-`nil` by `isInitialized` (`stepErr`; stage R7c, 2026-10-16). -/
theorem wp_rn_raft_Step_prop (wp_raft_Step : raft.Step.spec (GF := GF) (hG := hG))
    (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (r : Loc) (ml : Loc) (st : MsgSt)
    (Hty : st.msg.Type' = MsgProp) (Hfr : st.msg.From' = id) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        ownRawNode γ rn id rs ∗ rn.[RawNode, go!"raft"] ↦□ r ∗
        msgIn ml (DFrac.own 1) st ∗
        isMessage γ (absMsg .propose st.msg st.ents) ∗
        -- (2026-10-19, D21 M6) its entries' tickets
        ([∗list] e ∈ st.ents, entTk γ e) ∗ £ 1 }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #ml))
    {{ (err : GoInterface), RET #err; ownRawNode γ rn id rs ∗ stepErr err }} := by
  rcases st with ⟨m, ents, sn, ctx, rsp⟩
  simp only at Hty Hfr ⊢
  iintro %Φ ⟨#Hpkg, Hrn, #Hr, Hmin, #Hm, Htk, Hlc⟩ HΦ
  ihave #Hinit := isInitialized_access $$ Hpkg
  unfold isInitialized
  icases Hinit with ⟨%_, %_, %_, %_, %errPropDropped, %_, %_, %_, %_, %_, #Hinit⟩
  iNamed Hinit
  iNamed Hrn
  ihave #Hr' := rawNodeOwn_raft rn rnv $$ Hrn
  icombine Hr Hr' gives %Heq
  subst Heq
  ihave %Hpm := isMessage_propose_pure γ m ents $$ Hm
  obtain ⟨Hterm, Hne, Hlen⟩ := Hpm
  ihave #Hed : iprop([∗list] e ∈ ents, propData γ e) $$ []
  · iunfold isMessage at Hm
    simp only [absMsg, absMsgFrom]
    icases Hm with ⟨-, #Hed⟩
    iexact Hed
  icases propData_ccEnts γ ents $$ Hed with ⟨%cs, #Hcc⟩
  imod rdCred_zero_upd (GF := GF) γ with Hcr
  icases ownRaftPhysC_preFacts cf rnv.raft' id s (Hpvoff.dyn ⟨rs.capplied, rs.cfg, fp⟩) $$ Hphys with ⟨%Hpf, Hphys⟩
  wp_apply wp_raft_Step cf _ γ _ id s ml m ents ctx sn rsp
    (by simp only [StepMsg, stepMsgTypes]; rw [Hty]; simp [MsgProp])
    (by msg_ne') (by msg_ne')
    (by msg_ne') (by msg_ne')
    (by msg_ne') (by msg_ne')
    (by msg_ne') (by msg_ne')
    (by msg_ne') (by msg_ne')
    (by msg_ne')
    (fun _ => ⟨Hterm, .inr Hfr⟩) (by msg_ne') (by msg_ne') (by msg_ne') (by msg_ne') (by msg_ne')
    (RestMsgOk.of_ne ⟨by msg_ne', by msg_ne', by msg_ne', by msg_ne', by msg_ne'⟩) Hwf
    (GMode.Pre.of_facts Hpf (by msg_ne') (by msg_ne')) (fun h => absurd h (by msg_ne'))
    $$ [$Hphys $Hghost $Hlc Hmin Htk Hcr]
  · rw [Hty]
    simp only [ite_true]
    isplitl [Hmin Htk]
    · simp only [named]
      isplitl [Hmin]
      · iexact Hmin
      isplitl [Htk]
      · isplitr
        · iexists cs
          iexact Hcc
        iexact Htk
      isplitr
      · ipureintro
        intro _
        exact ⟨Hne, Hlen⟩
      isplitr
      · ipureintro
        intro Hc
        simp [MsgProp, MsgStorageApplyResp] at Hc
      · imodintro
        iintro %ty %Hty2 _
        rw [show mtypeOf MsgProp = some .propose from rfl] at Hty2
        cases Hty2
        iapply isMessage_ctx_intro _ .propose _ _ _ ⟨nofun, nofun⟩
        iexact Hm
    isplitl [Hcr]
    · simp [MsgProp, MsgReadIndex]; iexact Hcr
    · imodintro
      iintro %Hc
      simp [MsgProp, MsgSnap] at Hc
  iintro %err %s' %c' %md' ⟨Hphys, Hghost, %Hwf', %Href, %Hcc, %Hloc, %_, %_, %_, Herr⟩
  ihave #Hstep : stepErr err $$ [Herr]
  · unfold stepErr
    icases Herr with (%Hnil | ⟨-, #Hpd⟩)
    · ileft; ipureintro; exact Hnil
    · iright
      unfold errProposalDropped
      icombine Hpd ErrPropDropped gives %Heq
      subst Heq
      iframe Hpd
      ipureintro; exact HErrPropDropped
  have Hc := Href.commit_mono
  have e1 := Href.keep (by msg_ne') (by msg_ne'); subst e1
  have e2 := Hcc (by msg_ne'); subst c'
  obtain ⟨Hfr', Hap, -⟩ := Hloc (.inl Hty)
  have Hap' := Hap (fun Hc => by rw [Hty] at Hc; simp [MsgProp, MsgStorageApplyResp] at Hc)
  ihave #Hstr' := storedRecs_eq γ _ s'.logst.prev _ s'.logst.stored Hfr'.2.2.2.2.1
    Hfr'.2.2.2.2.2.1 $$ Hstrecs
  iapply HΦ
  isplitl
  rotate_left
  · iexact Hstep
  iapply ownRawNode_intro γ rn id rs s' cf fp rnv sv hprev steps Hwf' Hin Hal Hasync
    (by rw [Hap']; exact Hdlen) (by rw [Hfr'.2.2.1]; exact Hunp)
    (by rw [Hfr'.2.2.2.1]; exact Hsnap)
    (stepsOk_mono s s' _ Hfr'.1 ⟨Hfr'.2.2.2.2.1, Hfr'.2.2.2.2.2.1⟩ Hc Hap'
      (tc_le_of_gh Hfr'.2.2.2.2.2.2.2.2.1) Hstok)
    (by rw [Hfr'.1]; exact Htrm) (by rw [Hfr'.2.2.2.2.2.2.1]; exact Hstor)
    (Hpvoff.keep rfl rfl Hfr'.2.2.2.2.2.2.2.1 Hfr'.2.2.2.2.2.2.2.2.1 Hfr'.1 Hfr'.2.2.2.2.2.2.2.2.2.1)
    (by rw [Hfr'.2.2.2.2.2.2.2.2.1]; exact Hrs_out) (by rw [Hfr'.2.2.2.2.2.2.2.2.1]; exact Hrs_unst)
    (Int.le_trans Hrs_clb Hc)
    (RNFl.keep Hrnfl Hfr'.2.2.2.2.2.2.2.2.2.2.1 Hfr'.2.2.2.2.2.2.2.2.2.2.2 Hap')
    $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hsteps_cap Hpend Hdeliv Hstr'

end step

/-! ## `r.applyConfChange`, on the node (2026-10-13) -/

section applycc
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-! ### The dynamic mode (2026-10-14, stage B7 part 2; moved here from
`RawNode__ApplyConfChange.lean` on 2026-10-15 for `node.run`'s `confc` arm) -/

/-- The dynamic model's reading of `ApplyCCOkC c'` (2026-10-14, stage B7 part 2): at a ghost part
over `c'`, a non-leader takes no step, a leader that stays a voter takes `reMatch`, `commit` by a
joint quorum of `c'` and `sendApps` (an `MsgApp` carrying its commit index, `ReplSends`), and a
removed or demoted leader takes `reMatch` and steps down (`StepR.stepDown`, with
`StepDownOnRemoval`). `applyCCOkC_step`'s `StepR` version: `StepR` has the step-down. -/
theorem applyCCOkC_stepR {Adm : List EntryM → CCState → Prop} {dec : CCDec} {B : Int} (c' : CfgM)
    (id : w64) (s s' : NState) (g : RGh) (H : ApplyCCOkC c' id s s') (hc : g.cfg.cfg = c') :
    StepR Adm dec id B (rOf s g) [] (rOf s' g) := by
  obtain ⟨prs, pvs, Hdom, Hmk, Hsw⟩ := H
  unfold SwitchOkC at Hsw
  by_cases Hl : s.role = .leader
  · rw [ite_eq_left (show ({ s with progress := prs, prvals := pvs, isLearner := learnerOfC c' id } :
        NState).role = .leader from Hl)] at Hsw
    have Hpl : (toPState s).role = .leader := by simp [toPState, Hl, proleRole]
    -- the new `Progress` values
    have H1 : StepCF c' id (toPState s) []
        (toPState { s with progress := prs, prvals := pvs, isLearner := learnerOfC c' id }) := by
      have e : toPState { s with progress := prs, prvals := pvs, isLearner := learnerOfC c' id } =
          { toPState s with matched := prvalsMatch pvs } := by simp [toPState, Hl]
      rw [e]
      refine .reMatch _ _ Hpl (fun v i hv => ?_)
      simp only [prvalsMatch, GMap.lookup_fmap'] at hv
      cases hp : pvs !! v with
      | none => rw [hp] at hv; cases hv
      | some p' =>
        rw [hp] at hv
        simp only [Option.map_some, Option.some.injEq] at hv
        subst hv
        rcases Hmk v p' hp with h0 | ⟨p, hp0, hm⟩
        · exact .inl h0
        · right
          simp [toPState, Hl, prvalsMatch, hp0, hm]
    have Hz := rOf_pci_zero s g
    by_cases Hv : id ∈ c'.voters
    · rw [ite_eq_left Hv] at Hsw
      obtain ⟨c, ms, pvs2, lt', Hc, Hms, Hmm, rfl⟩ := Hsw
      generalize Hs1 : ({ s with progress := prs, prvals := pvs, isLearner := learnerOfC c' id } :
        NState) = s1 at H1 Hc Hms Hmm
      have Hl1 : s1.role = .leader := by rw [← Hs1]; exact Hl
      have Hpl1 : (toPState s1).role = .leader := by simp [toPState, Hl1, proleRole]
      -- the commit
      have H2 : StepCF c' id (toPState s1) []
          (toPState { s1 with logst := { s1.logst with committed := c } }) := by
        rcases Hc with rfl | ⟨Hlt, Hle, Htm, Hq⟩
        · have e : ({ s1 with logst := { s1.logst with committed := s1.logst.committed } } : NState)
              = s1 := by cases s1; rfl
          rw [e]; exact .refl _
        · have e : toPState { s1 with logst := { s1.logst with committed := c } } =
              { toPState s1 with commit := c } := by simp [toPState, Hl1]
          rw [e]
          exact .commit _ c Hpl1 Hlt Hle Htm Hq
      generalize Hs2 : ({ s1 with logst := { s1.logst with committed := c } } : NState) = s2
        at H2 Hms
      have Hl2 : s2.role = .leader := by rw [← Hs2]; exact Hl1
      -- the appends
      have H3 : StepCF c' id (toPState s2) []
          (toPState { sendMsgs s2 ms with prvals := pvs2, lt := lt' }) := by
        have e : toPState { sendMsgs s2 ms with prvals := pvs2, lt := lt' } =
            toPState { sendMsgs s2 ms with prvals := pvs2 } := rfl
        rw [e, toPState_prvals (sendMsgs s2 ms) pvs2 (fun _ => by
          rw [Hmm]; rw [← Hs2]; rfl), toPState_sendMsgs]
        exact .sendApps _ ms (by simp [toPState, Hl2, proleRole]) Hms.replOk Hms.commitEq
          (Hms.snapTo (by
            rw [← Hs2, ← Hs1]
            show domSet prs ⊆ c'.voters ∪ c'.learners
            rw [Hdom]; exact GMap.subseteq_refl _))
      have HF := StepCF.trans _ _ _ _ _ H1 (StepCF.trans _ _ _ _ _ H2 H3)
      have HR := HF.toR (Adm := Adm) (dec := dec) (B := B) (rOf s g) rfl hc Hz
      have Hfr : RFrame s { sendMsgs s2 ms with prvals := pvs2, lt := lt' } := by
        refine ⟨?_, ?_, fun _ => ⟨Hl, ?_⟩⟩ <;> (rw [← Hs2, ← Hs1]; try rfl)
      rw [rOf_frame _ _ g Hfr]
      exact HR
    · -- removed or demoted: `reMatch`, then the step-down
      rw [ite_eq_right Hv] at Hsw
      obtain ⟨pvs', rfl⟩ := Hsw
      generalize Hs1 : ({ s with progress := prs, prvals := pvs, isLearner := learnerOfC c' id } :
        NState) = s1 at H1 ⊢
      have HR1 := H1.toR (Adm := Adm) (dec := dec) (B := B) (rOf s g) rfl hc Hz
      have Hfr1 : RFrame s s1 := by
        refine ⟨?_, ?_, fun _ => ⟨Hl, ?_⟩⟩ <;> (rw [← Hs1]; try rfl)
      rw [← rOf_frame _ _ g Hfr1] at HR1
      have Hl1 : s1.role = .leader := by rw [← Hs1]; exact Hl
      have Hrl : (rOf s1 g).p.role = .leader := by simp [rOf, toPState, Hl1, proleRole]
      have HR2 := StepR.stepDown (Adm := Adm) (dec := dec) (id := id) (B := B) (rOf s1 g) Hrl
      have Ht1 : s1.term = s.term := by rw [← Hs1]
      have e : RState.mk (pbecomeFollower (rOf s1 g).p (rOf s1 g).p.term (W64 0))
          (rOf s1 g).applied (W64 0) (rOf s1 g).snap (rOf s1 g).cidx (rOf s1 g).cfg (rOf s1 g).fp =
          rOf ({ becomeFollower s1 s1.term (W64 0) with prvals := pvs' } : NState) g := by
        have h1 := toPState_prvals (becomeFollower s1 s1.term (W64 0)) pvs'
          (fun h => by simp [becomeFollower] at h)
        have h2 := toPState_becomeFollower s1 s1.term (W64 0)
        unfold rOf
        rw [h1, h2]
        simp [pciR, becomeFollower, toPState, resetTo0, resetTo]
      rw [e] at HR2
      exact .trans _ _ _ _ _ HR1 HR2
  · rw [ite_eq_right (show ¬ ({ s with progress := prs, prvals := pvs, isLearner := learnerOfC c' id } :
        NState).role = .leader from Hl)] at Hsw
    subst Hsw
    have e : rOf { s with progress := prs, prvals := pvs, isLearner := learnerOfC c' id } g =
        rOf s g := by
      unfold rOf pciR
      simp [toPState, Hl]
    rw [e]
    exact .refl _

/-- What `ApplyCCOkC` keeps of the physical state, the removed leader's step-down included. -/
theorem applyCCOkC_frame {c' : CfgM} {id : w64} {s s' : NState} (H : ApplyCCOkC c' id s s')
    (Hwf : NStateWf s) :
    NStateWf s' ∧ s'.term = s.term ∧ s'.prevote = s.prevote ∧ s'.gh = s.gh ∧
      s'.logst = { s.logst with committed := s'.logst.committed } ∧
      uint.Z s.logst.committed ≤ uint.Z s'.logst.committed ∧
      -- (2026-10-17) no pre-candidate made (`RNPv`)
      (s'.role = .preCandidate → s.role = .preCandidate) := by
  rcases applyCCOkC_step (B := 0) c' id s s' H with ⟨-, Hr, Hsf, Htk, Ht, Hpv, Hg, Hl, Hc⟩ | ⟨Hl, Hv, -⟩
  · exact ⟨⟨by rw [Hsf, Hr]; exact Hwf.1, by rw [Htk]; exact Hwf.2⟩, Ht, Hpv, Hg, Hl, Hc,
      fun h => by rw [← Hr]; exact h⟩
  · obtain ⟨prs, pvs, -, -, Hsw⟩ := H
    unfold SwitchOkC at Hsw
    rw [ite_eq_left (show ({ s with progress := prs, prvals := pvs, isLearner := learnerOfC c' id } :
        NState).role = .leader from Hl), ite_eq_right Hv] at Hsw
    obtain ⟨pvs', rfl⟩ := Hsw
    refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [becomeFollower, resetTo0, resetTo, stepFuncOf]

/-- `ccStepB`'s answer is `ccApplyM`'s, of fewer than `2^62` tracked ids. -/
theorem ccStepB_some {op : CCOp} {s s' : CCState} (h : ccStepB op s = some s') :
    ccApplyM op.1 op.2 s = some s' ∧ GMap.size s'.cfg.ids < 2 ^ 62 := by
  unfold ccStepB at h
  cases h1 : ccApplyM op.1 op.2 s with
  | none => rw [h1] at h; cases h
  | some s2 =>
    rw [h1] at h
    simp only [Option.bind_some] at h
    split at h
    · cases h; exact ⟨rfl, by assumption⟩
    · cases h


/-- `r.applyConfChange(cc)` at a dynamic node (2026-10-14, stage B7 part 2): the configuration
takes the next conf entry's change (`StepR.applyConf`), then `switchToConfig`'s effect
(`applyCCOkC_stepR`, a removed leader's step-down included); the node's ghost state follows
(`ownRaftGhostR_stepR`), and `ownRawNode` is re-sealed at the new configuration and
configuration index. The node is no candidate (a candidate has no conf entry to apply: `RInv`'s
`cand`), no pre-candidate (pre-vote off), and a removed leader steps down (`sdrOk`). -/
theorem wp_applyConf_dyn
    (wp_raft_applyConfChange : raft.applyConfChange.spec (GF := GF) (hG := hG))
    (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (dec : CCDec) (c0 : CCState)
    (h0 : CfgOk c0) (h1 : CCGood c0) (hm : rs.mode = .dyn dec c0 h0 h1) (k : Nat)
    (e : EntryM) (cs' : CCState)
    (cc : Loc) (ccm : CCV2M) (dq : DFrac)
    (Hpre : DynCCPreOp dec rs.delivered rs.capplied rs.cfg (ccm.transition, ccm.changes) k e cs')
    (s : NState) (cf : CfgM) (fp : List EntryM) (rnv : RawNode) (sv : SoftState)
    (hprev : HardStateM) (steps : List Loc)
    (Hwf : NStateWf s) (Hin : rs.mode = .static → id ∈ γ.reCfg) (Hasync : rnv.asyncStorageWrites' = false)
    (Hdlen : rs.delivered.length = (uint.Z s.logst.applying).toNat)
    (Hunp : rs.unpersisted = s.logst.unpersisted) (Hsnap : s.logst.snap = none)
    (Hstok : StepsOk s rs.steps)
    (Htrm : rs.term = s.term) (Hstor : rs.storage = s.logst.storage)
    (Hpvoff : RNPv rs s) (Hrs_out : rs.outlb = s.gh.outlb)
    (Hrs_unst : rs.unst = s.gh.unst) (Hrs_clb : uint.Z rs.clb ≤ uint.Z s.logst.committed)
    (Hrnfl : RNFl rs s) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        rawNodeOwn rn rnv ∗ ownRaftPhysCV cf cf.voters rnv.raft' id s ∗
        ownStepGhost γ (rs.mode.toG ⟨rs.capplied, rs.cfg, fp⟩) cf id s ∗
        sdrOk rnv.raft' rs.mode ∗ rnv.prevSoftSt' ↦□ sv ∗ hsRO rnv.prevHardSt' hprev ∗
        rnv.stepsOnAdvance' ↦* steps ∗
        ownSliceCap Loc rnv.stepsOnAdvance' (DFrac.own 1) ∗
        pendList γ id steps rs.steps ∗
        isCommitted γ rs.delivered ∗ storedRecs γ s.logst.prev s.logst.stored ∗
        ownCCV2 cc dq ccm ∗ £ 1 }}
      (App (Val (rnv.raft' @!! go.GoType.PointerType raft.ty @!! go!"applyConfChange")) (Val #cc))
    {{ (cs : Loc) (xs os ls lns : List w64), RET #cs;
        ownRawNode γ rn id { rs with cfg := cs', capplied := k + 1 } ∗
        ownCCV2 cc dq ccm ∗
        csPts cs (DFrac.own 1) (ConfStateM.mk xs ls os lns cs'.cfg.autoLeave) true ∗
        ⌜xs ≡ₚ elements cs'.cfg.incoming ∧ os ≡ₚ elements cs'.cfg.outgoing ∧
          ls ≡ₚ elements cs'.cfg.learners ∧ lns ≡ₚ elements cs'.cfg.learnersNext⌝ }} := by
  obtain ⟨Hk1, Hk2, Hke, Hconf, Hnoc, Hdec, Hstep, Hal', Hw0r⟩ := Hpre
  iintro %Φ ⟨#Hpkg, Hrn, Hphys, Hghost, #Hsdrf, #Hsoft, #Hhard, Hsteps, Hcap, Hpend, #Hdeliv,
    #Hstrecs, Hch, Hlc⟩ HΦ
  let g : RGh := ⟨rs.capplied, rs.cfg, fp⟩
  ihave Hghost : ownStepGhost γ (.dyn dec c0 h0 g) cf id s $$ [Hghost]
  · rw [show (GMode.dyn dec c0 h0 g) = rs.mode.toG ⟨rs.capplied, rs.cfg, fp⟩ by rw [hm]; rfl]
    iexact Hghost
  icases ownRaftPhysC_logwf cf rnv.raft' id s $$ Hphys with ⟨%Hlw, Hphys⟩
  icases ownStepGhost_deliv γ dec c0 h0 g cf id s rs.delivered
    (by rw [Hdlen]; have := uint_Z_nonneg s.logst.applying; omega) $$ Hdeliv Hghost
    with ⟨%Hdp, Hghost⟩
  icases ownStepGhost_ns_last γ _ cf id s $$ Hghost with ⟨%Hli2, Hghost⟩
  icases (ownStepGhost_dyn γ dec c0 h0 g cf id s).1 $$ Hghost with ⟨%HDc, Hgr⟩
  obtain ⟨HD, Hgc, Hnl, Hps⟩ := HDc
  -- (2026-10-20) at a configuration without a witness (`NoWitReconf`): a plain `applyConf`
  -- (`StepR.applyConf`)
  have hwcf : cf.wit = W64 0 := by rw [← Hgc]; exact Hw0r
  iunfold ownRaftGhostR at Hgr
  icases Hgr with ⟨Hg, %HI, #Hfr, #Hwr, #Hcamp⟩
  icases (entails_wand (persistent_entails_left (wand_entails
    (ownRaftGhost_logRecs (GF := GF) γ id (rOf s g).p true)))) $$ Hg with ⟨Hg, %-, #Hlr⟩
  icases ownRaftPhysC_preFacts cf rnv.raft' id s (Hpvoff.dyn ⟨rs.capplied, rs.cfg, fp⟩) $$ Hphys with ⟨%Hpf, Hphys⟩
  icases ownRaftPhysC_sdr cf rnv.raft' id s $$ Hphys with ⟨#Hsd, Hphys⟩
  ihave #Hsdrf' := Hsdrf
  iunfold sdrOk at Hsdrf'
  icases Hsdrf' with ⟨%b, #Hb, %Hbt⟩
  icombine Hb Hsd gives %Hbs
  have Hsdr : s.sdr = true := by rw [← Hbs]; exact Hbt (by rw [hm]; rfl)
  -- the entry, in the node's full log
  have Hfull_k : (rOf s g).full[k]? = some e := by
    obtain ⟨t, ht⟩ := Hdp
    rw [← ht, List.getElem?_append_left Hk2]; exact Hke
  have Htake : (rOf s g).full.take k = rs.delivered.take k := by
    obtain ⟨t, ht⟩ := Hdp
    rw [← ht, List.take_append_of_le_length (Nat.le_of_lt Hk2)]
  have Hkc : k < uint.nat s.logst.committed := by
    have := uint_nat_eq s.logst.committed; have := uint_nat_eq s.logst.applying; omega
  have Hnoc' : NoConfIn (rOf s g).full g.cidx k :=
    NoConfIn_prefix Hdp (Nat.le_of_lt Hk2) Hnoc
  -- the configuration the code sees is the model's
  have Hgood : CCGood rs.cfg := cfgFold_good h1 HI.cfg
  have Hcfg : cfgStateC cf = rs.cfg := by rw [← Hgc]; exact cfgStateC_of_good Hgood
  obtain ⟨Happ, Hsz⟩ := ccStepB_some Hstep
  -- no candidate: a candidate has no conf entry past `applied` (`RInv.cand`)
  have Hnc : s.role ≠ .candidate := by
    intro hc
    have hc' : (rOf s g).p.role = .candidate := by simp [rOf, toPState, hc, proleRole]
    obtain ⟨-, Hn⟩ := HI.cand hc'
    have Hac := HI.applied_cidx
    exact Hn k e (Nat.le_trans Hac Hk1) Hkc Hfull_k Hconf
  imod rdCred_zero_upd (GF := GF) γ with Hcr0
  iapply wp_fupd
  wp_apply +noauto wp_raft_applyConfChange cf rnv.raft' id s cc ccm dq cs'
      (by rw [Hcfg]; exact Happ) (by have := Hsz; omega) (fun _ _ => Hsdr)
      (fun h => by
        rcases h with h | h
        · exact absurd h Hnc
        · exact absurd h (Hpf.1 (by rw [hm]; rfl))) Hli2 hwcf
    $$ [$Hphys $Hch] as %cs %xs %os %ls %lns %s' ⟨Hphys, Hch, Hcs, %Hcs0, %Hok⟩
  -- the ghost step
  let g' : RGh := ⟨k + 1, cs', fp⟩
  have Hadm : AdmS dec c0 (fun l => l = (rOf s g).full.take (k + 1)) ((rOf s g).full.take (k + 1))
      cs' := by
    refine ⟨?_, rfl⟩
    unfold AdmFold
    have H0 := cfgFold_noConf dec c0 Hnoc' Hk1 HI.cfg
    rw [show (rOf s g).full.take (k + 1) = (rOf s g).full.take k ++ [e] by
      rw [List.take_add_one, Hfull_k]; rfl, cfgFold_snoc, H0, Option.bind_some]
    unfold entStep
    rw [ite_eq_left Hconf, Htake, Hdec, Option.bind_some]
    exact Hstep
  have HR1 : StepR (AdmS dec c0 (fun l => l = (rOf s g).full.take (k + 1))) dec id 0 (rOf s g) []
      (rOf s g') :=
    StepR.applyConf (rOf s g) k e (ccm.transition, ccm.changes) cs' (by simp [rOf, Hsnap]) Hk1 Hkc Hfull_k Hconf
      Hnoc' (by rw [Htake]; exact Hdec) Hstep Hadm
      (fun _ => by show rs.cfg.cfg.wit = W64 0; rw [Hgc]; exact hwcf)
  have HR2 := applyCCOkC_stepR (B := 0) (Adm := AdmS dec c0 (fun l => l = (rOf s g).full.take (k + 1)))
    (dec := dec) cs'.cfg id s s' g' Hok rfl
  have HR := StepR.trans _ _ _ _ _ HR1 HR2
  ihave #Hrecs : □ ∀ (fp' : List EntryM), ⌜fp' = (rOf s g).full.take (k + 1)⌝ -∗
      logRecs (GF := GF) γ base0 fp' $$ []
  · ihave #Hfl := logRecs_full γ (rOf s g).p.base (rOf s g).fp (rOf s g).p.log HI.full $$ Hfr Hlr
    imodintro
    iintro %fp' %Hfp'
    subst Hfp'
    rw [show (rOf s g).full = (rOf s g).fp ++ (rOf s g).p.log from rfl]
    iapply logRecs_take γ _ (k + 1) $$ Hfl
  ihave Hgr : ownRaftGhostR γ dec c0 id (rOf s g) $$ [Hg]
  · iunfold ownRaftGhostR
    iframe Hg Hfr Hwr
    isplitr
    · ipureintro; exact HI
    iintro %hc; iapply Hcamp; exact hc
  imod (preceipt_zero_bound (GF := GF) γ.reBoot.length) with #Hrc0
  imod ownRaftGhostR_stepR γ dec c0 h0 HD _ id 0 (by decide) _ _ _ HR $$ Hrc0 Hrecs [] [Hcr0] []
    Hlc Hgr with Hgr
  · rw [List.nil_append]
    iapply (BigSepL.bigSepL_nil (Φ := fun _ m => isMessage (GF := GF) γ m)).2
    iempintro
  · rw [List.nil_append, show rdCount ([] : List Msg) = 0 from rfl]; iexact Hcr0
  · rw [List.nil_append]; iapply msgsTks_nil
  ihave Hghost : ownStepGhost γ (.dyn dec c0 h0 g') cs'.cfg id s' $$ [Hgr]
  · iapply (ownStepGhost_dyn γ dec c0 h0 g' cs'.cfg id s').2
    iframe Hgr
    ipureintro; exact ⟨HD, rfl, by unfold NsLink; rw [Hok.gh]; exact Hnl, StepR.psubOk HR Hps⟩
  ihave Hghost : ownStepGhost γ (({ rs with cfg := cs', capplied := k + 1 } : RNState).mode.toG
      ⟨({ rs with cfg := cs', capplied := k + 1 } : RNState).capplied,
       ({ rs with cfg := cs', capplied := k + 1 } : RNState).cfg, fp⟩) cs'.cfg id s' $$ [Hghost]
  · rw [show (({ rs with cfg := cs', capplied := k + 1 } : RNState).mode.toG
        ⟨({ rs with cfg := cs', capplied := k + 1 } : RNState).capplied,
         ({ rs with cfg := cs', capplied := k + 1 } : RNState).cfg, fp⟩) = GMode.dyn dec c0 h0 g' by
      simp only; rw [hm]; rfl]
    iexact Hghost
  obtain ⟨Hwf', Ht', Hpv', Hgh', Hls', Hc', Hrl'⟩ := applyCCOkC_frame Hok Hwf
  ihave #Hstr' := storedRecs_eq γ _ s'.logst.prev _ s'.logst.stored (by rw [Hls'])
    (by rw [Hls']) $$ Hstrecs
  imodintro
  iapply HΦ $$ %cs %xs %os %ls %lns
  iframe Hch Hcs
  isplitl
  · iapply ownRawNode_intro γ rn id { rs with cfg := cs', capplied := k + 1 } s' cs'.cfg fp rnv sv
      hprev steps Hwf' (fun h => by simp only at h; rw [hm] at h; cases h) Hal' Hasync
      (by rw [Hls']; exact Hdlen) (by rw [Hls']; exact Hunp) (by rw [Hls']; exact Hsnap)
      (stepsOk_mono s s' _ Ht' ⟨by rw [Hls'], by rw [Hls']⟩ Hc' (by rw [Hls']) (tc_le_of_gh Hgh') Hstok)
      (by rw [Ht']; exact Htrm) (by rw [Hls']; exact Hstor)
      ⟨fun h => by rw [Hpv']; exact Hpvoff.1 h, by rw [Hgh']; exact Hpvoff.2.1,
        by rw [Hgh', Ht']; exact Hpvoff.2.2.1, fun h => by rw [Hgh', Ht']; exact Hpvoff.2.2.2 (Hrl' h)⟩
      (by rw [Hgh']; exact Hrs_out) (by rw [Hgh']; exact Hrs_unst) (Int.le_trans Hrs_clb Hc')
      (by unfold RNFl; rw [Hls']; exact Hrnfl)
      $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hcap Hpend Hdeliv Hstr'
  ipureintro; exact Hcs0

/-! ### The static mode -/

/-- (D19p, 2026-10-18) A shrinking change keeps the tracker within the tracked bound: the new
progress map tracks the voters and some of the old learners. -/
theorem trackedOk_shrink {γ : RaftNames} {id : w64} {s s' : NState} {lrn' : GSet w64}
    (H : TrackedOk γ (CfgM.simple γ.reCfg (domSet s.progress \ γ.reCfg)) id)
    (Hlp : ∀ k, k ∈ lrn' → k ∈ domSet s.progress) (Hd : domSet s'.progress ⊆ γ.reCfg ∪ lrn') :
    TrackedOk γ (CfgM.simple γ.reCfg (domSet s'.progress \ γ.reCfg)) id := by
  refine TrackedOk.simple_mono (fun k hk => ?_) H
  have hk' := ((GMap.elem_of_difference _ _ _).1 hk).1
  rcases (GMap.elem_of_union _ _ _).1 ((GMap.elem_of_subseteq _ _).1 Hd k hk') with h | h
  · exact Or.inl h
  · by_cases hc : k ∈ γ.reCfg
    · exact Or.inl hc
    · exact Or.inr ((GMap.elem_of_difference _ _ _).2 ⟨Hlp k h, hc⟩)

/-- After `applyConfChange`: the ghost step its result is (`applyCCOk_step`,
`ownRaftGhost_step_0`), and `ownRawNode` re-sealed at the same client-facing state. -/
theorem rawNode_applyCC_reseal (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState)
    (s s' : NState) (ps : PState) (rnv : RawNode) (sv : SoftState) (hprev : HardStateM)
    (steps : List Loc) (Hm : rs.mode = .static)
    (Hrel : NStateRel s ps) (Hin : id ∈ γ.reCfg) (Hasync : rnv.asyncStorageWrites' = false)
    (Hdlen : rs.delivered.length = (uint.Z s.logst.applying).toNat)
    (Hunp : rs.unpersisted = s.logst.unpersisted) (Hsnap : s.logst.snap = none)
    (Hstok : StepsOk s rs.steps) (Htrm : rs.term = s.term) (Hstor : rs.storage = s.logst.storage)
    (Hpvoff : RNPv rs s) (Hrs_out : rs.outlb = s.gh.outlb)
    (Hrs_unst : rs.unst = s.gh.unst) (Hrs_clb : uint.Z rs.clb ≤ uint.Z s.logst.committed)
    (Hrnfl : RNFl rs s)
    (Hok : ApplyCCOk γ.reCfg id s s')
    -- (D19p, 2026-10-18) the new tracker within the tracked bound
    (Htrk' : TrackedOk γ (CfgM.simple γ.reCfg (domSet s'.progress \ γ.reCfg)) id)
    (Hnl : NsLink γ s) (Hps : PSubOk (toPState s)) :
    ⊢ rawNodeOwn rn rnv -∗ ownRaftPhys γ.reCfg rnv.raft' id s' -∗ ownRaftGhost (GF := GF) γ id ps -∗
      sdrOk rnv.raft' rs.mode -∗
      rnv.prevSoftSt' ↦□ sv -∗ hsRO rnv.prevHardSt' hprev -∗ rnv.stepsOnAdvance' ↦* steps -∗
      ownSliceCap Loc rnv.stepsOnAdvance' (DFrac.own 1) -∗
      pendList γ id steps rs.steps -∗
      isCommitted γ rs.delivered -∗
      storedRecs γ s.logst.prev s.logst.stored -∗ £ 1 ={⊤}=∗
      ownRawNode γ rn id rs := by
  obtain ⟨Hst, Hro, Hsf, Htk, Htm, Hpv, Hgh, Hls, Hc⟩ :=
    applyCCOk_step (B := 0) _ γ.reCfg_ne _ _ _ Hok
  have Hprev : s'.logst.prev = s.logst.prev := by rw [Hls]
  have Hstored : s'.logst.stored = s.logst.stored := by rw [Hls]
  have Happ : s'.logst.applying = s.logst.applying := by rw [Hls]
  have Hunp' : s'.logst.unpersisted = s.logst.unpersisted := by rw [Hls]
  have Hsnap' : s'.logst.snap = s.logst.snap := by rw [Hls]
  have Hstor' : s'.logst.storage = s.logst.storage := by rw [Hls]
  have Hwf' : NStateWf s' := by
    obtain ⟨-, H1, H2⟩ := Hrel
    exact ⟨by rw [Hsf, Hro]; exact H1, by rw [Htk]; exact H2⟩
  iintro Hrn Hphys Hghost #Hsdrf #Hsoft #Hhard Hsteps Hcap Hpend #Hdeliv #Hstrecs Hlc
  rw [← Hrel.1] at *
  imod (preceipt_zero_bound (GF := GF) γ.reBoot.length) with #Hrc0
  ihave %Hst0 := ownRaftGhost_static γ id _ $$ Hghost
  imod ownRaftGhost_step_0 γ _ (CfgStatic.simple γ _ Hst0) id Htrk' 0 (by decide) _ _ Hst
    $$ Hrc0 Hlc Hghost with Hghost
  ihave #Hstr' := storedRecs_eq γ _ s'.logst.prev _ s'.logst.stored Hprev Hstored $$ Hstrecs
  iapply ownRawNode_intro_static γ rn id rs s' (toPState s') rnv sv hprev steps Hm ⟨rfl, Hwf'⟩ Hin Hasync
    (by rw [Happ]; exact Hdlen) (by rw [Hunp']; exact Hunp) (by rw [Hsnap']; exact Hsnap)
    (stepsOk_mono_le s s' _ (by rw [Htm]; exact Int.le_refl _) ⟨Hprev, Hstored⟩ Hc Happ (tc_le_of_gh Hgh) Hstok)
    (by rw [Htm]; exact Htrm) (by rw [Hstor']; exact Hstor) (Hpvoff.keep rfl rfl Hpv Hgh Htm Hro)
    (by rw [Hgh]; exact Hrs_out) (by rw [Hgh]; exact Hrs_unst) (Int.le_trans Hrs_clb Hc)
    (by unfold RNFl; rw [Hls]; exact Hrnfl) Htrk' (by unfold NsLink; rw [Hgh]; exact Hnl)
    (StepC.psubOk Hst (by rw [Hrel.1]; exact Hps))
    $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hcap Hpend Hdeliv Hstr'

/-- `r.applyConfChange(cc)` on the node's raft struct, for a change that leaves the
configuration unchanged (`node.run`'s `confc` arm); the ghost step inside. -/
theorem wp_rn_raft_applyConfChange
    (wp_raft_applyConfChange : raft.applyConfChange.spec (GF := GF) (hG := hG))
    (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (r : Loc) (cc : Loc) (ccm : CCV2M)
    (Hst : γ.reDyn = none)
    (Hn : CCShrink γ.reCfg ccm.transition ccm.changes) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        ownRawNode γ rn id rs ∗ rn.[RawNode, go!"raft"] ↦□ r ∗ ownCCV2 cc DFrac.discard ccm ∗
        £ 1 }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"applyConfChange")) (Val #cc))
    {{ (cs : Loc) (xs ls : List w64), RET #cs;
        ownRawNode γ rn id rs ∗ ownCCV2 cc DFrac.discard ccm ∗
        csPts cs (DFrac.own 1) (ConfStateM.mk xs ls [] [] false) true ∗
          ⌜xs ≡ₚ elements γ.reCfg ∧ (∀ k ∈ ls, k ∉ γ.reCfg)⌝ }} := by
  iintro %Φ ⟨#Hpkg, Hrn, #Hr, Hccs, Hlc⟩ HΦ
  icases ownRawNode_mode γ rn id rs $$ Hrn with ⟨%Hmd, Hrn⟩
  have Hm : rs.mode = .static := Hmd.2 Hst
  iNamed Hrn
  ihave #Hr' := rawNodeOwn_raft rn rnv $$ Hrn
  icombine Hr Hr' gives %Heq
  subst Heq
  icases ownRawNode_static_open γ rs Hm fp cf rnv.raft' id s $$ Hphys Hghost with
    ⟨Hphys, Hghost, %Htrk, %Hnl, %Hps⟩
  have Hrel : NStateRel s (toPState s) := ⟨rfl, Hwf⟩
  have Hin := Hin Hm
  iapply wp_fupd
  icases ownRaftPhys_progress_dom γ.reCfg rnv.raft' id s $$ Hphys with ⟨%Hsub, Hphys⟩
  icases ownRaftPhys_progress_size γ.reCfg rnv.raft' id s $$ Hphys with ⟨%Hsz, Hphys⟩
  obtain ⟨lrn', Hd', Hsz', Hn', Hlp⟩ := applyCC_of_shrink γ.reCfg s.progress _ _ Hn Hsub Hsz
  icases ownRaftGhost_ns_last γ id s Hnl $$ Hghost with ⟨%Hli2, Hghost⟩
  wp_apply +noauto (raft.applyConfChange.spec_simple wp_raft_applyConfChange) γ.reCfg rnv.raft' id
      s cc ccm DFrac.discard lrn' Hd' Hsz' Hn' Hli2
    $$ [$Hphys $Hccs] as %cs %xs %ls %s' ⟨Hphys, Hccs, Hcs, %Hcs0, %Hok, %Hdom'⟩
  imod rawNode_applyCC_reseal γ rn id rs s s' _ rnv sv hprev steps Hm Hrel Hin Hasync Hdlen Hunp
    Hsnap Hstok Htrm Hstor Hpvoff Hrs_out Hrs_unst Hrs_clb Hrnfl Hok
    (trackedOk_shrink Htrk Hlp Hdom') Hnl Hps
    $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hsteps_cap Hpend Hdeliv Hstrecs Hlc with Hrn
  try wp_auto
  imodintro
  iapply HΦ $$ %cs %xs %ls
  iframe Hrn Hccs Hcs
  ipureintro
  exact ⟨Hcs0.1, fun k hk => Hd' k ((GMap.elem_of_elements _ _).1 (Hcs0.2.mem_iff.1 hk))⟩

/-- The struct out of the node with the node's membership (`ownRawNode_borrow`'s and
`Hin`): for `_, ok := r.trk.Progress[r.id]`, which finds the node. -/
theorem ownRawNode_borrow_in (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (r : Loc)
    (Hst : γ.reDyn = none) :
    ⊢ ownRawNode (GF := GF) γ rn id rs -∗ rn.[RawNode, go!"raft"] ↦□ r -∗
      ∃ s : NState, ⌜id ∈ γ.reCfg⌝ ∗ ownRaftPhys γ.reCfg r id s ∗
        (ownRaftPhys γ.reCfg r id s -∗ ownRawNode γ rn id rs) := by
  iintro H #Hr
  icases ownRawNode_mode γ rn id rs $$ H with ⟨%Hmd, H⟩
  have Hm : rs.mode = .static := Hmd.2 Hst
  iNamed H
  icases ownRawNode_static_open γ rs Hm fp cf rnv.raft' id s $$ Hphys Hghost with
    ⟨Hphys, Hghost, %Htrk, %Hnl, %Hps⟩
  have Hrel : NStateRel s (toPState s) := ⟨rfl, Hwf⟩
  have Hin := Hin Hm
  ihave #Hr' := rawNodeOwn_raft rn rnv $$ Hrn
  icombine Hr Hr' gives %Heq
  subst Heq
  iexists s
  isplitr
  · ipureintro; exact Hin
  isplitl [Hphys]
  · iexact Hphys
  iintro Hphys
  iapply ownRawNode_intro_static γ rn id rs s _ rnv sv hprev steps Hm Hrel Hin Hasync Hdlen Hunp Hsnap
    Hstok Htrm Hstor Hpvoff Hrs_out Hrs_unst Hrs_clb Hrnfl Htrk Hnl Hps
    $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hsteps_cap Hpend Hdeliv Hstrecs

/-- `r.applyConfChange(cc)` on the node's raft struct in the dynamic mode (2026-10-15, stage N;
`node.run`'s `confc` arm): `wp_applyConf_dyn` on `ownRawNode`, the changes read-only. -/
theorem wp_rn_raft_applyConfChange_dyn
    (wp_raft_applyConfChange : raft.applyConfChange.spec (GF := GF) (hG := hG))
    (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (r : Loc) (cc : Loc) (ccm : CCV2M)
    (dec : CCDec) (c0 : CCState) (h0 : CfgOk c0)
    (h1 : CCGood c0) (hm : rs.mode = .dyn dec c0 h0 h1) (k : Nat) (e : EntryM)
    (cs' : CCState)
    (Hpre : DynCCPreOp dec rs.delivered rs.capplied rs.cfg (ccm.transition, ccm.changes) k e cs') :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        ownRawNode γ rn id rs ∗ rn.[RawNode, go!"raft"] ↦□ r ∗ ownCCV2 cc DFrac.discard ccm ∗
        £ 1 }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"applyConfChange")) (Val #cc))
    {{ (cs : Loc) (xs os ls lns : List w64), RET #cs;
        ownRawNode γ rn id { rs with cfg := cs', capplied := k + 1 } ∗
        ownCCV2 cc DFrac.discard ccm ∗
        csPts cs (DFrac.own 1) (ConfStateM.mk xs ls os lns cs'.cfg.autoLeave) true ∗
        ⌜xs ≡ₚ elements cs'.cfg.incoming ∧ os ≡ₚ elements cs'.cfg.outgoing ∧
          ls ≡ₚ elements cs'.cfg.learners ∧ lns ≡ₚ elements cs'.cfg.learnersNext⌝ }} := by
  iintro %Φ ⟨#Hpkg, Hrn, #Hr, Hccs, Hlc⟩ HΦ
  iNamed Hrn
  ihave #Hr' := rawNodeOwn_raft rn rnv $$ Hrn
  icombine Hr Hr' gives %Heq
  subst Heq
  iapply wp_applyConf_dyn wp_raft_applyConfChange γ rn id rs dec c0 h0 h1 hm k e cs' cc ccm
      DFrac.discard Hpre s cf fp rnv sv hprev steps Hwf Hin Hasync Hdlen Hunp Hsnap Hstok Htrm Hstor
      Hpvoff Hrs_out Hrs_unst Hrs_clb Hrnfl
    $$ [$Hpkg $Hrn $Hphys $Hghost $Hsdrf $Hsoft $Hhard $Hsteps $Hsteps_cap $Hpend $Hdeliv
      $Hstrecs $Hccs $Hlc]
  inext
  iintro %cs %xs %os %ls %lns ⟨Hrn, Hccs, Hcs, %Hcs⟩
  iapply HΦ $$ %cs %xs %os %ls %lns
  iframe Hrn Hccs Hcs
  ipureintro; exact Hcs

end applycc

/-! ## `run`'s states -/

section states
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `rs.asyncStorageWrites`, read from the node (`false`). -/
theorem ownRawNode_async (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) :
    ⊢ ownRawNode (GF := GF) γ rn id rs -∗
      ∃ rnv : RawNode, rawNodeOwn rn rnv ∗ ⌜rnv.asyncStorageWrites' = false⌝ ∗
        (rawNodeOwn rn rnv -∗ ownRawNode γ rn id rs) := by
  iintro H
  iNamed H
  iexists rnv
  isplitl [Hrn]
  · iexact Hrn
  isplitr
  · ipureintro; exact Hasync
  iintro Hrn
  iapply ownRawNode_intro γ rn id rs s cf fp rnv sv hprev steps Hwf Hin Hal Hasync Hdlen Hunp Hsnap
    Hstok Htrm Hstor Hpvoff Hrs_out Hrs_unst Hrs_clb Hrnfl
    $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hsteps_cap Hpend Hdeliv Hstrecs

/-- A `Ready` `run` computed and abandoned but keeps armed (`readyc` set): what
`ownRawNodeIdle_ready` needs of it, and, by the lower bounds of `rs`, that it holds no
messages (`SliceShape`, `k ≤ rs.outlb`) and no entries (`es ≠ [] → rs.unst`) once the
node is idle; and its read states with their facts (2026-10-13, persistent: from
`readyWithoutAccept`). (2026-10-16, stage R5: its hard state `hsOpt`, its entries `entsRO`,
its read states `readStatesPts`, no snapshot `nil`.) -/
def staleOk (γ : NodeNames) (rd : Ready) (rs : RNState) : IProp GF :=
  iprop(∃ (ce es : List EntryM) (k : Nat) (hrd : HardStateM),
    (⌜rd.SoftState' = null⌝ ∨ ∃ v : SoftState, rd.SoftState' ↦□ v) ∗
    hsOpt rd.HardState' hrd ∗
    entsRO rd.CommittedEntries' ce ∗ ownSliceCap Loc rd.CommittedEntries' (DFrac.own 1) ∗
    isCommitted γ.raft (rs.delivered ++ ce) ∗ entsRO rd.Entries' es ∗
    (∃ sts : List ReadStateM, readStatesPts rd.ReadStates' sts ∗
      [∗list] st ∈ sts, readStateOk γ.raft st) ∗
    ⌜rd.Snapshot' = null ∧
      (es ≠ [] → rs.unst = true) ∧ SliceShape rd.Messages' k ∧ k ≤ rs.outlb ∧
      (∀ e, ce.getLast? = some e → uint.Z e.Index' ≤ uint.Z rs.clb ∧
        uint.Z e.Index' = (rs.delivered.length : Int) + (ce.length : Int))⌝)

/-- A `Ready` `readyWithoutAccept` just computed: its outputs. (2026-10-16, stage R5: the
messages handed out (D8), owned at `readyDq`, with `rd.Messages`' slice and capacity; the
entries `entsRO`; the read states `readStatesPts`; the hard state `hsOpt`.) -/
def freshOk (γ : NodeNames) (rd : Ready) (rs : RNState) (ce es : List EntryM)
    (ms : List QMsg) : IProp GF :=
  iprop(entsRO rd.CommittedEntries' ce ∗ isCommitted γ.raft (rs.delivered ++ ce) ∗
    entsRO rd.Entries' es ∗ rd.Messages' ↦* ms.map QMsg.loc ∗
    ownSliceCap Loc rd.Messages' (DFrac.own 1) ∗
    ([∗list] q ∈ ms, msgOwn q.loc (readyDq q.st) q.st) ∗
    ([∗list] q ∈ ms, isRaftMsg γ.raft q.st) ∗
    (∃ sts : List ReadStateM, readStatesPts rd.ReadStates' sts ∗
      [∗list] st ∈ sts, readStateOk γ.raft st) ∗
    (∃ hrd : HardStateM, hsOpt rd.HardState' hrd) ∗
    ⌜(∀ q ∈ ms, uint.Z q.st.msg.Term' ≤ uint.Z rs.tc) ∧
     rd.Snapshot' = null⌝)

/-- Both halves of `rof`: no `Ready` handed out. -/
def rofFull (γ : NodeNames) : IProp GF :=
  iprop(∃ x : List EntryM × List EntryM × List EntryM,
    dghostVar γ.rof (DFrac.own (1 : Qp).half) x ∗ dghostVar γ.rof (DFrac.own (1 : Qp).half) x)

/-- `run`'s state besides the node, at the loop's head (`ac`: `advancec`, `rc`: `readyc`,
`rd`: `rd`): no `Ready` handed out (`ac` nil; then `rc` is nil or a stale `Ready` is
armed), or one handed out and its `Advance` awaited (`ac` is `n.advancec`). -/
def headRest (γ : NodeNames) (nv : node) (rs : RNState) (ac rc : GoChan) (rd : Ready) :
    IProp GF :=
  iprop(termLB γ.bud rs.tc ∗ ⌜rs.storage = γ.stor⌝ ∗ runCfg γ rs ∗
    ((⌜ac = chan.nil ∧ rs.steps = [] ∧ rs.unpersisted = []⌝ ∗
        dghostVar γ.dlv (DFrac.own (1 : Qp).half) rs.delivered ∗ rofFull γ ∗
        (⌜rc = chan.nil⌝ ∨ (⌜rc = nv.readyc'⌝ ∗ staleOk γ rd rs)))
     ∨ (⌜ac = nv.advancec' ∧ rc = chan.nil ∧ rs.unst = false⌝ ∗
        ∃ d ce : List EntryM, ⌜rs.delivered = d ++ ce⌝ ∗
          dghostVar γ.rof (DFrac.own (1 : Qp).half) (d, ce, rs.unpersisted))))

/-- `run`'s loop invariant, but for its local variables. -/
def runHead (γ : NodeNames) (id : w64) (nv : node) (ac rc : GoChan) (rd : Ready) : IProp GF :=
  iprop(∃ rs : RNState, ownRawNode γ.raft nv.rn' id rs ∗ headRest γ nv rs ac rc rd)

/-- `run`'s state after its first statement (`HasReady`, `readyWithoutAccept`): the node
may also be at a fresh `Ready` (`ownRawNodeReady`) or idle with a stale one armed. -/
def runMid (γ : NodeNames) (id : w64) (nv : node) (ac rc : GoChan) (rd : Ready) : IProp GF :=
  iprop((⌜ac = nv.advancec'⌝ ∗ runHead γ id nv ac rc rd) ∨
    (⌜ac = chan.nil⌝ ∗ ∃ rs : RNState, termLB γ.bud rs.tc ∗
      ⌜rs.storage = γ.stor ∧ rs.steps = [] ∧ rs.unpersisted = []⌝ ∗
      dghostVar γ.dlv (DFrac.own (1 : Qp).half) rs.delivered ∗ rofFull γ ∗ runCfg γ rs ∗
      ((⌜rc = chan.nil⌝ ∗ ownRawNode γ.raft nv.rn' id rs) ∨
       (⌜rc = nv.readyc'⌝ ∗ ∃ (ce es : List EntryM) (ms : List QMsg),
          ownRawNodeReady γ.raft nv.rn' id rs rd ce es ms false ∗ freshOk γ rd rs ce es ms) ∨
       (⌜rc = nv.readyc'⌝ ∗ ownRawNodeIdle γ.raft nv.rn' id rs ∗ staleOk γ rd rs))))

theorem headRest_termLB (γ : NodeNames) (nv : node) (rs : RNState) (ac rc : GoChan)
    (rd : Ready) :
    ⊢ headRest (GF := GF) γ nv rs ac rc rd -∗ termLB γ.bud rs.tc ∗ headRest γ nv rs ac rc rd := by
  iintro H
  unfold headRest
  icases H with ⟨#Hlb, H⟩
  iframe Hlb H

/-- (D19i part 1) The floor is not raised past `applied` at the loop's head (`runCfg_flw`). -/
theorem headRest_flw (γ : NodeNames) (nv : node) (rs : RNState) (ac rc : GoChan) (rd : Ready) :
    ⊢ headRest (GF := GF) γ nv rs ac rc rd -∗ ⌜rs.flw = false⌝ ∗ headRest γ nv rs ac rc rd := by
  iintro H
  unfold headRest
  icases H with ⟨#Hlb, %Hst, Hcfg, H⟩
  iunfold runCfg at Hcfg
  icases Hcfg with ⟨%Hm0, Hcfg⟩
  isplitr
  · ipureintro; exact Hm0.2.2
  iframe Hlb H
  isplitr
  · ipureintro; exact Hst
  iunfold runCfg
  iframe Hcfg
  ipureintro; exact Hm0

/-- A step changes only the node's term and (2026-10-17) the term ceiling, which the budget
covers. -/
theorem headRest_term (γ : NodeNames) (nv : node) (rs : RNState) (ac rc : GoChan) (rd : Ready)
    (t tc : w64) :
    ⊢ headRest (GF := GF) γ nv rs ac rc rd -∗ termLB γ.bud tc -∗
      headRest γ nv { { rs with tc := tc } with term := t } ac rc rd := by
  iintro H #Hlb
  unfold headRest
  icases H with ⟨-, %Hst, H⟩
  iframe Hlb
  isplitr
  · ipureintro; exact Hst
  iExactEq H
  rfl

/-- With no `Ready` handed out (`ac` nil). -/
theorem headRest_nil (γ : NodeNames) (nv : node) (rs : RNState) (rc : GoChan) (rd : Ready)
    (Hnn : nv.advancec' ≠ chan.nil) :
    ⊢ headRest (GF := GF) γ nv rs chan.nil rc rd -∗
      termLB γ.bud rs.tc ∗ ⌜rs.storage = γ.stor ∧ rs.steps = [] ∧ rs.unpersisted = []⌝ ∗
      dghostVar γ.dlv (DFrac.own (1 : Qp).half) rs.delivered ∗ rofFull γ ∗ runCfg γ rs ∗
      (⌜rc = chan.nil⌝ ∨ (⌜rc = nv.readyc'⌝ ∗ staleOk γ rd rs)) := by
  iintro H
  unfold headRest
  icases H with ⟨#Hlb, %Hst, Hcfg, (⟨%Hs, Hdlv, Hrof, Hrc⟩ | ⟨%Hs, -⟩)⟩
  · iframe Hlb Hdlv Hrof Hrc Hcfg
    ipureintro; exact ⟨Hst, Hs.2⟩
  · exact absurd Hs.1.symm Hnn

/-- With a `Ready` handed out (`ac` not nil): `runMid` as it is. -/
theorem runHead_mid_busy (γ : NodeNames) (id : w64) (nv : node) (ac rc : GoChan) (rd : Ready)
    (Hac : ac ≠ chan.nil) :
    ⊢ runHead (GF := GF) γ id nv ac rc rd -∗ runMid γ id nv ac rc rd := by
  iintro H
  unfold runMid
  ileft
  unfold runHead
  icases H with ⟨%rs, Hrn, Hrest⟩
  unfold headRest
  icases Hrest with ⟨#Hlb, %Hst, Hcfg, (⟨%Hs, Hdlv, Hrof, Hrc⟩ | ⟨%Hs, Hd⟩)⟩
  · exact absurd Hs.1 Hac
  isplitr
  · ipureintro; exact Hs.1
  iexists rs
  iframe Hrn Hlb Hcfg
  isplitr
  · ipureintro; exact Hst
  iright
  iframe Hd
  ipureintro; exact Hs

/-- Abandoning a fresh `Ready` (keeping it armed, `ownRawNodeReady_abandon_keep`), or
leaving the idle node: back to `runHead`. -/
theorem runMid_head (γ : NodeNames) (id : w64) (nv : node) (ac rc : GoChan) (rd : Ready) :
    ⊢ runMid (GF := GF) γ id nv ac rc rd -∗ runHead γ id nv ac rc rd := by
  iintro H
  unfold runMid
  icases H with (⟨-, H⟩ | ⟨%Hac, %rs, #Hlb, %Hrs, Hdlv, Hrof, Hcfg, H⟩)
  · iexact H
  obtain ⟨Hst, Hsteps, Hunp⟩ := Hrs
  unfold runHead
  icases H with (⟨%Hrc, Hrn⟩ | ⟨%Hrc, %ce, %es, %ms, Hrn, Hf⟩ | ⟨%Hrc, Hrn, Hstale⟩)
  · iexists rs
    iframe Hrn
    unfold headRest
    iframe Hlb Hcfg
    isplitr
    · ipureintro; exact Hst
    ileft
    iframe Hdlv Hrof
    isplitr
    · ipureintro; exact ⟨Hac, Hsteps, Hunp⟩
    ileft; ipureintro; exact Hrc
  · unfold freshOk
    icases Hf with ⟨#Hce, #Hcommitted, #Hents, Hmsgs, Hmsgs_cap, Hown, #Hmsgs_ok, #Hrsts, -,
      %Hfacts⟩
    ihave %Hshape := ownSlice_shape _ _ _ $$ Hmsgs
    icases ownRawNodeReady_abandon_keep γ.raft nv.rn' id rs rd ce es ms Hsteps Hunp
      $$ Hmsgs Hmsgs_cap Hown Hrn with ⟨Hce_cap, #Hrdsoft, ⟨%hrd, #Hrdh⟩, %n, %u, %c, %Hnuc, Hrn⟩
    iexists { rs with outlb := n, unst := u, clb := c }
    iframe Hrn
    unfold headRest
    rw [show runCfg γ { rs with outlb := n, unst := u, clb := c } = runCfg (GF := GF) γ rs
      from rfl]
    iframe Hlb Hcfg
    isplitr
    · ipureintro; exact Hst
    ileft
    iframe Hdlv Hrof
    isplitr
    · ipureintro; exact ⟨Hac, Hsteps, Hunp⟩
    iright
    isplitr
    · ipureintro; exact Hrc
    unfold staleOk
    iexists ce, es, ms.length, hrd
    iframe Hrdsoft Hrdh Hce Hce_cap Hcommitted Hents Hrsts
    ipureintro
    exact ⟨Hfacts.2, Hnuc.2.1, by simpa using Hshape, Hnuc.1, Hnuc.2.2⟩
  · iexists rs
    ihave Hrn := ownRawNodeIdle_ownRawNode γ.raft nv.rn' id rs $$ Hrn
    iframe Hrn
    unfold headRest
    iframe Hlb Hcfg
    isplitr
    · ipureintro; exact Hst
    ileft
    iframe Hdlv Hrof
    isplitr
    · ipureintro; exact ⟨Hac, Hsteps, Hunp⟩
    iright
    isplitr
    · ipureintro; exact Hrc
    iexact Hstale

/-- A `Ready`'s messages are of terms within the budget: at most the node's. (2026-10-16,
stage R5: with the messages' ownership, as `readyData` holds them.) -/
theorem readyMsgs_termLB (γ : NodeNames) (t : w64) (ms : List QMsg)
    (H : ∀ q ∈ ms, uint.Z q.st.msg.Term' ≤ uint.Z t) :
    ⊢ ([∗list] q ∈ ms, msgOwn (GF := GF) q.loc (readyDq q.st) q.st) -∗
      ([∗list] q ∈ ms, isRaftMsg (GF := GF) γ.raft q.st) -∗ termLB γ.bud t -∗
      [∗list] q ∈ ms, msgOwn q.loc (readyDq q.st) q.st ∗ isRaftMsg γ.raft q.st ∗
        termLB γ.bud q.st.msg.Term' := by
  induction ms with
  | nil =>
    iintro - - -
    iapply BigSepL.bigSepL_nil.2
    iempintro
  | cons q ms ih =>
    iintro Ho Hl #Hlb
    icases BigSepL.bigSepL_cons.1 $$ Ho with ⟨Hq, Ho⟩
    icases BigSepL.bigSepL_cons.1 $$ Hl with ⟨Hm, Hl⟩
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hq Hm]
    · iframe Hq Hm
      iapply termLB_le γ.bud t q.st.msg.Term' (H q (List.mem_cons_self ..)) $$ Hlb
    · iapply ih (fun m' hm => H m' (List.mem_cons_of_mem _ hm)) $$ Ho Hl Hlb

/-- What `readyc` and `advancec` may be. -/
theorem runMid_chans (γ : NodeNames) (id : w64) (nv : node) (ac rc : GoChan) (rd : Ready) :
    ⊢ runMid (GF := GF) γ id nv ac rc rd -∗
      ⌜(rc = chan.nil ∨ rc = nv.readyc') ∧ (ac = chan.nil ∨ ac = nv.advancec')⌝ := by
  iintro H
  unfold runMid
  icases H with (⟨%Hac, H⟩ | ⟨%Hac, %rs, -, -, -, -, -, H⟩)
  · unfold runHead
    icases H with ⟨%rs, -, Hrest⟩
    unfold headRest
    icases Hrest with ⟨-, -, -, (⟨%Hs, -, -, (%Hrc | ⟨%Hrc, -⟩)⟩ | ⟨%Hs, -⟩)⟩
    · ipureintro; exact ⟨.inl Hrc, .inr Hac⟩
    · ipureintro; exact ⟨.inr Hrc, .inr Hac⟩
    · ipureintro; exact ⟨.inl Hs.2.1, .inr Hac⟩
  icases H with (⟨%Hrc, -⟩ | ⟨%Hrc, -⟩ | ⟨%Hrc, -⟩)
  · ipureintro; exact ⟨.inl Hrc, .inl Hac⟩
  · ipureintro; exact ⟨.inr Hrc, .inl Hac⟩
  · ipureintro; exact ⟨.inr Hrc, .inl Hac⟩

/-- `readyc` armed: a fresh `Ready`, or an idle node and a stale one. -/
theorem runMid_ready (γ : NodeNames) (id : w64) (nv : node) (ac : GoChan) (rd : Ready)
    (Hnn : nv.readyc' ≠ chan.nil) (Hnn' : nv.advancec' ≠ chan.nil) :
    ⊢ runMid (GF := GF) γ id nv ac nv.readyc' rd -∗
      ⌜ac = chan.nil⌝ ∗ ∃ rs : RNState, termLB γ.bud rs.tc ∗
        ⌜rs.storage = γ.stor ∧ rs.steps = [] ∧ rs.unpersisted = []⌝ ∗
        dghostVar γ.dlv (DFrac.own (1 : Qp).half) rs.delivered ∗ rofFull γ ∗ runCfg γ rs ∗
        ((∃ (ce es : List EntryM) (ms : List QMsg),
            ownRawNodeReady γ.raft nv.rn' id rs rd ce es ms false ∗ freshOk γ rd rs ce es ms) ∨
         (ownRawNodeIdle γ.raft nv.rn' id rs ∗ staleOk γ rd rs)) := by
  iintro H
  unfold runMid
  icases H with (⟨%Hac, H⟩ | ⟨%Hac, %rs, #Hlb, %Hrs, Hdlv, Hrof, Hcfg, H⟩)
  · unfold runHead
    icases H with ⟨%rs, -, Hrest⟩
    unfold headRest
    icases Hrest with ⟨-, -, -, (⟨%Hs, -⟩ | ⟨%Hs, -⟩)⟩
    · exact absurd (Hac.symm.trans Hs.1) Hnn'
    · exact absurd Hs.2.1 Hnn
  isplitr
  · ipureintro; exact Hac
  iexists rs
  iframe Hlb Hdlv Hrof Hcfg
  isplitr
  · ipureintro; exact Hrs
  icases H with (⟨%Hrc, -⟩ | ⟨%Hrc, Hf⟩ | ⟨%Hrc, Hrn, Hstale⟩)
  · exact absurd Hrc Hnn
  · ileft; iexact Hf
  · iright; iframe Hrn Hstale

/-- `advancec` armed: a `Ready` handed out. -/
theorem runMid_busy (γ : NodeNames) (id : w64) (nv : node) (rc : GoChan) (rd : Ready)
    (Hnn : nv.advancec' ≠ chan.nil) :
    ⊢ runMid (GF := GF) γ id nv nv.advancec' rc rd -∗
      ∃ (rs : RNState) (d ce : List EntryM), ownRawNode γ.raft nv.rn' id rs ∗
        termLB γ.bud rs.tc ∗ runCfg γ rs ∗
        ⌜rs.storage = γ.stor ∧ rc = chan.nil ∧ rs.unst = false ∧ rs.delivered = d ++ ce⌝ ∗
        dghostVar γ.rof (DFrac.own (1 : Qp).half) (d, ce, rs.unpersisted) := by
  iintro H
  unfold runMid
  icases H with (⟨-, H⟩ | ⟨%Hac, -⟩)
  · unfold runHead
    icases H with ⟨%rs, Hrn, Hrest⟩
    unfold headRest
    icases Hrest with ⟨#Hlb, %Hst, Hcfg, (⟨%Hs, -⟩ | ⟨%Hs, %d, %ce, %Hd, Hrof⟩)⟩
    · exact absurd Hs.1 Hnn
    iexists rs, d, ce
    iframe Hrn Hlb Hrof Hcfg
    ipureintro; exact ⟨Hst, Hs.2.1, Hs.2.2, Hd⟩
  · exact absurd Hac Hnn

/-- The leader fields, in any of `run`'s states. -/
theorem runMid_lead (γ : NodeNames) (id : w64) (nv : node) (ac rc : GoChan) (rd : Ready)
    (r : Loc) :
    ⊢ runMid (GF := GF) γ id nv ac rc rd -∗ nv.rn'.[RawNode, go!"raft"] ↦□ r -∗
      leadFields r (runMid γ id nv ac rc rd) := by
  iintro H #Hr
  unfold runMid
  icases H with (⟨%Hac, H⟩ | ⟨%Hac, %rs, #Hlb, %Hrs, Hdlv, Hrof, Hcfg, H⟩)
  · unfold runHead
    icases H with ⟨%rs, Hrn, Hrest⟩
    ihave Hlf := ownRawNode_lead γ.raft nv.rn' id rs r $$ Hrn Hr
    iunfold leadFields at Hlf
    icases Hlf with ⟨%ld, %t, Hl, Ht, Hback⟩
    unfold leadFields
    iexists ld, t
    iframe Hl Ht
    iintro Hl Ht
    ileft
    isplitr
    · ipureintro; exact Hac
    iexists rs
    iframe Hrest
    iapply Hback $$ Hl Ht
  icases H with (⟨%Hrc, Hrn⟩ | ⟨%Hrc, %ce, %es, %ms, Hrn, Hf⟩ | ⟨%Hrc, Hrn, Hstale⟩)
  · ihave Hlf := ownRawNode_lead γ.raft nv.rn' id rs r $$ Hrn Hr
    iunfold leadFields at Hlf
    icases Hlf with ⟨%ld, %t, Hl, Ht, Hback⟩
    unfold leadFields
    iexists ld, t
    iframe Hl Ht
    iintro Hl Ht
    iright
    isplitr
    · ipureintro; exact Hac
    iexists rs
    iframe Hlb Hdlv Hrof Hcfg
    isplitr
    · ipureintro; exact Hrs
    ileft
    isplitr
    · ipureintro; exact Hrc
    iapply Hback $$ Hl Ht
  · ihave Hlf := ownRawNodeReady_lead γ.raft nv.rn' id rs rd ce es ms false r $$ Hrn Hr
    iunfold leadFields at Hlf
    icases Hlf with ⟨%ld, %t, Hl, Ht, Hback⟩
    unfold leadFields
    iexists ld, t
    iframe Hl Ht
    iintro Hl Ht
    iright
    isplitr
    · ipureintro; exact Hac
    iexists rs
    iframe Hlb Hdlv Hrof Hcfg
    isplitr
    · ipureintro; exact Hrs
    iright; ileft
    isplitr
    · ipureintro; exact Hrc
    iexists ce, es, ms
    iframe Hf
    iapply Hback $$ Hl Ht
  · ihave Hlf := ownRawNodeIdle_lead γ.raft nv.rn' id rs r $$ Hrn Hr
    iunfold leadFields at Hlf
    icases Hlf with ⟨%ld, %t, Hl, Ht, Hback⟩
    unfold leadFields
    iexists ld, t
    iframe Hl Ht
    iintro Hl Ht
    iright
    isplitr
    · ipureintro; exact Hac
    iexists rs
    iframe Hlb Hdlv Hrof Hcfg
    isplitr
    · ipureintro; exact Hrs
    iright; iright
    isplitr
    · ipureintro; exact Hrc
    iframe Hstale
    iapply Hback $$ Hl Ht

end states

/-! ## The configuration `run` shares with the driver (2026-10-15, stage N) -/

section cfgshare
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

omit ffi [FfiInterp ffi] [FfiSemantics ext ffi] go_gctx in
/-- A conf change's premises on the driver's view (a prefix `D` of the committed log handed
out, the configuration index `ca` of the last applied conf change) carry over to `run`'s
`RawNode`, whose committed log `D'` extends `D` and whose configuration index `ca'` is past `ca`
over no conf entry: the conf entry at `k` cannot be below `ca'`. -/
theorem dynCCPreOp_transfer {dec : CCDec} {D D' : List EntryM} {ca ca' : Nat}
    {cfg : CCState} {op : CCOp} {k : Nat} {e : EntryM} {cs' : CCState}
    (Hp : DynCCPreOp dec D ca cfg op k e cs') (Hpre : D <+: D') (Hca : ca ≤ ca')
    (Hnc : NoConfIn D' ca ca') : DynCCPreOp dec D' ca' cfg op k e cs' := by
  obtain ⟨Hk1, Hk2, Hke, Hconf, Hnoc, Hdec, Hstep, Hal⟩ := Hp
  have Hke' : D'[k]? = some e := prefix_getElem? Hpre Hke
  have Hlen : D.length ≤ D'.length := Hpre.length_le
  have Hk1' : ca' ≤ k := by
    refine Nat.le_of_not_lt fun h => ?_
    exact Hnc k e Hk1 h Hke' Hconf
  refine ⟨Hk1', by omega, Hke', Hconf, ?_, ?_, Hstep, Hal⟩
  · intro j x hj1 hj2 hx
    have hx' : D[j]? = some x := by
      obtain ⟨t, rfl⟩ := Hpre
      rw [List.getElem?_append_left (by omega)] at hx
      exact hx
    exact Hnoc j x (by omega) hj2 hx'
  · obtain ⟨t, rfl⟩ := Hpre
    rw [List.take_append_of_le_length (by omega)]
    exact Hdec

omit ffi [FfiInterp ffi] [FfiSemantics ext ffi] go_gctx in
/-- `NoConfIn` over two adjacent ranges. -/
theorem NoConfIn_trans {D : List EntryM} {a b c : Nat} (H1 : NoConfIn D a b)
    (H2 : NoConfIn D b c) : NoConfIn D a c := by
  intro k e hk1 hk2 he
  by_cases h : k < b
  · exact H1 k e hk1 h he
  · exact H2 k e (by omega) hk2 he

omit ffi [FfiInterp ffi] [FfiSemantics ext ffi] go_gctx in
/-- `NoConfIn` over a smaller range. -/
theorem NoConfIn_mono {D : List EntryM} {a b a' b' : Nat} (H : NoConfIn D a b)
    (ha : a ≤ a') (hb : b' ≤ b) : NoConfIn D a' b' := by
  intro k e hk1 hk2 he
  exact H k e (by omega) (by omega) he

omit ffi [FfiInterp ffi] [FfiSemantics ext ffi] go_gctx in
theorem NoConfIn_empty (D : List EntryM) (a : Nat) : NoConfIn D a a := by
  intro k e hk1 hk2 _
  omega

/-- The node's mode, out of `run`'s state. -/
theorem headRest_mode (γ : NodeNames) (nv : node) (rs : RNState) (ac rc : GoChan) (rd : Ready) :
    ⊢ headRest (GF := GF) γ nv rs ac rc rd -∗ ⌜rs.mode = γ.mode⌝ ∗ headRest γ nv rs ac rc rd := by
  iintro H
  unfold headRest
  icases H with ⟨#Hlb, %Hst, Hcfg, H⟩
  iunfold runCfg at Hcfg
  icases Hcfg with ⟨%Hm, Hcfg⟩
  isplitr
  · ipureintro; exact Hm.1
  iframe Hlb
  isplitr
  · ipureintro; exact Hst
  iframe H
  iunfold runCfg
  iframe Hcfg
  ipureintro; exact Hm

/-- `runCfg` out of `run`'s state, to be put back at a new configuration and configuration
index (the rest of the state does not read them). -/
theorem headRest_cfg (γ : NodeNames) (nv : node) (rs : RNState) (ac rc : GoChan) (rd : Ready)
    (cfg' : CCState) (ca' : Nat) :
    ⊢ headRest (GF := GF) γ nv rs ac rc rd -∗ runCfg γ rs ∗
      (runCfg γ { rs with cfg := cfg', capplied := ca' } -∗
        headRest γ nv { rs with cfg := cfg', capplied := ca' } ac rc rd) := by
  iintro H
  unfold headRest
  icases H with ⟨#Hlb, %Hst, Hcfg, H⟩
  iframe Hcfg
  iintro Hcfg
  iframe Hlb Hcfg
  isplitr
  · ipureintro; exact Hst
  iExactEq H
  rfl

/-- The `confc` arm in the dynamic mode: the driver's view of the configuration (`cap`'s half)
agrees with `run`'s, so the change's premises hold of the `RawNode` (`dynCCPreOp_transfer`);
the shared configuration moves to the entry applied, `(k + 1, cs')`. -/
theorem runCfg_confc (γ : NodeNames) (rs : RNState) (ds : List EntryM) (ca : Nat)
    (cfg : CCState) (op : CCOp) (k : Nat) (e : EntryM) (cs' : CCState) (dec : CCDec)
    (Hp : DynCCPreOp dec ds ca cfg op k e cs') :
    ⊢ runCfg (GF := GF) γ rs -∗ monoListLbOwn γ.dlm ds -∗
      dghostVar γ.cap (DFrac.own (1 : Qp).half) (ca, cfg) -∗
      ⌜DynCCPreOp dec rs.delivered rs.capplied rs.cfg op k e cs'⌝ ∗
      |==> (runCfg γ { rs with cfg := cs', capplied := k + 1 } ∗
        dghostVar γ.cap (DFrac.own (1 : Qp).half) (k + 1, cs') ∗ monoNatLbOwn γ.cam (k + 1)) := by
  iintro Hcfg #Hlb Hcap
  iunfold runCfg at Hcfg
  icases Hcfg with ⟨%Hm, Hdlm, %ca_r, Hcap_r, Hcam, %Hinv⟩
  ihave %Heq := dghostVar_agree _ _ _ _ _ $$ Hcap_r Hcap
  simp only [Prod.mk.injEq] at Heq
  obtain ⟨rfl, rfl⟩ := Heq
  ihave %Hpfx := mono_list_auth_lb_valid _ _ _ _ $$ Hdlm Hlb
  have Hp' := dynCCPreOp_transfer Hp Hpfx.2 Hinv.1 Hinv.2
  isplitr
  · ipureintro; exact Hp'
  obtain ⟨Hk1, Hk2, -⟩ := Hp'
  imod dghostVar_update_halves (k + 1, cs') γ.cap _ _ $$ Hcap_r Hcap with ⟨Hcap_r, Hcap⟩
  imod mono_nat_own_update (k + 1) (by omega) $$ Hcam with ⟨Hcam, #Hlb'⟩
  imodintro
  iframe Hcap Hlb'
  iunfold runCfg
  iframe Hdlm
  isplitr
  · ipureintro; exact ⟨Hm.1, by simp only; omega, Hm.2.2⟩
  iexists k + 1
  iframe Hcap_r Hcam
  ipureintro
  exact ⟨Nat.le_refl _, NoConfIn_empty _ _⟩

/-- The `readyc` arm: the committed log handed out grows by the `Ready`'s committed entries
(the configuration and its index unchanged); a lower bound of it for the driver. -/
theorem runCfg_extend (γ : NodeNames) (rs rs' : RNState) (ce : List EntryM)
    (Hd : rs'.delivered = rs.delivered ++ ce) (Hm : rs'.mode = rs.mode) (Hc : rs'.cfg = rs.cfg)
    (Hca : rs'.capplied = rs.capplied) (Hfw : rs'.flw = rs.flw) :
    ⊢ runCfg (GF := GF) γ rs ==∗ runCfg γ rs' ∗ monoListLbOwn γ.dlm (rs.delivered ++ ce) := by
  iintro Hcfg
  iunfold runCfg at Hcfg
  icases Hcfg with ⟨%Hm0, Hdlm, %ca_r, Hcap_r, Hcam, %Hinv⟩
  imod monoListAuthOwn_update_app ce $$ Hdlm with ⟨Hdlm, #Hlb⟩
  imodintro
  iframe Hlb
  iunfold runCfg
  rw [Hd, Hm, Hc, Hca]
  iframe Hdlm
  isplitr
  · ipureintro
    refine ⟨Hm0.1, ?_, by rw [Hfw]; exact Hm0.2.2⟩
    have := Hm0.2.1
    simp only [List.length_append]; omega
  iexists ca_r
  iframe Hcap_r Hcam
  ipureintro
  exact ⟨Hinv.1, NoConfIn_prefix (List.prefix_append _ _) Hm0.2.1 Hinv.2⟩

/-- (D19i part 1) The floor is not raised past `applied` (`RNState.flw`). -/
theorem runCfg_flw (γ : NodeNames) (rs : RNState) :
    ⊢ runCfg (GF := GF) γ rs -∗ ⌜rs.flw = false⌝ ∗ runCfg γ rs := by
  iintro Hcfg
  iunfold runCfg at Hcfg
  icases Hcfg with ⟨%Hm0, Hdlm, Hrest⟩
  isplitr
  · ipureintro; exact Hm0.2.2
  iunfold runCfg
  iframe Hdlm Hrest
  ipureintro; exact Hm0

/-- The `advancec` arm, before `Advance`: the driver's A1 (no conf entry of the committed log
handed out past its configuration index, a lower bound of `run`'s) is A1 at the `RawNode`. -/
theorem runCfg_a1 (γ : NodeNames) (rs : RNState) (ca_d : Nat) :
    ⊢ runCfg (GF := GF) γ rs -∗ monoNatLbOwn γ.cam ca_d -∗
      ⌜γ.mode.isDyn = true → NoConfIn rs.delivered ca_d rs.delivered.length⌝ -∗
      ⌜rs.mode.isDyn = true → NoConfIn rs.delivered rs.capplied rs.delivered.length⌝ ∗
      runCfg γ rs := by
  iintro Hcfg #Hlb %HA
  iunfold runCfg at Hcfg
  icases Hcfg with ⟨%Hm0, Hdlm, %ca_r, Hcap_r, Hcam, %Hinv⟩
  ihave %Hle := monoNatLbOwn_valid _ _ _ _ $$ Hcam Hlb
  isplitr
  · ipureintro
    intro hd
    rw [Hm0.1] at hd
    exact NoConfIn_mono (HA hd) (by omega) (Nat.le_refl _)
  iunfold runCfg
  iframe Hdlm
  isplitr
  · ipureintro; exact Hm0
  iexists ca_r
  iframe Hcap_r Hcam
  ipureintro; exact Hinv

/-- The `advancec` arm, after `Advance`: the configuration index moved up to at most the
committed log handed out, over no conf entry (A1), not at all in the static mode. -/
theorem runCfg_advance (γ : NodeNames) (rs rs' : RNState)
    (Hd : rs'.delivered = rs.delivered) (Hm : rs'.mode = rs.mode) (Hc : rs'.cfg = rs.cfg)
    (Hfw : rs'.flw = false)
    (Hca : rs.capplied ≤ rs'.capplied ∧ rs'.capplied ≤ max rs.capplied rs.delivered.length ∧
      (rs.mode = .static → rs'.capplied = rs.capplied))
    (HA1 : rs.mode.isDyn = true → NoConfIn rs.delivered rs.capplied rs.delivered.length) :
    ⊢ runCfg (GF := GF) γ rs -∗ runCfg γ rs' := by
  iintro Hcfg
  iunfold runCfg at Hcfg
  icases Hcfg with ⟨%Hm0, Hdlm, %ca_r, Hcap_r, Hcam, %Hinv⟩
  iunfold runCfg
  rw [Hd, Hm, Hc]
  iframe Hdlm
  have Hcases : rs'.capplied = rs.capplied ∨
      (rs.mode.isDyn = true ∧ rs'.capplied ≤ rs.delivered.length) := by
    cases hm : rs.mode with
    | static => exact .inl (Hca.2.2 hm)
    | dyn _ _ _ _ =>
      right; refine ⟨rfl, ?_⟩
      have := Hca.2.1; have := Hm0.2.1; omega
  isplitr
  · ipureintro
    refine ⟨Hm0.1, ?_, Hfw⟩
    rcases Hcases with h | ⟨-, h⟩
    · rw [h]; exact Hm0.2.1
    · exact h
  iexists ca_r
  iframe Hcap_r Hcam
  ipureintro
  rcases Hcases with h | ⟨hd, h⟩
  · rw [h]; exact Hinv
  · refine ⟨by have := Hca.1; omega, ?_⟩
    exact NoConfIn_trans Hinv.2 (NoConfIn_mono (HA1 hd) (Nat.le_refl _) h)

end cfgshare

end EtcdGrove
end Perennial
