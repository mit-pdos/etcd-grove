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
`r.applyConfChange` takes a `*pb.ConfChangeV2` (`ownConfChangeV2`, given back) and returns a fresh
`*pb.ConfState` (`csPts cs 1 … true`); the run loop's states over the new `Ready` fields
(`staleOk`/`freshOk`: `hsOpt`, `entsRO`, `readStatesPts`, `rd.Snapshot' = null`, the messages
handed out owned).

**D22 S-d4 (2026-10-21).** `run` steps a `MsgSnap` at a node that takes snapshots
(`wp_rn_raft_Step_net`'s snapshot case, `RawNode.Step`'s), and hands out a snapshot `Ready`: a
fresh `Ready` carries its loan (`freshOk`'s `rdSnapOut`), an abandoned one with a snapshot raises
`unst` (`ownRawNodeReady_abandon_keep`), so a stale one never has one; `runCfg`'s authority follows
the loan's committed log (`rsDlv`, `runCfg_extend`, `runCfg_advance`).
-/
module

public import Proof.go_etcd_io.raft.v3.InvNodeChan
public import Spec.go_etcd_io.raft.v3.raft__Step
public import Spec.go_etcd_io.raft.v3.raft__applyConfChange
public import Proof.go_etcd_io.raft.v3.InvRawnodeC
-- `Step.commit_mono`
public import Proof.go_etcd_io.raft.v3.Protocol.Facts
import all Proof.go_etcd_io.raft.v3.InvNodeChan
public import Proof.go_etcd_io.raft.v3.InvRawnodeReady
public import Proof.go_etcd_io.raft.v3.InvApplyConf
public import Spec.go_etcd_io.raft.v3.RawNode__ProposeConfChange

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
variable [GooseExts] [GooseSemantics] [GooseInterp]
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
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
  icases ownRaftPhysC_view c r id s $$ H with ⟨%rss, %sl1, %sl2, %ms1, %ms2, Hv⟩
  iNamed Hv
  isplitl [Hf_lead]
  · iexact Hf_lead
  isplitl [Hf_Term]
  · iexact Hf_Term
  iintro Hl Ht
  ihave H := Hclose $$ %sl1 %sl2 %ms1 %ms2 %s.outbox %s.logst %s.gh %rss %s.rd Ht Hf_Vote
    Hf_readStates HreadStates HreadStates_cap %(And.intro rfl rfl) Hf_raftLog Hf_state Hl Hf_msgs Hmsgs Hmsgs_cap Hf_msgsAA HmsgsAA HmsgsAA_cap Houtbox
    %HmsgsAA_ok %Hout_term %Hgh_out %(Hgh_unst.1) %(⟨rfl, Hgh_unst.2.1, fun _ h => h⟩) %(fun _ => Int.le_refl _) %Hxf Hscert Hlog
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
    Hstok Htrm Hstor Hpvoff Hrs_out Hrs_unst Hrs_clb Hrnfl Hloan
    Hsdt $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hsteps_cap Hpend Hdeliv Hstrecs Hloanc Hsloc

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
    Hsnap Hstok Htrm Hstor Hpvoff Hrs_out Hrs_unst Hrs_clb Hrnfl Hloan Hsdt Hidle
    $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hsteps_cap Hpend Hdeliv Hstrecs Hloanc Hsloc

/-- The fields of the raft struct `isNodeChan` shares, out of a node. -/
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
    Hstok Htrm Hstor Hpvoff Hrs_out Hrs_unst Hrs_clb Hrnfl Hloan
    Hsdt $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hsteps_cap Hpend Hdeliv Hstrecs Hloanc Hsloc

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
    (ce es : List EntryM) (ms : List QMsg) (h : Bool) (r : Loc) (L : Option SnapLoan := none) :
    ⊢ ownRawNodeReady (GF := GF) γ rn id rs rd ce es ms h L -∗ rn.[RawNode, go!"raft"] ↦□ r -∗
      leadFields r (ownRawNodeReady γ rn id rs rd ce es ms h L) := by
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
    Hrdrs Hce Hce_cap Hents Hrdz Hsloc
  isplitl
  · iunfold ownRaftPhysReady
    iexists rsl, sl1, sl2, ms1, ms2
    simp only [named]
    iframe Hf_id Hf_Term Hf_Vote Hf_readStates HreadStates HreadStates_cap Hf_raftLog Hf_state
      Hf_lead Hf_msgs Hf_msgsAA HmsgsAA HmsgsAA_cap Hself Hother Hlog Hundo Hclose Hscert
    ipureintro
    exact ⟨Houtbox, HmsgsAA_ok, Hout_term, Hgh_out, Hgh_unst, Hxf, Hmslen⟩
  ipureintro
  exact ⟨Hwf, Hin, Hal, Hasync, Hdlen, Hunp, Hsnap, Hloan, Htrm, Hstor, Hpvoff, Hrs_out, Hrs_unst,
    Hrs_clb, Hrnfl, Hceok, Hes, Hrdc, Hprc, Hnsout, Hsdt⟩

/-! ## Abandoning a `Ready`, keeping it armed -/

/-- `ownRawNodeReady_abandon`, also giving back what of the `Ready` `ownRawNodeIdle_ready`
takes should `run` send it after all: its committed entries' capacity and its soft
state. (2026-10-16, stage R5: and its hard state; the messages handed out come back at
`readyDq` with `rd.Messages`' slice and capacity.) (D22 S-d4, 2026-10-21) A `Ready` with a
snapshot (`L`) raises the lower bound `unst` too (the ghost state admits it, `GhLogOk`: a snapshot
is pending): the node is then not idle (`ownRawNodeIdle_facts`), so `run` never sends a stale
`Ready` with a snapshot -- `HasReady` reports the pending snapshot, and `run` computes a fresh one. -/
theorem ownRawNodeReady_abandon_keep (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState)
    (rd : Ready) (ce es : List EntryM) (ms : List QMsg) (L : Option SnapLoan)
    (Hsteps0 : rs.steps = []) (Hunp0 : rs.unpersisted = []) :
    ⊢ rd.Messages' ↦* ms.map QMsg.loc -∗ ownSliceCap Loc rd.Messages' (DFrac.own 1) -∗
      ([∗list] q ∈ ms, msgOwn q.loc (readyDq q.st) q.st) -∗
      ownRawNodeReady (GF := GF) γ rn id rs rd ce es ms false L -∗
      ownSliceCap Loc rd.CommittedEntries' (DFrac.own 1) ∗
      (⌜rd.SoftState' = null⌝ ∨ ∃ v : SoftState, rd.SoftState' ↦□ v) ∗
      (∃ hrd : HardStateM, hsOpt rd.HardState' hrd ∗ phsWit γ hrd) ∗
      ∃ (n : Nat) (u : Bool) (c : w64),
        ⌜ms.length ≤ n ∧ (es ≠ [] → u = true) ∧ (L.isSome = true → u = true) ∧
         (∀ e, ce.getLast? = some e → uint.Z e.Index' ≤ uint.Z c ∧
           uint.Z e.Index' = (rs.delivered.length : Int) + (ce.length : Int))⌝ ∗
        ownRawNode γ rn id { rs with outlb := n, unst := u, clb := c } := by
  iintro Hmsgs Hmsgs_cap Hown H
  iunfold ownRawNodeReady at H
  icases H with ⟨%s, %cf, %fp, %rnv, %sv, %hprev, H⟩
  iNamed H
  -- (D22 S-d4) with a snapshot, one is pending
  ihave %Hrsn : ⌜L.isSome = true → s.logst.snap ≠ none⌝ $$ [Hrdz]
  · cases L with
    | none => ipureintro; intro h; cases h
    | some l =>
      iunfold rdSnapRel at Hrdz
      icases Hrdz with ⟨-, -, %H⟩
      ipureintro; intro _; rw [H.2.1]; simp
  iclear Hrdz
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
  ihave Hlog : ownRaftLog s.log s.logst $$ [Hlog]
  · iExactEq Hlog; rfl
  let g : NGhost :=
    { s.gh with
      outlb := ms1.length + ms2.length,
      unst := decide (nextUnstable s.logst ≠ [] ∨ L.isSome = true) }
  ihave Hphys := Hclose $$ %sl1 %sl2 %ms1 %ms2 %s.outbox %s.logst %g %rsl %s.rd Hf_Term Hf_Vote
    Hf_readStates HreadStates HreadStates_cap %(And.intro rfl rfl)
    Hf_raftLog Hf_state Hf_lead Hf_msgs Hm1 Hc1 Hf_msgsAA HmsgsAA HmsgsAA_cap
    Hob %HmsgsAA_ok %Hout_term %(Nat.le_refl _)
    %(⟨fun h => (of_decide_eq_true h).imp (fun x => x) Hrsn, Hgh_unst.1.2⟩ : GhLogOk g s.logst)
    %(⟨rfl, fun _ => ⟨rfl, rfl, rfl, Int.le_refl _⟩, fun _ h => h⟩ :
      g.ns = s.gh.ns ∧ LogNsKeep s s.logst ∧ ∀ m ∈ s.outbox, m ∈ s.outbox)
    %(fun _ => Int.le_refl _) %(Hxf.of_fields rfl rfl rfl rfl) Hscert Hlog
  ihave #Hdeliv : isCommitted γ rs.delivered $$ []
  · iapply isCommitted_mono γ rs.delivered (rs.delivered ++ ce) (List.prefix_append _ _)
      $$ Hcommitted
  ihave Hpend : lentPend rs.slent (pendList γ id ([] : List Loc) rs.steps) $$ []
  · iapply lentPend_none Hloan.2; rw [Hsteps0]; iapply pendList_nil
  ihave #Hlc := loanCom_none γ Hloan.2
  iexists ms1.length + ms2.length, decide (nextUnstable s.logst ≠ [] ∨ L.isSome = true),
    s.logst.committed
  isplitr
  · ipureintro
    refine ⟨Hmslen, fun h => by rw [Hes] at h; exact decide_eq_true (.inl h),
      fun h => decide_eq_true (.inr h), fun e He => ?_⟩
    obtain ⟨-, H2, H3⟩ := Hceok e He
    refine ⟨H2, ?_⟩
    rw [H3, Hdlen]
    have := uint_Z_nonneg s.logst.applying
    omega
  let rs' : RNState :=
    { rs with
      outlb := ms1.length + ms2.length,
      unst := decide (nextUnstable s.logst ≠ [] ∨ L.isSome = true),
      clb := s.logst.committed }
  let s' : NState := { s with outbox := s.outbox, logst := s.logst, gh := g }
  ihave Hghost := ownStepGhost_congr γ _ cf id (s := s) (s' := s') rfl rfl rfl rfl $$ Hghost
  iapply ownRawNode_intro γ rn id rs' s' cf fp rnv sv hprev [] Hwf Hin Hal Hasync Hdlen
    (Hunp0.trans Hunp.symm) Hsnap (by show StepsOk _ rs.steps; rw [Hsteps0]; trivial) Htrm
    Hstor Hpvoff rfl rfl
    (Int.le_refl _) ⟨Hrnfl.1, fun h => absurd Hrnfl.2 (Int.not_le.2 h)⟩ Hloan.1
    Hsdt $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hsteps_cap Hpend Hdeliv Hstrecs Hlc Hsloc

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
variable [GooseExts] [GooseSemantics] [GooseInterp]
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
`st`.) (D22 S-d4, 2026-10-21) A `MsgSnap` too, as `RawNode.Step` takes it (until then a premise
`Type ≠ MsgSnap`): outside the no-snapshot mode, (2026-10-28, stage U3c) in either mode (until then
the static mode only, `DynNoSnap`), with its snapshot's facts and certificate (`"#Hsnap"`); after it
a snapshot may be pending (`psnap`). -/
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
    -- (2026-10-19, D21 M2r) a transfer request only outside the cluster's no-transfer mode
    (Hxt : st.msg.Type' = MsgTransferLeader → γ.reNoXfer = false)
    -- (D22 S-d4) a snapshot only outside the cluster's no-snapshot mode (`RawNode.Step`'s; until
    -- then, D22 S-c, no snapshot at all)
    (Hsnp : st.msg.Type' = MsgSnap → γ.reNoSnap = false) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        ownRawNode γ rn id rs ∗ rn.[RawNode, go!"raft"] ↦□ r ∗
        msgIn ml DFrac.discard st ∗
        -- (D22 S-d4) but a snapshot's, whose abstraction is `absSnap` (below)
        □ (∀ ty, ⌜mtypeOf st.msg.Type' = some ty⌝ -∗ ⌜ty ≠ .snap⌝ -∗
          isMessage γ (absMsg ty st.msg st.ents st.ctx)) ∗
        -- (D22 S-d4) a snapshot's facts and certificate, as `RawNode.Step`'s `"#Hsnap"`
        □ (⌜st.msg.Type' = MsgSnap⌝ -∗
           ∃ (sv : SnapshotM) (scfg : CSLists),
             ⌜st.snap = some sv ∧ scfg = sv.Metadata'.ConfState'.lists ∧
               uint.Z sv.Metadata'.Index' < 2^61⌝ ∗
             isMessageC γ (absSnap st.msg sv scfg) ∗ snapDataOk γ sv.Metadata'.Index' sv.Data' ∗
             -- (2026-10-26, D22 J2) its receiver-local fact
             snapLocal γ id sv.Metadata'.Index') ∗
        rdCred γ (if st.msg.Type' = MsgReadIndex then 1 else 0) ∗ £ 1 }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #ml))
    {{ (err : GoInterface) (t : w64), RET #err;
        ownRawNode γ rn id
          { rs with term := t, psnap := rs.psnap || decide (st.msg.Type' = MsgSnap) } ∗
        ⌜uint.Z rs.term ≤ uint.Z t ∧ uint.Z t ≤ uint.Z rs.tc ∧
          (st.msg.Type' ≠ MsgPreVoteResp →
            uint.Z t ≤ max (uint.Z rs.term) (uint.Z st.msg.Term') +
              (if st.msg.Type' = MsgTimeoutNow then 1 else 0))⌝ }} := by
  rcases st with ⟨m, ents, sn, ctx, rsp⟩
  have Hok0 := Hok
  simp only [NetMsgOk] at Hok0 Htn Hmtc Hpvb Hxt Hsnp ⊢
  obtain ⟨Hty, -⟩ := Hok0
  have Hps' : (rs.psnap || decide (m.Type' = MsgSnap)) = false → rs.psnap = false :=
    fun h => (Bool.or_eq_false_iff.1 h).1
  iintro %Φ ⟨#Hpkg, Hrn, #Hr, Hmin, #Hmsg, #Hsnap, Hcred, Hlc⟩ HΦ
  iNamed Hrn
  ihave #Hr' := rawNodeOwn_raft rn rnv $$ Hrn
  icombine Hr Hr' gives %Heq
  subst Heq
  icases ownStepGhost_boot_term γ _ cf id s (m.Type' = MsgPreVote) Hpvb $$ Hghost
    with ⟨%Hb1, Hghost⟩
  icases ownStepGhost_nsLink γ _ cf id s $$ Hghost with ⟨%Hnl, Hghost⟩
  have HnP : m.Type' ≠ MsgProp := by not_net
  icases ownRaftPhysC_preFacts cf rnv.raft' id s (Hpvoff.guard rs.capplied rs.cfg) $$ Hphys with ⟨%Hpf, Hphys⟩
  -- (D22 S-d3b) the log and what the storage will hold, before the step (`ackInv`'s carry)
  icases ownRaftPhysC_persistRel cf rnv.raft' id s $$ Hphys with ⟨%Hpr, Hphys⟩
  icases ownRaftPhysC_gh cf rnv.raft' id s $$ Hphys with ⟨%Hgh0, Hphys⟩
  have Hrel := fun h => Hpr.2 (ack_snap_sip Hloan Hgh0.1.2 h)
  -- (2026-10-28, stage U4a) `delivered`'s terms are the log's, for a restore's record
  icases ownRaftPhysC_applying cf rnv.raft' id s $$ Hphys with ⟨%Hac0, Hphys⟩
  icases ownStepGhost_dlv_terms γ _ cf id s rs.delivered
    (by have := uint_Z_nonneg s.logst.applying; rw [Hdlen]; omega) Hac0 $$ Hdeliv Hghost
    with ⟨%Hdag, Hghost⟩
  wp_apply Hok.raftStep Hpvoff Htrm Hmtc Htn Hb1 (Hrnfl.1 Hflw) (fun h => Hnl.2.1.trans (Hxt h)) (wp_raft_Step cf _ γ _ id s ml m ents ctx sn rsp)
      Hwf
    (RNMode.pre_net Hpf (by not_net)) (fun h => Hnl.1.trans (Hsnp h))
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
      · ipureintro; intro _; exact Hok.resps
      isplitr
      · ipureintro; not_net
      imodintro
      iintro %ty %Hty' %Hne
      iapply Hmsg $$ %ty %Hty' %Hne
    isplitl [Hcred]
    · iexact Hcred
    -- (D22 S-d4) a snapshot's facts, at the static mode
    imodintro
    iintro %h
    icases Hsnap $$ %h with ⟨%sv0, %scfg0, %Hp0, #Hm0, #Hd0, -⟩
    iexists sv0, scfg0
    iframe Hm0 Hd0
    ipureintro; exact Hp0
  simp only [HnP]
  iintro %err %s' %c' %md' ⟨Hphys, Hghost, %Hwf', %Href, %Hcc, -, %Hfr, %Htm, %Hresp, %Hsfr,
    %Htrc, -⟩
  have Hc := Href.commit_mono
  have Hmtc' : uint.Z m.Term' ≤ uint.Z s.gh.tc := by rw [← Hpvoff.2.1]; exact Hmtc
  have Htc0 := Hpvoff.2.2.1
  by_cases Hs : m.Type' = MsgSnap
  · -- (D22 S-d4) a snapshot, as `RawNode.Step`'s: the static mode, the restore's configuration;
    -- any queue, the acknowledgement's facts carried across the restore (`ackInv_snap`)
    obtain ⟨⟨Ha, Hu, Hsd, Hsg, Hpre, Hgh, Hfl', Hap', Ht1, Ht2, Hpcs⟩, Hsl⟩ := Hsfr Hs
    -- (2026-10-28, stage U0) at the configuration it started at (until then the restore's)
    have e2 := Hcc (fun h => by rw [Hs] at h; simp [MsgSnap, MsgStorageAppendResp] at h); subst c'
    icases Hsnap $$ %Hs with ⟨%sv0, %scfg0, %Hp0, #Hm0, -, #Hloc0⟩
    obtain ⟨Hsn0, Hcl0, -⟩ := Hp0
    have Hsl0 := Hsl sv0 Hsn0
    -- (2026-10-26, D22 J2) the pending snapshot kept, or the message's, local to the node
    ihave #Hsloc' : snapLocOk γ id s'.logst.snap $$ []
    · rcases Hsl0 with ⟨-, h2, -, -⟩ | ⟨-, -, h2, -, -, -⟩
      · rw [h2]; iexact Hsloc
      · rw [h2]; iapply (snapLocOk_some γ id (snapId sv0)).2
        rw [show (snapId sv0).index' = sv0.Metadata'.Index' from rfl]; iexact Hloc0
    -- (2026-10-28, stage U3c) in either mode: the ghost part at a new full prefix (a restore's)
    obtain ⟨fp', Hmd, Hfp'⟩ := RNMode.stepOut_snap Href Hs
    ihave Hghost : ownStepGhost γ (rs.mode.toG ⟨rs.capplied, rs.cfg, fp'⟩) cf id s' $$ [Hghost]
    · rw [← Hmd]; iexact Hghost
    have HnT : m.Type' ≠ MsgTimeoutNow := by rw [Hs]; simp [MsgSnap, MsgTimeoutNow]
    have Ht3' : m.Type' ≠ MsgPreVoteResp → uint.Z s'.term ≤ max (uint.Z s.term) (uint.Z m.Term') +
        (if m.Type' = MsgTimeoutNow then 1 else 0) := by
      intro _; rw [ite_eq_right HnT]; omega
    have Hle : uint.Z s'.term ≤ uint.Z s.gh.tc := by
      have := Int.max_le.2 ⟨Htc0, Hmtc'⟩; omega
    ihave #HG2 := isMessage_snap_leadFull γ m sv0 scfg0 $$ [Hm0]
    · iapply isMessageC_isMessage γ _ $$ Hm0
    ihave #Hstr' : ackInv γ
        { rs with term := s'.term, psnap := rs.psnap || decide (m.Type' = MsgSnap) } s' $$ []
    · iapply ackInv_snap γ rfl Hstok Ht1 Hsd Hsl0 Hrel Hpr.1 $$ Hstrecs HG2
    iapply HΦ $$ %err %s'.term
    isplitl
    · iapply ownRawNode_intro γ rn id
          { rs with term := s'.term, psnap := rs.psnap || decide (m.Type' = MsgSnap) } s' cf fp'
          rnv sv hprev steps Hwf' Hin Hal
          Hasync (by rw [Ha]; exact Hdlen) (by rw [Hu]; exact Hunp)
          (fun h => by have h1 := h.1; simp [Hs] at h1)
          (stepsOk_mono_st s s' _ Ht1 Hsd Hc Ha (tc_le_of_gh Hgh) Hstok) rfl
          (by rw [Hsg]; exact Hstor)
          ((Hpvoff.step rfl rfl Hpre Hgh Hle Hpcs (by not_net)).fp_pc Hfp')
          (by rw [Hgh]; exact Hrs_out) (by rw [Hgh]; exact Hrs_unst) (Int.le_trans Hrs_clb Hc)
          (RNFl.keep Hrnfl Hfl' (by rw [Hap']; exact Int.le_refl _) Ha)
          (Hloan.step s'.term Hgh (fun _ => ⟨by
              rcases Hsl0 with ⟨-, h2, -, -⟩ | ⟨-, -, h2, -, h3, -⟩
              · exact .inl h2
              · exact .inr ⟨_, h2, h3, by simp [Hs]⟩, Hfl', Hsd, Hu, Ha, Hc⟩))
          (Hsdt.snap Hdag Hsl0) $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hsteps_cap Hpend Hdeliv Hstr' Hloanc Hsloc'
    ipureintro
    rw [Htrm]
    exact ⟨Ht1, by rw [Hpvoff.2.1]; exact Hle, Ht3'⟩
  have e1 := Href.keep (by not_net) Hs (fun h => absurd h (by not_net)); subst e1
  have e2 := Hcc (fun h => absurd h (by not_net)); subst c'
  obtain ⟨Ha, Hsn, Hu, Hpv, Hsd, Hsg, Hpre, Hgh, Hfl', Hap'⟩ := Hfr Hs (by not_net) (fun h => absurd h (by not_net))
  obtain ⟨Ht1, -, Ht3, Hip4, Ht5, Hpcs⟩ := Htm Hs
  have Ht3' : m.Type' ≠ MsgPreVoteResp → uint.Z s'.term ≤ max (uint.Z s.term) (uint.Z m.Term') +
      (if m.Type' = MsgTimeoutNow then 1 else 0) := by
    intro hpr
    by_cases h : m.Type' = MsgTimeoutNow
    · rw [ite_eq_left h]; exact Ht5 h
    · rw [ite_eq_right h]; have := Ht3 (by not_net) hpr h; omega
  have Hle : uint.Z s'.term ≤ uint.Z s.gh.tc := by
    by_cases hpr : m.Type' = MsgPreVoteResp
    · rcases (Hresp.2 hpr).1 with h | ⟨hp, h⟩
      · have := Int.max_le.2 ⟨Htc0, Hmtc'⟩; omega
      · have := Hpvoff.2.2.2.1 hp; omega
    · have h1 := Ht3' hpr
      by_cases h : m.Type' = MsgTimeoutNow
      · rw [ite_eq_left h] at h1
        have := Htn h; rw [Hpvoff.2.1, Htrm] at this; omega
      · rw [ite_eq_right h] at h1
        have := Int.max_le.2 ⟨Htc0, Hmtc'⟩; omega
  have Hstok' : StepsOk s' rs.steps := stepsOk_mono_le s s' _ Ht1 ⟨Hpv, (logStoreRec_stored Hsd)⟩ Hc Ha (tc_le_of_gh Hgh) Hstok
  -- (D22 S-d3b) the acknowledgement's facts across the step: a `MsgApp`'s truncation, at an entry of
  -- its leader's log (`ackInv_app`), or `offsetInProgress` not moved back
  ihave #Hstr' : ackInv γ
      { rs with term := s'.term, psnap := rs.psnap || decide (m.Type' = MsgSnap) } s' $$ []
  · by_cases Happ : m.Type' = MsgApp
    · ihave #Hm' := Hmsg $$ %MsgType.app %(by rw [Happ]; exact mtypeOf_MsgApp) %(by decide)
      rw [isMessage_absMsg_ctx γ .app m ents ctx (And.intro (by decide) (by decide))]
      ihave #Hents := isMessage_app_leadFull γ m ents $$ Hm'
      iapply ackInv_app γ rfl Hstok Ht1 Hpv Hsn (logStoreRec_stored Hsd) (Htrc Happ) Hrel Hpr.1 $$ Hstrecs Hents
    · iapply ackInv_keep γ rfl Hstok Ht1 Hpv Hsn (logStoreRec_stored Hsd) (Hip4 Happ) $$ Hstrecs
  ihave #Hsloc' := snapLocOk_keep γ id (.inl Hsn) $$ Hsloc
  iapply HΦ $$ %err %s'.term
  isplitl
  · iapply ownRawNode_intro γ rn id
        { rs with term := s'.term, psnap := rs.psnap || decide (m.Type' = MsgSnap) } s' cf fp
        rnv sv hprev steps Hwf' Hin Hal
        Hasync (by rw [Ha]; exact Hdlen) (by rw [Hu]; exact Hunp)
        (fun h => by rw [Hsn]; exact Hsnap ⟨Hps' h.1, h.2⟩)
        Hstok' rfl (by rw [Hsg]; exact Hstor)
        (Hpvoff.step rfl rfl Hpre Hgh Hle Hpcs (by not_net))
        (by rw [Hgh]; exact Hrs_out) (by rw [Hgh]; exact Hrs_unst) (Int.le_trans Hrs_clb Hc)
        (RNFl.keep Hrnfl Hfl' Hap' Ha)
        (Hloan.step s'.term Hgh (fun _ => ⟨.inl Hsn, Hfl', (logStoreRec_stored Hsd), Hu, Ha, Hc⟩))
        (Hsdt.ofRec Hsn Hsd) $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hsteps_cap Hpend Hdeliv Hstr' Hloanc Hsloc'
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
    -- (2026-10-27) either way the entry's bytes decode as its type says
    have Hdec : ∀ o, (propDataIs (GF := GF) γ e o ⊢ ⌜CCDecodes e.Type' e.Data'⌝) := by
      intro o
      cases o with
      | some d =>
        iintro He
        iunfold propDataIs at He
        icases He with ⟨%Hd, -⟩
        ipureintro; exact Hd.2.2
      | none =>
        iintro He
        iunfold propDataIs at He
        icases He with %Hz
        ipureintro; exact Hz.2
    have Hone : ∀ o, (propDataIs (GF := GF) γ e o ⊢ ∃ c, ccEntOk e c) := by
      intro o
      iintro He
      icases (Hdec o) $$ He with %Hdec
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
    (Hty : st.msg.Type' = MsgProp) (Hfr : st.msg.From' = id)
    -- (2026-10-22, D38a) no responses (`raft.Step`'s `Hnors`)
    (Hrs : st.resps = []) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        ownRawNode γ rn id rs ∗ rn.[RawNode, go!"raft"] ↦□ r ∗
        msgIn ml (DFrac.own 1) st ∗
        isMessage γ (absMsg .propose st.msg st.ents) ∗
        -- (2026-10-19, D21 M6) its entries' tickets
        ([∗list] e ∈ st.ents, entTk γ e) ∗ £ 1 }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #ml))
    {{ (err : GoInterface), RET #err; ownRawNode γ rn id rs ∗ stepErr err }} := by
  rcases st with ⟨m, ents, sn, ctx, rsp⟩
  simp only at Hty Hfr Hrs ⊢
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
  icases ownRaftPhysC_preFacts cf rnv.raft' id s (Hpvoff.guard rs.capplied rs.cfg) $$ Hphys with ⟨%Hpf, Hphys⟩
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
      · ipureintro; intro _; exact Hrs
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
  iintro %err %s' %c' %md' ⟨Hphys, Hghost, %Hwf', %Href, %Hcc, %Hloc, %_, %Htm, %_, -, -, Herr⟩
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
  have e1 := Href.keep (by msg_ne') (by msg_ne') (fun h => absurd h (by msg_ne')); subst e1
  have e2 := Hcc (by msg_ne'); subst c'
  obtain ⟨Hfr', Hap, -⟩ := Hloc.1 (fun h => absurd h (by msg_ne')) (.inl Hty)
  have Hap' := Hap (fun Hc => by rw [Hty] at Hc; simp [MsgProp, MsgStorageApplyResp] at Hc)
  ihave #Hstr' := ackInv_keep (rs' := rs) γ rfl Hstok (by rw [Hfr'.1]; exact Int.le_refl _)
    Hfr'.2.2.2.2.1 Hfr'.2.2.2.1 (logStoreRec_stored Hfr'.2.2.2.2.2.1) Hfr'.2.1 $$ Hstrecs
  ihave #Hsloc' := snapLocOk_keep γ id (.inl Hfr'.2.2.2.1) $$ Hsloc
  iapply HΦ
  isplitl
  rotate_left
  · iexact Hstep
  iapply ownRawNode_intro γ rn id rs s' cf fp rnv sv hprev steps Hwf' Hin Hal Hasync
    (by rw [Hap']; exact Hdlen) (by rw [Hfr'.2.2.1]; exact Hunp)
    (by rw [Hfr'.2.2.2.1]; exact Hsnap)
    (stepsOk_mono s s' _ Hfr'.1 ⟨Hfr'.2.2.2.2.1, (logStoreRec_stored Hfr'.2.2.2.2.2.1)⟩ Hc Hap'
      (tc_le_of_gh Hfr'.2.2.2.2.2.2.2.2.1) Hstok)
    (by rw [Hfr'.1]; exact Htrm) (by rw [Hfr'.2.2.2.2.2.2.1]; exact Hstor)
    (Hpvoff.keep rfl rfl Hfr'.2.2.2.2.2.2.2.1 Hfr'.2.2.2.2.2.2.2.2.1 Hfr'.1 Hfr'.2.2.2.2.2.2.2.2.2.1
      Hfr'.2.2.2.1 (PreGuardF.step (Htm (by msg_ne'))))
    (by rw [Hfr'.2.2.2.2.2.2.2.2.1]; exact Hrs_out) (by rw [Hfr'.2.2.2.2.2.2.2.2.1]; exact Hrs_unst)
    (Int.le_trans Hrs_clb Hc)
    (RNFl.keep Hrnfl Hfr'.2.2.2.2.2.2.2.2.2.2.1 Hfr'.2.2.2.2.2.2.2.2.2.2.2 Hap')
    (Hloan.keep Hfr'.2.2.2.2.2.2.2.2.1 Hfr'.2.2.2.1 Hfr'.2.2.2.2.2.2.2.2.2.2.1 (logStoreRec_stored Hfr'.2.2.2.2.2.1)
      Hfr'.2.2.1 Hap' Hc)
    (Hsdt.ofRec Hfr'.2.2.2.1 Hfr'.2.2.2.2.2.1) $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hsteps_cap Hpend Hdeliv Hstr' Hloanc Hsloc'

end step

/-! ## `r.applyConfChange`, on the node (2026-10-13) -/

section applycc
variable [GooseExts] [GooseSemantics] [GooseInterp]
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
`StepDownOnRemoval`) or (2026-10-25, T-M M2c) without it takes `reMatch` only and stays leader.
`applyCCOkC_step`'s `StepR` version: `StepR` has the step-down. -/
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
    · -- removed or demoted: `reMatch`, then the step-down with `StepDownOnRemoval`; (2026-10-25,
      -- T-M M2c) without it, `reMatch` only: the node stays leader
      rw [ite_eq_right Hv] at Hsw
      by_cases Hsd : ({ s with progress := prs, prvals := pvs, isLearner := learnerOfC c' id } :
        NState).sdr = true
      rotate_left
      · rw [if_neg Hsd] at Hsw
        subst Hsw
        generalize Hs1 : ({ s with progress := prs, prvals := pvs, isLearner := learnerOfC c' id } :
          NState) = s1 at H1 ⊢
        have HR1 := H1.toR (Adm := Adm) (dec := dec) (B := B) (rOf s g) rfl hc Hz
        have Hfr1 : RFrame s s1 := by
          refine ⟨?_, ?_, fun _ => ⟨Hl, ?_⟩⟩ <;> (rw [← Hs1]; try rfl)
        rw [← rOf_frame _ _ g Hfr1] at HR1
        exact HR1
      rw [if_pos Hsd] at Hsw
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
      (s'.role = .preCandidate → s.role = .preCandidate) ∧
      -- (2026-10-28, stage U3c) a follower stays one (`SnapFol`)
      (s.role = .follower → s'.role = .follower) := by
  rcases applyCCOkC_step (B := 0) c' id s s' H with ⟨-, Hr, Hsf, Htk, Ht, Hpv, Hg, Hl, Hc⟩ | ⟨Hl, Hv, Hsd, -⟩
  · exact ⟨⟨by rw [Hsf, Hr]; exact Hwf.1, by rw [Htk]; exact Hwf.2⟩, Ht, Hpv, Hg, Hl, Hc,
      fun h => by rw [← Hr]; exact h, fun h => by rw [Hr]; exact h⟩
  · obtain ⟨prs, pvs, -, -, Hsw⟩ := H
    unfold SwitchOkC at Hsw
    rw [ite_eq_left (show ({ s with progress := prs, prvals := pvs, isLearner := learnerOfC c' id } :
        NState).role = .leader from Hl), ite_eq_right Hv,
      if_pos (show ({ s with progress := prs, prvals := pvs, isLearner := learnerOfC c' id } :
        NState).sdr = true from Hsd)] at Hsw
    obtain ⟨pvs', rfl⟩ := Hsw
    refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
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
    (cc : Loc) (ccm : ConfChangeV2M) (dq : DFrac)
    -- (2026-10-28, stage U3d) of a committed log `D` within the commit index: the committed log
    -- handed out (while a snapshot `Ready` is lent, the loan's)
    (D : List EntryM)
    (Hpre : DynCCPreOp dec D rs.capplied rs.cfg (ccm.transition, ccm.changes) k e cs')
    (s : NState) (cf : CfgM) (fp : List EntryM) (rnv : RawNode) (sv : SoftState)
    (hprev : HardStateM) (steps : List Loc)
    (Hwf : NStateWf s) (Hin : rs.mode = .static → id ∈ γ.reCfg) (Hasync : rnv.asyncStorageWrites' = false)
    (Hdlen : rs.delivered.length = (uint.Z s.logst.applying).toNat)
    (Hunp : rs.unpersisted = s.logst.unpersisted)
    (Hsnap : rs.psnap = false ∧ rs.slent = none → s.logst.snap = none)
    (Hstok : StepsOk s rs.steps)
    (Htrm : rs.term = s.term) (Hstor : rs.storage = s.logst.storage)
    (Hpvoff : RNPv rs fp s) (Hrs_out : rs.outlb = s.gh.outlb)
    (Hrs_unst : rs.unst = s.gh.unst) (Hrs_clb : uint.Z rs.clb ≤ uint.Z s.logst.committed)
    (Hrnfl : RNFl rs s) (Hloan : LoanOk rs s) (Hsdt : SdtTie rs s)
    (HDc : (D.length : Int) ≤ uint.Z s.logst.committed) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        rawNodeOwn rn rnv ∗ ownRaftPhysCV cf cf.voters rnv.raft' id s ∗
        ownStepGhost γ (rs.mode.toG ⟨rs.capplied, rs.cfg, fp⟩) cf id s ∗
        sdrOk rnv.raft' rs.mode ∗ rnv.prevSoftSt' ↦□ sv ∗ prevHS γ rnv.prevHardSt' hprev rs.phs ∗
        rnv.stepsOnAdvance' ↦* steps ∗
        ownSliceCap Loc rnv.stepsOnAdvance' (DFrac.own 1) ∗
        lentPend rs.slent (pendList γ id steps rs.steps) ∗
        isCommitted γ rs.delivered ∗ ackInv γ rs s ∗
        loanCom γ rs.slent ∗ snapLocOk γ id s.logst.snap ∗ ownConfChangeV2 cc dq ccm ∗ £ 1 ∗
        isCommitted γ D }}
      (App (Val (rnv.raft' @!! go.GoType.PointerType raft.ty @!! go!"applyConfChange")) (Val #cc))
    {{ (cs : Loc) (xs os ls lns : List w64), RET #cs;
        ownRawNode γ rn id { rs with cfg := cs', capplied := k + 1 } ∗
        ownConfChangeV2 cc dq ccm ∗
        csPts cs (DFrac.own 1) (ConfStateM.mk xs ls os lns cs'.cfg.autoLeave) true ∗
        ⌜xs ≡ₚ elements cs'.cfg.incoming ∧ os ≡ₚ elements cs'.cfg.outgoing ∧
          ls ≡ₚ elements cs'.cfg.learners ∧ lns ≡ₚ elements cs'.cfg.learnersNext⌝ }} := by
  obtain ⟨Hk1, Hk2, Hke, Hconf, Hnoc, ⟨op', Hdec, Hstep'⟩, Hstep, Hal'⟩ := Hpre
  iintro %Φ ⟨#Hpkg, Hrn, Hphys, Hghost, #Hsdrf, #Hsoft, #Hhard, Hsteps, Hcap, Hpend, #Hdeliv,
    #Hstrecs, #Hloanc, #Hsloc, Hch, Hlc, #HDd⟩ HΦ
  let g : RGh := ⟨rs.capplied, rs.cfg, fp⟩
  ihave Hghost : ownStepGhost γ (.dyn dec c0 h0 g) cf id s $$ [Hghost]
  · rw [show (GMode.dyn dec c0 h0 g) = rs.mode.toG ⟨rs.capplied, rs.cfg, fp⟩ by rw [hm]; rfl]
    iexact Hghost
  icases ownRaftPhysC_logwf cf rnv.raft' id s $$ Hphys with ⟨%Hlw, Hphys⟩
  icases ownStepGhost_deliv γ dec c0 h0 g cf id s D HDc $$ HDd Hghost
    with ⟨%Hdp, Hghost⟩
  icases ownStepGhost_ns_last γ _ cf id s $$ Hghost with ⟨%Hli2, Hghost⟩
  icases (ownStepGhost_dyn γ dec c0 h0 g cf id s).1 $$ Hghost with ⟨%HDc, Hgr, #Hcl⟩
  obtain ⟨HD, Hgc, Hnl⟩ := HDc
  iunfold ownRaftGhostR at Hgr
  icases Hgr with ⟨Hg, %HI, #Hfr, #Hcamp⟩
  icases (entails_wand (persistent_entails_left (wand_entails
    (ownRaftGhost_logRecs (GF := GF) γ id (rOf s g).p true)))) $$ Hg with ⟨Hg, %-, #Hlr⟩
  icases ownRaftPhysC_preFacts cf rnv.raft' id s (Hpvoff.guard rs.capplied rs.cfg) $$ Hphys with ⟨%Hpf, Hphys⟩
  -- the entry, in the node's full log
  have Hfull_k : (rOf s g).full[k]? = some e := by
    obtain ⟨t, ht⟩ := Hdp
    rw [← ht, List.getElem?_append_left Hk2]; exact Hke
  have Htake : (rOf s g).full.take k = D.take k := by
    obtain ⟨t, ht⟩ := Hdp
    rw [← ht, List.take_append_of_le_length (Nat.le_of_lt Hk2)]
  have Hkc : k < uint.nat s.logst.committed := by
    have := uint_nat_eq s.logst.committed; omega
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
  -- (2026-10-25, T-M M2b) no pre-candidate either: its campaign guard has no conf entry past
  -- `applied` (`PreGuardF`; until then pre-vote was off in the dynamic mode)
  have Hnpc : s.role ≠ .preCandidate := by
    intro hp
    have Hg : PreGuardF fp s := by have := Hpf.1; rw [hm] at this; exact this
    obtain ⟨-, Hn⟩ := Hg HI.full.1 hp
    have Hac := HI.applied_cidx
    exact Hn k e (Nat.le_trans Hac Hk1) Hkc Hfull_k Hconf
  imod rdCred_zero_upd (GF := GF) γ with Hcr0
  iapply wp_fupd
  wp_apply +noauto wp_raft_applyConfChange cf rnv.raft' id s cc ccm dq cs'
      (by rw [Hcfg]; exact Happ) (by have := Hsz; omega)
      (fun h => by
        rcases h with h | h
        · exact absurd h Hnc
        · exact absurd h Hnpc) Hli2
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
    exact Hstep'
  have HR1 : StepR (AdmS dec c0 (fun l => l = (rOf s g).full.take (k + 1))) dec id 0 (rOf s g) []
      (rOf s g') :=
    StepR.applyConf (rOf s g) k e op' cs' Hk1 Hkc Hfull_k Hconf
      Hnoc'.noUndec (by rw [Htake]; exact Hdec) Hstep' Hadm
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
    iframe Hg Hfr
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
    isplitr
    · ipureintro; exact ⟨HD, rfl, by unfold NsLink; rw [Hok.gh]; exact Hnl⟩
    rw [show s'.logst.storage = s.logst.storage by rw [(applyCCOkC_frame Hok Hwf).2.2.2.2.1]]
    iexact Hcl
  ihave Hghost : ownStepGhost γ (({ rs with cfg := cs', capplied := k + 1 } : RNState).mode.toG
      ⟨({ rs with cfg := cs', capplied := k + 1 } : RNState).capplied,
       ({ rs with cfg := cs', capplied := k + 1 } : RNState).cfg, fp⟩) cs'.cfg id s' $$ [Hghost]
  · rw [show (({ rs with cfg := cs', capplied := k + 1 } : RNState).mode.toG
        ⟨({ rs with cfg := cs', capplied := k + 1 } : RNState).capplied,
         ({ rs with cfg := cs', capplied := k + 1 } : RNState).cfg, fp⟩) = GMode.dyn dec c0 h0 g' by
      simp only; rw [hm]; rfl]
    iexact Hghost
  obtain ⟨Hwf', Ht', Hpv', Hgh', Hls', Hc', Hrl', Hfol'⟩ := applyCCOkC_frame Hok Hwf
  ihave #Hstr' := ackInv_keep (rs' := rs) γ rfl Hstok (by rw [Ht']; exact Int.le_refl _)
    (by rw [Hls']) (by rw [Hls']) (by rw [Hls']) (by rw [Hls']; exact Int.le_refl _) $$ Hstrecs
  ihave #Hsloc' := snapLocOk_keep γ id (o := s.logst.snap) (o' := s'.logst.snap) (.inl (by rw [Hls']))
    $$ Hsloc
  imodintro
  iapply HΦ $$ %cs %xs %os %ls %lns
  iframe Hch Hcs
  isplitl
  · iapply ownRawNode_intro γ rn id { rs with cfg := cs', capplied := k + 1 } s' cs'.cfg fp rnv sv
      hprev steps Hwf' (fun h => by simp only at h; rw [hm] at h; cases h) Hal' Hasync
      (by rw [Hls']; exact Hdlen) (by rw [Hls']; exact Hunp) (by rw [Hls']; exact Hsnap)
      (stepsOk_mono s s' _ Ht' ⟨by rw [Hls'], by rw [Hls']⟩ Hc' (by rw [Hls']) (tc_le_of_gh Hgh') Hstok)
      (by rw [Ht']; exact Htrm) (by rw [Hls']; exact Hstor)
      ⟨fun _ _ hp => absurd (Hrl' hp) Hnpc, by rw [Hgh']; exact Hpvoff.2.1,
        by rw [Hgh', Ht']; exact Hpvoff.2.2.1, fun h => by rw [Hgh', Ht']; exact Hpvoff.2.2.2.1 (Hrl' h),
        fun h => Hfol' (Hpvoff.2.2.2.2 (by rw [Hls'] at h; exact h))⟩
      (by rw [Hgh']; exact Hrs_out) (by rw [Hgh']; exact Hrs_unst) (Int.le_trans Hrs_clb Hc')
      (by unfold RNFl; rw [Hls']; exact Hrnfl)
      (Hloan.keep Hgh' (by rw [Hls']) (by rw [Hls']) (by rw [Hls']) (by rw [Hls']) (by rw [Hls']) Hc')
      (by unfold SdtTie; rw [Hls']; exact Hsdt) $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hcap Hpend Hdeliv Hstr' Hloanc Hsloc'
  ipureintro; exact Hcs0

/-! ### The static mode -/

/-- (D19p, 2026-10-18) A shrinking change keeps the tracker within the tracked bound: the new
progress map tracks the voters and some of the old learners. -/
theorem trackedOk_shrink {γ : RaftNames} {id : w64} {s s' : NState} {lrn' : GSet w64}
    (H : TrackedOk γ (CfgM.simple γ.reCfg (domSet s.progress \ γ.reCfg)) id)
    (Hlp : ∀ k, k ∈ lrn' → k ∈ domSet s.progress) (Hd : lrn' = domSet s'.progress \ γ.reCfg) :
    TrackedOk γ (CfgM.simple γ.reCfg (domSet s'.progress \ γ.reCfg)) id := by
  refine TrackedOk.simple_mono (fun k hk => ?_) H
  rw [← Hd] at hk
  by_cases hc : k ∈ γ.reCfg
  · exact Or.inl hc
  · exact Or.inr ((GMap.elem_of_difference _ _ _).2 ⟨Hlp k hk, hc⟩)

/-- After `applyConfChange`: the ghost step its result is (`applyCCOkC_step`,
`ownRaftGhost_step_0`), and `ownRawNode` re-sealed at the same client-facing state. -/
theorem rawNode_applyCC_reseal (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState)
    (s s' : NState) (ps : PState) (rnv : RawNode) (sv : SoftState) (hprev : HardStateM)
    (steps : List Loc) (Hm : rs.mode = .static)
    (Hrel : NStateRel s ps) (Hin : id ∈ γ.reCfg) (Hasync : rnv.asyncStorageWrites' = false)
    (Hdlen : rs.delivered.length = (uint.Z s.logst.applying).toNat)
    (Hunp : rs.unpersisted = s.logst.unpersisted)
    (Hsnap : rs.psnap = false ∧ rs.slent = none → s.logst.snap = none)
    (Hstok : StepsOk s rs.steps) (Htrm : rs.term = s.term) (Hstor : rs.storage = s.logst.storage)
    {fp : List EntryM} (Hpvoff : RNPv rs fp s) (Hrs_out : rs.outlb = s.gh.outlb)
    (Hrs_unst : rs.unst = s.gh.unst) (Hrs_clb : uint.Z rs.clb ≤ uint.Z s.logst.committed)
    (Hrnfl : RNFl rs s) (Hloan : LoanOk rs s) (Hsdt : SdtTie rs s)
    (Hok : ApplyCCOkC (CfgM.simple γ.reCfg (domSet s'.progress \ γ.reCfg)) id s s')
    -- (D19p, 2026-10-18) the new tracker within the tracked bound
    (Htrk' : TrackedOk γ (CfgM.simple γ.reCfg (domSet s'.progress \ γ.reCfg)) id)
    (Hnl : NsLink γ s) :
    ⊢ rawNodeOwn rn rnv -∗ ownRaftPhys γ.reCfg rnv.raft' id s' -∗ ownRaftGhost (GF := GF) γ id ps -∗
      sdrOk rnv.raft' rs.mode -∗
      rnv.prevSoftSt' ↦□ sv -∗ prevHS γ rnv.prevHardSt' hprev rs.phs -∗ rnv.stepsOnAdvance' ↦* steps -∗
      ownSliceCap Loc rnv.stepsOnAdvance' (DFrac.own 1) -∗
      lentPend rs.slent (pendList γ id steps rs.steps) -∗
      isCommitted γ rs.delivered -∗
      ackInv γ rs s -∗
      loanCom γ rs.slent -∗
      -- (D22 S-b′3) the storage's certificate link
      certLink γ s.logst.storage -∗
      -- (2026-10-26, D22 J2) the pending snapshot's receiver-local fact
      snapLocOk γ id s.logst.snap -∗ £ 1 ={⊤}=∗
      ownRawNode γ rn id rs := by
  obtain ⟨Hst, Hro, Hsf, Htk, Htm, Hpv, Hgh, Hls, Hc⟩ :=
    (applyCCOkC_step (B := 0) _ _ _ _ Hok).resolve_right
      (fun ⟨_, Hv, _⟩ => Hv (by rw [CfgM.voters_simple]; exact Hin))
  have Hprev : s'.logst.prev = s.logst.prev := by rw [Hls]
  have Hstored : s'.logst.stored = s.logst.stored := by rw [Hls]
  have Happ : s'.logst.applying = s.logst.applying := by rw [Hls]
  have Hunp' : s'.logst.unpersisted = s.logst.unpersisted := by rw [Hls]
  have Hsnap' : s'.logst.snap = s.logst.snap := by rw [Hls]
  have Hstor' : s'.logst.storage = s.logst.storage := by rw [Hls]
  have Hwf' : NStateWf s' := by
    obtain ⟨-, H1, H2⟩ := Hrel
    exact ⟨by rw [Hsf, Hro]; exact H1, by rw [Htk]; exact H2⟩
  iintro Hrn Hphys Hghost #Hsdrf #Hsoft #Hhard Hsteps Hcap Hpend #Hdeliv #Hstrecs #Hloanc #Hcl #Hsloc Hlc
  ihave #Hsloc' := snapLocOk_keep γ id (.inl Hsnap') $$ Hsloc
  ihave #Hcl' : certLink (GF := GF) γ s'.logst.storage $$ []
  · rw [Hstor']; iexact Hcl
  rw [← Hrel.1] at *
  imod (preceipt_zero_bound (GF := GF) γ.reBoot.length) with #Hrc0
  ihave %Hst0 := ownRaftGhost_static γ id _ $$ Hghost
  imod ownRaftGhost_step_0 γ _ (CfgStatic.simple γ _ Hst0) id Htrk' 0 (by decide) _ _ Hst
    $$ Hrc0 Hlc Hghost with Hghost
  ihave #Hstr' := ackInv_keep (rs' := rs) γ rfl Hstok (by rw [Htm]; exact Int.le_refl _)
    Hprev Hsnap' Hstored (by rw [Hls]; exact Int.le_refl _) $$ Hstrecs
  iapply ownRawNode_intro_static γ rn id rs s' (toPState s') rnv sv hprev steps Hm ⟨rfl, Hwf'⟩ Hin Hasync
    (by rw [Happ]; exact Hdlen) (by rw [Hunp']; exact Hunp) (by rw [Hsnap']; exact Hsnap)
    (stepsOk_mono_le s s' _ (by rw [Htm]; exact Int.le_refl _) ⟨Hprev, Hstored⟩ Hc Happ (tc_le_of_gh Hgh) Hstok)
    (by rw [Htm]; exact Htrm) (by rw [Hstor']; exact Hstor) (Hpvoff.keepS rfl rfl Hpv Hgh Htm Hro Hsnap' Hm)
    (by rw [Hgh]; exact Hrs_out) (by rw [Hgh]; exact Hrs_unst) (Int.le_trans Hrs_clb Hc)
    (by unfold RNFl; rw [Hls]; exact Hrnfl)
    (Hloan.keep Hgh (by rw [Hls]) (by rw [Hls]) (by rw [Hls]) (by rw [Hls]) (by rw [Hls]) Hc)
    (by unfold SdtTie; rw [Hls]; exact Hsdt)
    Htrk' (by unfold NsLink; rw [Hgh]; exact Hnl)
    $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hcap Hpend Hdeliv Hstr' Hloanc Hcl' Hsloc'

/-- `r.applyConfChange(cc)` on the node's raft struct, for a change that leaves the
configuration unchanged (`node.run`'s `confc` arm); the ghost step inside. -/
theorem wp_rn_raft_applyConfChange
    (wp_raft_applyConfChange : raft.applyConfChange.spec (GF := GF) (hG := hG))
    (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (r : Loc) (cc : Loc) (ccm : ConfChangeV2M)
    (Hst : γ.reDyn = none)
    (Hn : CCShrink γ.reCfg ccm.transition ccm.changes) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        ownRawNode γ rn id rs ∗ rn.[RawNode, go!"raft"] ↦□ r ∗ ownConfChangeV2 cc DFrac.discard ccm ∗
        £ 1 }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"applyConfChange")) (Val #cc))
    {{ (cs : Loc) (xs ls : List w64), RET #cs;
        ownRawNode γ rn id rs ∗ ownConfChangeV2 cc DFrac.discard ccm ∗
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
    ⟨Hphys, Hghost, %Htrk, %Hnl, #Hcl⟩
  have Hrel : NStateRel s (toPState s) := ⟨rfl, Hwf⟩
  have Hin := Hin Hm
  iapply wp_fupd
  icases ownRaftPhys_progress_dom γ.reCfg rnv.raft' id s $$ Hphys with ⟨%Hsub, Hphys⟩
  icases ownRaftPhys_progress_size γ.reCfg rnv.raft' id s $$ Hphys with ⟨%Hsz, Hphys⟩
  obtain ⟨lrn', Hd', Hsz', Hn', Hlp⟩ := applyCC_of_shrink γ.reCfg s.progress _ _ Hn Hsub Hsz
  icases ownRaftGhost_ns_last γ id s Hnl $$ Hghost with ⟨%Hli2, Hghost⟩
  wp_apply +noauto (raft.applyConfChange.spec_simple wp_raft_applyConfChange) γ.reCfg rnv.raft' id
      s cc ccm DFrac.discard lrn' Hd' Hsz' Hn' Hli2 Hin
    $$ [$Hphys $Hccs] as %cs %xs %ls %s' ⟨Hphys, Hccs, Hcs, %Hcs0, %Hok, %Hdom'⟩
  imod rawNode_applyCC_reseal γ rn id rs s s' _ rnv sv hprev steps Hm Hrel Hin Hasync Hdlen Hunp
    Hsnap Hstok Htrm Hstor Hpvoff Hrs_out Hrs_unst Hrs_clb Hrnfl Hloan Hsdt (Hdom' ▸ Hok)
    (trackedOk_shrink Htrk Hlp Hdom') Hnl
    $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hsteps_cap Hpend Hdeliv Hstrecs Hloanc Hcl Hsloc Hlc with Hrn
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
    ⟨Hphys, Hghost, %Htrk, %Hnl, #Hcl⟩
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
    Hstok Htrm Hstor Hpvoff Hrs_out Hrs_unst Hrs_clb Hrnfl Hloan Hsdt Htrk Hnl
    $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hsteps_cap Hpend Hdeliv Hstrecs Hloanc Hcl Hsloc

/-- `r.applyConfChange(cc)` on the node's raft struct in the dynamic mode (2026-10-15, stage N;
`node.run`'s `confc` arm): `wp_applyConf_dyn` on `ownRawNode`, the changes read-only. -/
theorem wp_rn_raft_applyConfChange_dyn
    (wp_raft_applyConfChange : raft.applyConfChange.spec (GF := GF) (hG := hG))
    (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (r : Loc) (cc : Loc) (ccm : ConfChangeV2M)
    (dec : CCDec) (c0 : CCState) (h0 : CfgOk c0)
    (h1 : CCGood c0) (hm : rs.mode = .dyn dec c0 h0 h1) (k : Nat) (e : EntryM)
    (cs' : CCState)
    -- (2026-10-28, stage U3d) of the committed log handed out (while a snapshot `Ready` is lent,
    -- the loan's: `rsDlv`)
    (Hpre : DynCCPreOp dec (rsDlv rs) rs.capplied rs.cfg (ccm.transition, ccm.changes) k e cs') :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        ownRawNode γ rn id rs ∗ rn.[RawNode, go!"raft"] ↦□ r ∗ ownConfChangeV2 cc DFrac.discard ccm ∗
        £ 1 }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"applyConfChange")) (Val #cc))
    {{ (cs : Loc) (xs os ls lns : List w64), RET #cs;
        ownRawNode γ rn id { rs with cfg := cs', capplied := k + 1 } ∗
        ownConfChangeV2 cc DFrac.discard ccm ∗
        csPts cs (DFrac.own 1) (ConfStateM.mk xs ls os lns cs'.cfg.autoLeave) true ∗
        ⌜xs ≡ₚ elements cs'.cfg.incoming ∧ os ≡ₚ elements cs'.cfg.outgoing ∧
          ls ≡ₚ elements cs'.cfg.learners ∧ lns ≡ₚ elements cs'.cfg.learnersNext⌝ }} := by
  iintro %Φ ⟨#Hpkg, Hrn, #Hr, Hccs, Hlc⟩ HΦ
  iNamed Hrn
  ihave #Hr' := rawNodeOwn_raft rn rnv $$ Hrn
  icombine Hr Hr' gives %Heq
  subst Heq
  -- the committed log handed out, committed and within the commit index
  ihave #HDd : isCommitted γ (rsDlv rs) $$ []
  · unfold rsDlv
    cases hs : rs.slent with
    | none => iexact Hdeliv
    | some l => icases Hloanc with ⟨#H, -⟩; iexact H
  icases ownRaftPhysC_logwf cf rnv.raft' id s $$ Hphys with ⟨%Hlw, Hphys⟩
  have HDc : ((rsDlv rs).length : Int) ≤ uint.Z s.logst.committed := by
    unfold rsDlv
    cases hs : rs.slent with
    | none => rw [Hdlen]; have := uint_Z_nonneg s.logst.applying; omega
    | some l =>
      obtain ⟨-, -, Hi, -, -, -, -, Hdl, -⟩ := Hloan.2.2 l hs
      simp only; rw [Hdl]; have := uint_Z_nonneg l.snap.Metadata'.Index'; omega
  iapply wp_applyConf_dyn wp_raft_applyConfChange γ rn id rs dec c0 h0 h1 hm k e cs' cc ccm
      DFrac.discard (rsDlv rs) Hpre s cf fp rnv sv hprev steps Hwf Hin Hasync Hdlen Hunp Hsnap Hstok
      Htrm Hstor Hpvoff Hrs_out Hrs_unst Hrs_clb Hrnfl Hloan Hsdt HDc
    $$ [$Hpkg $Hrn $Hphys $Hghost $Hsdrf $Hsoft $Hhard $Hsteps $Hsteps_cap $Hpend $Hdeliv
      $Hstrecs $Hloanc $Hsloc $Hccs $Hlc $HDd]
  inext
  iintro %cs %xs %os %ls %lns ⟨Hrn, Hccs, Hcs, %Hcs⟩
  iapply HΦ $$ %cs %xs %os %ls %lns
  iframe Hrn Hccs Hcs
  ipureintro; exact Hcs

end applycc

/-! ## `run`'s states -/

section states
variable [GooseExts] [GooseSemantics] [GooseInterp]
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
    Hstok Htrm Hstor Hpvoff Hrs_out Hrs_unst Hrs_clb Hrnfl Hloan
    Hsdt $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hsteps_cap Hpend Hdeliv Hstrecs Hloanc Hsloc

/-- (D22 S-d4) A node with nothing queued has nothing lent (`LoanOk`: a loan's acknowledgement is
queued until `Advance`). -/
theorem ownRawNode_slent_nil (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState)
    (h : rs.steps = []) :
    ⊢ ownRawNode (GF := GF) γ rn id rs -∗ ⌜rs.slent = none⌝ ∗ ownRawNode γ rn id rs := by
  iintro H
  iNamed H
  isplitr
  · ipureintro; exact Hloan.none_of_nil h
  iapply ownRawNode_intro γ rn id rs s cf fp rnv sv hprev steps Hwf Hin Hal Hasync Hdlen Hunp Hsnap
    Hstok Htrm Hstor Hpvoff Hrs_out Hrs_unst Hrs_clb Hrnfl Hloan
    Hsdt $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hsteps_cap Hpend Hdeliv Hstrecs Hloanc Hsloc

/-- (D22 S-d4) The pure facts of a `Ready`'s snapshot as the application gets it (`LoanOut`). -/
theorem rdSnapOut_pure (γ : RaftNames) (rs : RNState) (rd : Ready) (ce es : List EntryM)
    (L : Option SnapLoan) :
    rdSnapOut (GF := GF) γ rs rd ce es L ⊢
      ⌜(L = none → rd.Snapshot' = null) ∧ (∀ l, L = some l → LoanOut rs rd ce es l)⌝ ∗
      rdSnapOut γ rs rd ce es L := by
  cases L with
  | none =>
    simp only [rdSnapOut]
    iintro %H
    isplitr
    · ipureintro; exact ⟨(fun _ => H), (fun _ h => by cases h)⟩
    ipureintro; exact H
  | some l =>
    simp only [rdSnapOut]
    iintro ⟨Hs, #Hc, %H⟩
    isplitr
    · ipureintro; exact ⟨(fun h => by cases h), (fun l' h => by cases h; exact H)⟩
    iframe Hs Hc
    ipureintro; exact H

/-- A `Ready` `run` computed and abandoned but keeps armed (`readyc` set): what
`ownRawNodeIdle_ready` needs of it, and, by the lower bounds of `rs`, that it holds no
messages (`SliceShape`, `k ≤ rs.outlb`) and no entries (`es ≠ [] → rs.unst`) once the
node is idle; and its read states with their facts (2026-10-13, persistent: from
`readyWithoutAccept`). (2026-10-16, stage R5: its hard state `hsOpt`, its entries `entsRO`,
its read states `readStatesPts`, no snapshot `nil`.) (D22 S-d4, 2026-10-21) A snapshot only with
`unst` raised (`ownRawNodeReady_abandon_keep`), so none once the node is idle. -/
def staleOk (γ : NodeNames) (rd : Ready) (rs : RNState) : IProp GF :=
  iprop(∃ (ce es : List EntryM) (k : Nat) (hrd : HardStateM),
    (⌜rd.SoftState' = null⌝ ∨ ∃ v : SoftState, rd.SoftState' ↦□ v) ∗
    hsOpt rd.HardState' hrd ∗
    -- (D22 S-b) its witness, as `readyWithoutAccept` computed it
    hsWit γ.raft (phsNext rs.phs hrd) (rs.delivered ++ ce).length ∗
    entsRO rd.CommittedEntries' ce ∗ ownSliceCap Loc rd.CommittedEntries' (DFrac.own 1) ∗
    isCommitted γ.raft (rs.delivered ++ ce) ∗ entsRO rd.Entries' es ∗
    (∃ sts : List ReadStateM, readStatesPts rd.ReadStates' sts ∗
      [∗list] st ∈ sts, readStateRaw γ.raft st) ∗
    ⌜(rd.Snapshot' ≠ null → rs.unst = true) ∧
      (es ≠ [] → rs.unst = true) ∧ SliceShape rd.Messages' k ∧ k ≤ rs.outlb ∧
      (∀ e, ce.getLast? = some e → uint.Z e.Index' ≤ uint.Z rs.clb ∧
        uint.Z e.Index' = (rs.delivered.length : Int) + (ce.length : Int))⌝)

/-- A `Ready` `readyWithoutAccept` just computed: its outputs. (2026-10-16, stage R5: the
messages handed out (D8), owned at `readyDq`, with `rd.Messages`' slice and capacity; the
entries `entsRO`; the read states `readStatesPts`; the hard state `hsOpt`.) (D22 S-d4,
2026-10-21) And its snapshot, if any (the loan `L`, `rdSnapOut`; until then `rd.Snapshot'`
`nil`), none without a restore since the last `Ready`. -/
def freshOk (γ : NodeNames) (rd : Ready) (rs : RNState) (ce es : List EntryM)
    (ms : List QMsg) (L : Option SnapLoan) : IProp GF :=
  iprop(entsRO rd.CommittedEntries' ce ∗ isCommitted γ.raft (rs.delivered ++ ce) ∗
    entsRO rd.Entries' es ∗ rd.Messages' ↦* ms.map QMsg.loc ∗
    ownSliceCap Loc rd.Messages' (DFrac.own 1) ∗
    ([∗list] q ∈ ms, msgOwn q.loc (readyDq q.st) q.st) ∗
    ([∗list] q ∈ ms, isRaftMsg γ.raft γ.id q.st) ∗
    (∃ sts : List ReadStateM, readStatesPts rd.ReadStates' sts ∗
      [∗list] st ∈ sts, readStateRaw γ.raft st) ∗
    -- (D22 S-b) with its witness (`hsWit`)
    (∃ hrd : HardStateM, hsOpt rd.HardState' hrd ∗ hsWit γ.raft (phsNext rs.phs hrd) (rs.delivered ++ ce).length) ∗
    rdSnapOut γ.raft rs rd ce es L ∗
    ⌜(∀ q ∈ ms, uint.Z q.st.msg.Term' ≤ uint.Z rs.tc) ∧ (rs.psnap = false → L = none)⌝)

/-- Both halves of `rof`: no `Ready` handed out. -/
def rofFull (γ : NodeNames) : IProp GF :=
  iprop(∃ x : List EntryM × List EntryM × List EntryM × HardStateM × Option SnapLoan,
    dghostVar γ.rof (DFrac.own (1 : Qp).half) x ∗ dghostVar γ.rof (DFrac.own (1 : Qp).half) x)

/-- `run`'s state besides the node, at the loop's head (`ac`: `advancec`, `rc`: `readyc`,
`rd`: `rd`): no `Ready` handed out (`ac` nil; then `rc` is nil or a stale `Ready` is
armed), or one handed out and its `Advance` awaited (`ac` is `n.advancec`). (D22 S-d4) With none
handed out none is lent; `run`'s record of the one handed out names its loan (`rs.slent`). -/
def headRest (γ : NodeNames) (nv : node) (rs : RNState) (ac rc : GoChan) (rd : Ready) :
    IProp GF :=
  iprop(termLB γ.bud rs.tc ∗ ⌜rs.storage = γ.stor⌝ ∗ runCfg γ rs ∗
    ((⌜ac = chan.nil ∧ rs.steps = [] ∧ rs.unpersisted = [] ∧ rs.slent = none⌝ ∗
        dghostVar γ.dlv (DFrac.own (1 : Qp).half) (rs.delivered, rs.phs) ∗ rofFull γ ∗
        (⌜rc = chan.nil⌝ ∨ (⌜rc = nv.readyc'⌝ ∗ staleOk γ rd rs)))
     ∨ (⌜ac = nv.advancec' ∧ rc = chan.nil ∧ rs.unst = false⌝ ∗
        ∃ d ce : List EntryM, ⌜rs.delivered = d ++ ce⌝ ∗
          dghostVar γ.rof (DFrac.own (1 : Qp).half) (d, ce, rs.unpersisted, rs.phs, rs.slent))))

/-- `run`'s loop invariant, but for its local variables. -/
def runHead (γ : NodeNames) (id : w64) (nv : node) (ac rc : GoChan) (rd : Ready) : IProp GF :=
  iprop(∃ rs : RNState, ownRawNode γ.raft nv.rn' id rs ∗ headRest γ nv rs ac rc rd)

/-- `run`'s state after its first statement (`HasReady`, `readyWithoutAccept`): the node
may also be at a fresh `Ready` (`ownRawNodeReady`) or idle with a stale one armed. (D22 S-d4) A
fresh one with its snapshot, if any (`L`). -/
def runMid (γ : NodeNames) (id : w64) (nv : node) (ac rc : GoChan) (rd : Ready) : IProp GF :=
  iprop((⌜ac = nv.advancec'⌝ ∗ runHead γ id nv ac rc rd) ∨
    (⌜ac = chan.nil⌝ ∗ ∃ rs : RNState, termLB γ.bud rs.tc ∗
      ⌜rs.storage = γ.stor ∧ rs.steps = [] ∧ rs.unpersisted = [] ∧ rs.slent = none⌝ ∗
      dghostVar γ.dlv (DFrac.own (1 : Qp).half) (rs.delivered, rs.phs) ∗ rofFull γ ∗ runCfg γ rs ∗
      ((⌜rc = chan.nil⌝ ∗ ownRawNode γ.raft nv.rn' id rs) ∨
       (⌜rc = nv.readyc'⌝ ∗ ∃ (ce es : List EntryM) (ms : List QMsg) (L : Option SnapLoan),
          ownRawNodeReady γ.raft nv.rn' id rs rd ce es ms false L ∗ freshOk γ rd rs ce es ms L) ∨
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
  · ipureintro; exact Hm0.2.2.1
  iframe Hlb H
  isplitr
  · ipureintro; exact Hst
  iunfold runCfg
  iframe Hcfg
  ipureintro; exact Hm0

/-- (D22 S-d4) A node that takes snapshots is outside the no-snapshot mode (`runCfg`; until
2026-10-28, stage U3d, also in the static mode): what `run`'s `MsgSnap` step needs. -/
theorem headRest_snapIn (γ : NodeNames) (nv : node) (rs : RNState) (ac rc : GoChan) (rd : Ready) :
    ⊢ headRest (GF := GF) γ nv rs ac rc rd -∗
      ⌜γ.snapIn = true → γ.raft.reNoSnap = false⌝ ∗ ⌜rs.mode = γ.mode⌝ ∗
      headRest γ nv rs ac rc rd := by
  iintro H
  unfold headRest
  icases H with ⟨#Hlb, %Hst, Hcfg, H⟩
  iunfold runCfg at Hcfg
  icases Hcfg with ⟨%Hm0, Hcfg⟩
  isplitr
  · ipureintro; exact Hm0.2.2.2.2.1
  isplitr
  · ipureintro; exact Hm0.1
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

/-- (D22 S-d4) A network step: the term, the term ceiling, and after a `MsgSnap` (`b`, only at a
node that takes snapshots) a snapshot may be pending. -/
theorem headRest_step (γ : NodeNames) (nv : node) (rs : RNState) (ac rc : GoChan) (rd : Ready)
    (t tc : w64) (b : Bool) (Hb : b = true → γ.snapIn = true) :
    ⊢ headRest (GF := GF) γ nv rs ac rc rd -∗ termLB γ.bud tc -∗
      headRest γ nv { { rs with tc := tc } with term := t, psnap := rs.psnap || b } ac rc rd := by
  iintro H #Hlb
  unfold headRest
  icases H with ⟨-, %Hst, Hcfg, H⟩
  iframe Hlb
  isplitr
  · ipureintro; exact Hst
  isplitl [Hcfg]
  · iunfold runCfg at Hcfg
    icases Hcfg with ⟨%Hm0, Hdlm, Hcfg⟩
    iunfold runCfg
    isplitr
    · ipureintro
      obtain ⟨H1, H2, H3, H4, H5, H6⟩ := Hm0
      refine ⟨H1, H2, H3, fun h => ?_, H5, H6⟩
      have hb : b = false := by
        cases hb : b
        · rfl
        · rw [Hb hb] at h; cases h
      simp only [hb, Bool.or_false]
      exact H4 h
    isplitl [Hdlm]
    · iExactEq Hdlm; rfl
    iExactEq Hcfg; rfl
  iExactEq H
  rfl

/-- With no `Ready` handed out (`ac` nil). -/
theorem headRest_nil (γ : NodeNames) (nv : node) (rs : RNState) (rc : GoChan) (rd : Ready)
    (Hnn : nv.advancec' ≠ chan.nil) :
    ⊢ headRest (GF := GF) γ nv rs chan.nil rc rd -∗
      termLB γ.bud rs.tc ∗
      ⌜rs.storage = γ.stor ∧ rs.steps = [] ∧ rs.unpersisted = [] ∧ rs.slent = none⌝ ∗
      dghostVar γ.dlv (DFrac.own (1 : Qp).half) (rs.delivered, rs.phs) ∗ rofFull γ ∗ runCfg γ rs ∗
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
  obtain ⟨Hst, Hsteps, Hunp, Hsl⟩ := Hrs
  unfold runHead
  icases H with (⟨%Hrc, Hrn⟩ | ⟨%Hrc, %ce, %es, %ms, %L, Hrn, Hf⟩ | ⟨%Hrc, Hrn, Hstale⟩)
  · iexists rs
    iframe Hrn
    unfold headRest
    iframe Hlb Hcfg
    isplitr
    · ipureintro; exact Hst
    ileft
    iframe Hdlv Hrof
    isplitr
    · ipureintro; exact ⟨Hac, Hsteps, Hunp, Hsl⟩
    ileft; ipureintro; exact Hrc
  · unfold freshOk
    icases Hf with ⟨#Hce, #Hcommitted, #Hents, Hmsgs, Hmsgs_cap, Hown, #Hmsgs_ok, #Hrsts,
      ⟨%hrd0, #Hrdh0, #Hhsw⟩, Hsnz, %Hfacts⟩
    -- (D22 S-d4) no snapshot unless one is handed out (`rdSnapOut`)
    ihave %Hsz : ⌜L = none → rd.Snapshot' = null⌝ $$ [Hsnz]
    · cases L with
      | none => iunfold rdSnapOut at Hsnz; icases Hsnz with %H; ipureintro; intro _; exact H
      | some l => ipureintro; intro h; cases h
    ihave %Hshape := ownSlice_shape _ _ _ $$ Hmsgs
    icases ownRawNodeReady_abandon_keep γ.raft nv.rn' id rs rd ce es ms L Hsteps Hunp
      $$ Hmsgs Hmsgs_cap Hown Hrn with ⟨Hce_cap, #Hrdsoft, -, %n, %u, %c, %Hnuc, Hrn⟩
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
    · ipureintro; exact ⟨Hac, Hsteps, Hunp, Hsl⟩
    iright
    isplitr
    · ipureintro; exact Hrc
    unfold staleOk
    iexists ce, es, ms.length, hrd0
    iframe Hrdsoft Hrdh0 Hhsw Hce Hce_cap Hcommitted Hents Hrsts
    ipureintro
    refine ⟨fun h => Hnuc.2.2.1 ?_, Hnuc.2.1, by simpa using Hshape, Hnuc.1, Hnuc.2.2.2⟩
    cases L with
    | none => exact absurd (Hsz rfl) h
    | some _ => rfl
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
    · ipureintro; exact ⟨Hac, Hsteps, Hunp, Hsl⟩
    iright
    isplitr
    · ipureintro; exact Hrc
    iexact Hstale

/-- A `Ready`'s messages are of terms within the budget: at most the node's. (2026-10-16,
stage R5: with the messages' ownership, as `readyData` holds them.) -/
theorem readyMsgs_termLB (γ : NodeNames) (t : w64) (ms : List QMsg)
    (H : ∀ q ∈ ms, uint.Z q.st.msg.Term' ≤ uint.Z t) :
    ⊢ ([∗list] q ∈ ms, msgOwn (GF := GF) q.loc (readyDq q.st) q.st) -∗
      ([∗list] q ∈ ms, isRaftMsg (GF := GF) γ.raft γ.id q.st) -∗ termLB γ.bud t -∗
      [∗list] q ∈ ms, msgOwn q.loc (readyDq q.st) q.st ∗ isRaftMsg γ.raft γ.id q.st ∗
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
        ⌜rs.storage = γ.stor ∧ rs.steps = [] ∧ rs.unpersisted = [] ∧ rs.slent = none⌝ ∗
        dghostVar γ.dlv (DFrac.own (1 : Qp).half) (rs.delivered, rs.phs) ∗ rofFull γ ∗ runCfg γ rs ∗
        ((∃ (ce es : List EntryM) (ms : List QMsg) (L : Option SnapLoan),
            ownRawNodeReady γ.raft nv.rn' id rs rd ce es ms false L ∗ freshOk γ rd rs ce es ms L) ∨
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

/-- `advancec` armed: a `Ready` handed out. (D22 S-d4) `run`'s record names its loan. -/
theorem runMid_busy (γ : NodeNames) (id : w64) (nv : node) (rc : GoChan) (rd : Ready)
    (Hnn : nv.advancec' ≠ chan.nil) :
    ⊢ runMid (GF := GF) γ id nv nv.advancec' rc rd -∗
      ∃ (rs : RNState) (d ce : List EntryM), ownRawNode γ.raft nv.rn' id rs ∗
        termLB γ.bud rs.tc ∗ runCfg γ rs ∗
        ⌜rs.storage = γ.stor ∧ rc = chan.nil ∧ rs.unst = false ∧ rs.delivered = d ++ ce⌝ ∗
        dghostVar γ.rof (DFrac.own (1 : Qp).half) (d, ce, rs.unpersisted, rs.phs, rs.slent) := by
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
  icases H with (⟨%Hrc, Hrn⟩ | ⟨%Hrc, %ce, %es, %ms, %L, Hrn, Hf⟩ | ⟨%Hrc, Hrn, Hstale⟩)
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
  · ihave Hlf := ownRawNodeReady_lead γ.raft nv.rn' id rs rd ce es ms false r L $$ Hrn Hr
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
    iexists ce, es, ms, L
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

omit [GooseInterp] [GooseSemantics] go_gctx in
/-- A conf change's premises on the driver's view (a prefix `D` of the committed log handed
out, the configuration index `ca` of the last applied conf change) carry over to `run`'s
`RawNode`, whose committed log `D'` extends `D` and whose configuration index `ca'` is past `ca`
over no conf entry: the conf entry at `k` cannot be below `ca'`. -/
theorem dynCCPreOp_transfer {dec : CCDec} {D D' : List EntryM} {ca ca' : Nat}
    {cfg : CCState} {op : CCOp} {k : Nat} {e : EntryM} {cs' : CCState}
    (Hp : DynCCPreOp dec D ca cfg op k e cs') (Hpre : D <+: D') (Hca : ca ≤ ca')
    (Hnc : NoConfIn D' ca ca') : DynCCPreOp dec D' ca' cfg op k e cs' := by
  obtain ⟨Hk1, Hk2, Hke, Hconf, Hnoc, ⟨op', Hdec, Hstep'⟩, Hstep, Hal⟩ := Hp
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
    exact ⟨op', Hdec, Hstep'⟩

omit [GooseInterp] [GooseSemantics] go_gctx in
/-- `NoConfIn` over two adjacent ranges. -/
theorem NoConfIn_trans {D : List EntryM} {a b c : Nat} (H1 : NoConfIn D a b)
    (H2 : NoConfIn D b c) : NoConfIn D a c := by
  intro k e hk1 hk2 he
  by_cases h : k < b
  · exact H1 k e hk1 h he
  · exact H2 k e (by omega) hk2 he

omit [GooseInterp] [GooseSemantics] go_gctx in
/-- `NoConfIn` over a smaller range. -/
theorem NoConfIn_mono {D : List EntryM} {a b a' b' : Nat} (H : NoConfIn D a b)
    (ha : a ≤ a') (hb : b' ≤ b) : NoConfIn D a' b' := by
  intro k e hk1 hk2 he
  exact H k e (by omega) (by omega) he

omit [GooseInterp] [GooseSemantics] go_gctx in
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
the shared configuration moves to the entry applied, `(k + 1, cs')`. (2026-10-28, stage U3d) Over
the committed log handed out (`rsDlv`: while a snapshot `Ready` is lent, the loan's; until then no
snapshot was lent in the dynamic mode). -/
theorem runCfg_confc (γ : NodeNames) (rs : RNState) (ds : List EntryM) (ca : Nat)
    (cfg : CCState) (op : CCOp) (k : Nat) (e : EntryM) (cs' : CCState) (dec : CCDec)
    (Hdy : γ.mode.isDyn = true)
    (Hp : DynCCPreOp dec ds ca cfg op k e cs') :
    ⊢ runCfg (GF := GF) γ rs -∗ monoListLbOwn γ.dlm ds -∗
      dghostVar γ.cap (DFrac.own (1 : Qp).half) (ca, cfg) -∗
      ⌜DynCCPreOp dec (rsDlv rs) rs.capplied rs.cfg op k e cs'⌝ ∗
      |==> (runCfg γ { rs with cfg := cs', capplied := k + 1 } ∗
        dghostVar γ.cap (DFrac.own (1 : Qp).half) (k + 1, cs') ∗ monoNatLbOwn γ.cam (k + 1)) := by
  iintro Hcfg #Hlb Hcap
  iunfold runCfg at Hcfg
  icases Hcfg with ⟨%Hm0, Hdlm, %ca_r, Hcap_r, Hcam, %Hinv⟩
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
  isplitr
  · ipureintro
    exact ⟨Hm0.1, by show k + 1 ≤ (rsDlv rs).length; omega, Hm0.2.2.1, Hm0.2.2.2.1, Hm0.2.2.2.2.1, Hm0.2.2.2.2.2⟩
  isplitl [Hdlm]
  · iExactEq Hdlm; rfl
  iexists k + 1
  iframe Hcap_r Hcam
  ipureintro
  exact ⟨Nat.le_refl _, NoConfIn_empty _ _⟩

/-- The `readyc` arm: the committed log handed out grows by the `Ready`'s committed entries
(the configuration and its index unchanged); a lower bound of it for the driver. (D22 S-d4,
2026-10-21) With a snapshot (`L`, recorded as the node's loan, `RNState.slent`): to the committed
log up to it (`dlvAfter`), which extends `delivered`; none without a restore since the last
`Ready`, so none at a node that takes no snapshots. -/
theorem runCfg_extend (γ : NodeNames) (rs rs' : RNState) (ce : List EntryM) (L : Option SnapLoan)
    (Hsl0 : rs.slent = none)
    (Hd : rs'.delivered = rs.delivered ++ ce) (Hm : rs'.mode = rs.mode) (Hc : rs'.cfg = rs.cfg)
    (Hca : rs'.capplied = rs.capplied) (Hfw : rs'.flw = rs.flw)
    (Hps : rs'.psnap = false) (Hsl : rs'.slent = L)
    (HL : ∀ l, L = some l → ce = [] ∧ rs.delivered <+: l.dlv)
    (HpL : rs.psnap = false → L = none) :
    ⊢ runCfg (GF := GF) γ rs ==∗
      runCfg γ rs' ∗ monoListLbOwn γ.dlm (dlvAfter rs.delivered ce L) := by
  iintro Hcfg
  iunfold runCfg at Hcfg
  icases Hcfg with ⟨%Hm0, Hdlm, %ca_r, Hcap_r, Hcam, %Hinv⟩
  obtain ⟨Hmd, Hcp, Hflw, Hsn, Hsi, -⟩ := Hm0
  rw [rsDlv_none Hsl0]
  rw [rsDlv_none Hsl0] at Hcp Hinv
  have Hext : rs.delivered <+: dlvAfter rs.delivered ce L := by
    cases L with
    | none => exact List.prefix_append _ _
    | some l => exact (HL l rfl).2
  imod monoListAuthOwn_update (dlvAfter rs.delivered ce L) Hext $$ Hdlm with ⟨Hdlm, #Hlb⟩
  imodintro
  iframe Hlb
  have Hrs' : rsDlv rs' = dlvAfter rs.delivered ce L := by
    unfold rsDlv
    rw [Hsl]
    cases L with
    | none => exact Hd
    | some l => rfl
  iunfold runCfg
  rw [Hrs', Hd, Hm, Hc, Hca, Hps, Hsl]
  iframe Hdlm
  isplitr
  · ipureintro
    refine ⟨Hmd, ?_, by rw [Hfw]; exact Hflw, fun h => ⟨rfl, HpL (Hsn h).1⟩, Hsi, ?_⟩
    · exact Nat.le_trans Hcp Hext.length_le
    · intro l hl
      obtain ⟨rfl, Hp⟩ := HL l hl
      simpa using Hp
  iexists ca_r
  iframe Hcap_r Hcam
  ipureintro
  exact ⟨Hinv.1, NoConfIn_prefix Hext Hcp Hinv.2⟩

/-- (D22 S-d4) What `runCfg` says of snapshots: none pending or lent at a node that takes none,
and one that takes them is outside the no-snapshot mode (until 2026-10-28, stage U3d, also in the
static mode). (Until D22 S-d4
`runCfg_psnap`/`runCfg_slent`: none at all.) -/
theorem runCfg_snap (γ : NodeNames) (rs : RNState) :
    ⊢ runCfg (GF := GF) γ rs -∗
      ⌜(γ.snapIn = false → rs.psnap = false ∧ rs.slent = none) ∧
        (γ.snapIn = true → γ.raft.reNoSnap = false) ∧ rs.mode = γ.mode⌝ ∗
      runCfg γ rs := by
  iintro Hcfg
  iunfold runCfg at Hcfg
  icases Hcfg with ⟨%Hm0, Hdlm, Hrest⟩
  isplitr
  · ipureintro; exact ⟨Hm0.2.2.2.1, Hm0.2.2.2.2.1, Hm0.1⟩
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

/-- (2026-10-28, stage U3d) The `advancec` arm, before `Advance`, from `run`'s side after the
rendezvous (`runCfgR`): A1 at the `RawNode` (`runCfg_a1`, or the loan's `runCfgLoan`), and,
dynamically after a snapshot `Ready`, its `ConfState` no auto-leave one. -/
theorem runCfgR_a1 (γ : NodeNames) (rs : RNState) (ca_d : Nat) :
    ⊢ runCfgR (GF := GF) γ rs -∗ monoNatLbOwn γ.cam ca_d -∗
      ⌜γ.mode.isDyn = true → NoConfIn rs.delivered ca_d rs.delivered.length⌝ -∗
      ⌜rs.mode.isDyn = true → NoConfIn rs.delivered rs.capplied rs.delivered.length⌝ ∗
      ⌜∀ l, rs.slent = some l → rs.mode.isDyn = true →
        l.snap.Metadata'.ConfState'.AutoLeave' = false⌝ ∗
      runCfgR γ rs := by
  iintro Hcfg #Hlb %HA
  by_cases hc : rs.slent = none ∨ rs.mode.isDyn = false
  · ihave Hcfg := (runCfgR_of_runCfg (GF := GF) γ rs hc).1 $$ Hcfg
    icases runCfg_a1 γ { rs with flw := false } ca_d $$ Hcfg Hlb [] with ⟨%HA1, Hcfg⟩
    · ipureintro; exact HA
    ihave Hcfg := (runCfgR_of_runCfg (GF := GF) γ rs hc).2 $$ Hcfg
    isplitr
    · ipureintro; exact HA1
    isplitr
    · ipureintro
      intro l hl hd
      rcases hc with h | h
      · rw [h] at hl; cases hl
      · rw [h] at hd; cases hd
    iexact Hcfg
  · have hl : ∃ l, rs.slent = some l := by
      cases h : rs.slent with
      | none => exact absurd (.inl h) hc
      | some l => exact ⟨l, rfl⟩
    obtain ⟨l, hl⟩ := hl
    have hd : rs.mode.isDyn = true := by
      cases h : rs.mode.isDyn
      · exact absurd (.inr h) hc
      · rfl
    ihave Hcfg := (runCfgR_loan (GF := GF) γ rs l hl hd).1 $$ Hcfg
    iunfold runCfgLoan at Hcfg
    icases Hcfg with ⟨%Hm, Hrest⟩
    isplitr
    · ipureintro; intro _; exact Hm.2.2.2.2.1
    isplitr
    · ipureintro; intro l' hl' _; rw [hl] at hl'; cases hl'; exact Hm.2.2.2.2.2
    iapply (runCfgR_loan (GF := GF) γ rs l hl hd).2
    iunfold runCfgLoan
    iframe Hrest
    ipureintro; exact Hm

/-- The `advancec` arm, after `Advance`: the configuration index moved up to at most the
committed log handed out, over no conf entry (A1), not at all in the static mode. (D22 S-d4,
2026-10-21) After a snapshot `Ready` the loan is returned and the committed log handed out is the
loan's (`advRS`), which the authority is already over (`rsDlv`); (2026-10-28, stage U3d)
dynamically the configuration the snapshot's, which the rendezvous already shared
(`runCfgLoan`). -/
theorem runCfg_advance (γ : NodeNames) (rs : RNState) (t : w64) (ca : Nat)
    (Hca : (rs.slent = none → rs.capplied ≤ ca ∧ ca ≤ max rs.capplied rs.delivered.length) ∧
      (∀ l, rs.slent = some l → rs.mode.isDyn = true → ca = l.dlv.length) ∧
      (rs.mode = .static → ca = rs.capplied))
    (HA1 : rs.mode.isDyn = true → NoConfIn rs.delivered rs.capplied rs.delivered.length) :
    ⊢ runCfgR (GF := GF) γ rs -∗ runCfg γ (advRS rs t ca) := by
  iintro Hcfg
  cases hsl : rs.slent with
  | none =>
    ihave Hcfg := (runCfgR_of_runCfg (GF := GF) γ rs (.inl hsl)).1 $$ Hcfg
    iunfold runCfg at Hcfg
    icases Hcfg with ⟨%Hm0, Hdlm, %ca_r, Hcap_r, Hcam, %Hinv⟩
    obtain ⟨Hmd, Hcp, -, Hsn, Hsi, Hpre⟩ := Hm0
    simp only [rsDlv, hsl] at Hmd Hcp Hsn Hsi Hpre Hinv
    rw [advRS_none t ca hsl]
    have Hcases : ca = rs.capplied ∨ (rs.mode.isDyn = true ∧ ca ≤ rs.delivered.length) := by
      cases hm : rs.mode with
      | static => exact .inl (Hca.2.2 hm)
      | dyn _ _ _ _ =>
        right; refine ⟨rfl, ?_⟩
        have := (Hca.1 hsl).2; omega
    iunfold runCfg
    isplitr
    · ipureintro
      refine ⟨Hmd, ?_, rfl, fun h => by simpa [hsl] using Hsn h, Hsi,
        fun l h => by simp [hsl] at h⟩
      simp only [rsDlv, hsl]
      rcases Hcases with h | ⟨-, h⟩
      · rw [h]; exact Hcp
      · exact h
    isplitl [Hdlm]
    · iExactEq Hdlm; simp only [rsDlv, hsl]
    iexists ca_r
    iframe Hcap_r Hcam
    ipureintro
    simp only [rsDlv, hsl]
    rcases Hcases with h | ⟨hd, h⟩
    · rw [h]; exact Hinv
    · refine ⟨by have := (Hca.1 hsl).1; omega, ?_⟩
      exact NoConfIn_trans Hinv.2 (NoConfIn_mono (HA1 hd) (Nat.le_refl _) h)
  | some l =>
    have Hadv : advRS rs t ca =
        { rs with
          steps := [], term := t, capplied := ca, flw := false,
          slent := none, unpersisted := [], delivered := l.dlv,
          cfg := rs.mode.foldCfg l.dlv rs.cfg } := by
      unfold advRS; rw [hsl]
    rw [Hadv]
    cases hd : rs.mode.isDyn with
    | false =>
      -- statically the index and the configuration do not move
      ihave Hcfg := (runCfgR_of_runCfg (GF := GF) γ rs (.inr hd)).1 $$ Hcfg
      iunfold runCfg at Hcfg
      icases Hcfg with ⟨%Hm0, Hdlm, %ca_r, Hcap_r, Hcam, %Hinv⟩
      obtain ⟨Hmd, Hcp, -, Hsn, Hsi, Hpre⟩ := Hm0
      simp only [rsDlv, hsl] at Hmd Hcp Hsn Hsi Hpre Hinv
      have Hst : rs.mode = .static := by
        cases hm : rs.mode with
        | static => rfl
        | dyn _ _ _ _ => rw [hm] at hd; cases hd
      have Hca0 : ca = rs.capplied := Hca.2.2 Hst
      rw [show rs.mode.foldCfg l.dlv rs.cfg = rs.cfg by rw [Hst]; rfl]
      iunfold runCfg
      isplitr
      · ipureintro
        have Hsin : γ.snapIn = true := by
          cases h : γ.snapIn
          · have := (Hsn h).2; simp at this
          · rfl
        refine ⟨Hmd, ?_, rfl, fun h => absurd (h.symm.trans Hsin) Bool.false_ne_true, Hsi,
          fun l' h => by simp at h⟩
        simp only [rsDlv]; rw [Hca0]; exact Hcp
      isplitl [Hdlm]
      · iExactEq Hdlm; simp only [rsDlv, hsl]
      iexists ca_r
      iframe Hcap_r Hcam
      ipureintro
      simp only [rsDlv]
      rw [Hca0]
      exact Hinv
    | true =>
      -- dynamically at the snapshot's index and configuration, which the rendezvous shared
      ihave Hcfg := (runCfgR_loan (GF := GF) γ rs l hsl hd).1 $$ Hcfg
      iunfold runCfgLoan at Hcfg
      icases Hcfg with ⟨%Hm, Hdlm, Hcap_r, Hcam⟩
      obtain ⟨Hmd, Hsin, Hns, -, -, -⟩ := Hm
      have Hca0 : ca = l.dlv.length := Hca.2.1 l hsl hd
      iunfold runCfg
      isplitr
      · ipureintro
        refine ⟨Hmd, ?_, rfl, fun h => absurd (h.symm.trans Hsin) Bool.false_ne_true,
          fun _ => Hns, fun l' h => by simp at h⟩
        simp only [rsDlv]; rw [Hca0]; exact Nat.le_refl _
      isplitl [Hdlm]
      · iExactEq Hdlm; simp only [rsDlv]
      iexists l.dlv.length
      iframe Hcap_r Hcam
      ipureintro
      simp only [rsDlv]
      rw [Hca0]
      exact ⟨Nat.le_refl _, NoConfIn_empty _ _⟩

end cfgshare

end EtcdGrove
end Perennial
