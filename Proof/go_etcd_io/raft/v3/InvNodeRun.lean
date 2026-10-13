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
-/
module

public import Proof.go_etcd_io.raft.v3.InvNode
public import Spec.go_etcd_io.raft.v3.raft__Step
public import Spec.go_etcd_io.raft.v3.raft__applyConfChange
-- `Step.commit_mono`
public import Proof.go_etcd_io.raft.v3.Protocol.Facts

@[expose] public section

set_option autoImplicit false

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
theorem ownRaftPhys_lead (cfg : GSet w64) (r : Loc) (id : w64) (s : NState) :
    ⊢ ownRaftPhys (GF := GF) cfg r id s -∗
      r.[raft, go!"lead"] ↦ s.lead ∗ r.[raft, go!"Term"] ↦ s.term ∗
      (r.[raft, go!"lead"] ↦ s.lead -∗ r.[raft, go!"Term"] ↦ s.term -∗
        ownRaftPhys cfg r id s) := by
  iintro H
  icases ownRaftPhys_view cfg r id s $$ H with ⟨%rss, %sl1, %sl2, %ms1, %ms2, Hv⟩
  iNamed Hv
  isplitl [Hf_lead]
  · iexact Hf_lead
  isplitl [Hf_Term]
  · iexact Hf_Term
  iintro Hl Ht
  ihave H := Hclose $$ %sl1 %sl2 %ms1 %ms2 %s.outbox %s.logst %s.gh %rss %s.rd Ht Hf_Vote
    Hf_readStates HreadStates HreadStates_cap %(And.intro rfl rfl) Hf_raftLog Hf_state Hl Hf_msgs Hmsgs Hmsgs_cap Hf_msgsAA HmsgsAA HmsgsAA_cap Houtbox
    %HmsgsAA_ok %Hout_term %Hgh_out %Hgh_unst Hlog
  iapply ownRaftPhys_eq cfg r id _ _ (by cases s; rfl) $$ H

/-- The raft struct out of the node (`r` is the node's raft pointer), and back. -/
theorem ownRawNode_borrow (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (r : Loc) :
    ⊢ ownRawNode (GF := GF) γ rn id rs -∗ rn.[RawNode, go!"raft"] ↦□ r -∗
      ∃ s : NState, ownRaftPhys γ.reCfg r id s ∗
        (ownRaftPhys γ.reCfg r id s -∗ ownRawNode γ rn id rs) := by
  iintro H #Hr
  iNamed H
  ihave #Hr' := rawNodeOwn_raft rn rnv $$ Hrn
  icombine Hr Hr' gives %Heq
  subst Heq
  iexists s
  isplitl [Hphys]
  · iexact Hphys
  iintro Hphys
  iapply ownRawNode_intro γ rn id rs s ps rnv sv steps Hrel Hin Hasync Hdlen Hunp Hsnap Hstok
    Htrm Hstor Hpvoff Hrs_out Hrs_unst Hrs_clb
    $$ Hrn Hphys Hghost Hsoft Hsteps Hsteps_cap Hpend Hpown Hdeliv Hstrecs

theorem ownRawNodeIdle_borrow (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (r : Loc) :
    ⊢ ownRawNodeIdle (GF := GF) γ rn id rs -∗ rn.[RawNode, go!"raft"] ↦□ r -∗
      ∃ s : NState, ownRaftPhys γ.reCfg r id s ∗
        (ownRaftPhys γ.reCfg r id s -∗ ownRawNodeIdle γ rn id rs) := by
  iintro H #Hr
  iNamed H
  ihave #Hr' := rawNodeOwn_raft rn rnv $$ Hrn
  icombine Hr Hr' gives %Heq
  subst Heq
  iexists s
  isplitl [Hphys]
  · iexact Hphys
  iintro Hphys
  iapply ownRawNodeIdle_intro γ rn id rs s ps rnv sv steps Hrel Hin Hasync Hdlen Hunp Hsnap
    Hstok Htrm Hstor Hpvoff Hrs_out Hrs_unst Hrs_clb Hidle
    $$ Hrn Hphys Hghost Hsoft Hsteps Hsteps_cap Hpend Hpown Hdeliv Hstrecs

/-- The fields of the raft struct `isNode` shares, out of a node. -/
theorem ownRawNode_shared (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) :
    ⊢ ownRawNode (GF := GF) γ rn id rs -∗
      ∃ (r : Loc) (lok : GoInterfaceOk), rn.[RawNode, go!"raft"] ↦□ r ∗
        r.[raft, go!"id"] ↦□ id ∗ r.[raft, go!"logger"] ↦□ (interface.ok lok : GoInterface) ∗
        isLogger lok ∗ ownRawNode γ rn id rs := by
  iintro H
  iNamed H
  ihave #Hr := rawNodeOwn_raft rn rnv $$ Hrn
  icases ownRaftPhys_shared γ.reCfg rnv.raft' id s $$ Hphys with
    ⟨%lok, #Hid, #Hlg, #Hlogger, Hphys⟩
  iexists rnv.raft', lok
  iframe Hr Hid Hlg Hlogger
  iapply ownRawNode_intro γ rn id rs s ps rnv sv steps Hrel Hin Hasync Hdlen Hunp Hsnap Hstok
    Htrm Hstor Hpvoff Hrs_out Hrs_unst Hrs_clb
    $$ Hrn Hphys Hghost Hsoft Hsteps Hsteps_cap Hpend Hpown Hdeliv Hstrecs

/-- The leader fields, for `run`'s check (any values: the check only logs and arms the
proposal channel). -/
def leadFields (r : Loc) (X : IProp GF) : IProp GF :=
  iprop(∃ (ld t : w64), r.[raft, go!"lead"] ↦ ld ∗ r.[raft, go!"Term"] ↦ t ∗
    (r.[raft, go!"lead"] ↦ ld -∗ r.[raft, go!"Term"] ↦ t -∗ X))

theorem ownRawNode_lead (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (r : Loc) :
    ⊢ ownRawNode (GF := GF) γ rn id rs -∗ rn.[RawNode, go!"raft"] ↦□ r -∗
      leadFields r (ownRawNode γ rn id rs) := by
  iintro H #Hr
  icases ownRawNode_borrow γ rn id rs r $$ H Hr with ⟨%s, Hphys, Hback⟩
  icases ownRaftPhys_lead γ.reCfg r id s $$ Hphys with ⟨Hl, Ht, Hclose⟩
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
  icases ownRawNodeIdle_borrow γ rn id rs r $$ H Hr with ⟨%s, Hphys, Hback⟩
  icases ownRaftPhys_lead γ.reCfg r id s $$ Hphys with ⟨Hl, Ht, Hclose⟩
  unfold leadFields
  iexists s.lead, s.term
  iframe Hl Ht
  iintro Hl Ht
  iapply Hback
  iapply Hclose $$ Hl Ht

theorem ownRawNodeReady_lead (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (rd : Ready)
    (ce es : List raftpb.Entry) (ms : List raftpb.Message) (h : Bool) (r : Loc) :
    ⊢ ownRawNodeReady (GF := GF) γ rn id rs rd ce es ms h -∗ rn.[RawNode, go!"raft"] ↦□ r -∗
      leadFields r (ownRawNodeReady γ rn id rs rd ce es ms h) := by
  iintro H #Hr
  iunfold ownRawNodeReady at H
  icases H with ⟨%s, %ps, %rnv, %sv, H⟩
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
  iexists s, ps, rnv, sv
  simp only [named]
  iframe Hrn Hghost Hout Hsoft Hsteps Hsteps_cap Hcommitted Hstrecs Hrdsoft Hrdrs Hce Hce_cap
  isplitl
  · iunfold ownRaftPhysReady
    iexists rsl, sl1, sl2, ms1, ms2
    simp only [named]
    iframe Hf_id Hf_Term Hf_Vote Hf_readStates HreadStates HreadStates_cap Hf_raftLog Hf_state
      Hf_lead Hf_msgs Hf_msgsAA HmsgsAA HmsgsAA_cap Houtbox Hlog Hundo Hclose
    ipureintro
    exact ⟨HmsgsAA_ok, Hout_term, Hgh_out, Hgh_unst, Hmslen⟩
  ipureintro
  exact ⟨Hrel, Hin, Hasync, Hdlen, Hunp, Hsnap, Htrm, Hstor, Hpvoff, Hrs_out, Hrs_unst, Hrs_clb,
    Hrdz, Hceok, Hes, Hrdc⟩

/-! ## Abandoning a `Ready`, keeping it armed -/

/-- `ownRawNodeReady_abandon`, also giving back what of the `Ready` `ownRawNodeIdle_ready`
takes should `run` send it after all: its committed entries' capacity and its soft
state. -/
theorem ownRawNodeReady_abandon_keep (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState)
    (rd : Ready) (ce es : List raftpb.Entry) (ms : List raftpb.Message)
    (Hsteps0 : rs.steps = []) (Hunp0 : rs.unpersisted = []) :
    ⊢ rd.Messages' ↦* ms -∗ ownSliceCap raftpb.Message rd.Messages' (DFrac.own 1) -∗
      ownRawNodeReady (GF := GF) γ rn id rs rd ce es ms -∗
      ownSliceCap raftpb.Entry rd.CommittedEntries' (DFrac.own 1) ∗
      (⌜rd.SoftState' = null⌝ ∨ ∃ v : SoftState, rd.SoftState' ↦□ v) ∗
      ∃ (n : Nat) (u : Bool) (c : w64),
        ⌜ms.length ≤ n ∧ (es ≠ [] → u = true) ∧
         (∀ e, ce.getLast? = some e → uint.Z e.Index' ≤ uint.Z c ∧
           uint.Z e.Index' = (rs.delivered.length : Int) + (ce.length : Int))⌝ ∗
        ownRawNode γ rn id { rs with outlb := n, unst := u, clb := c } := by
  iintro Hmsgs Hmsgs_cap H
  iunfold ownRawNodeReady at H
  icases H with ⟨%s, %ps, %rnv, %sv, H⟩
  iNamed H
  isplitl [Hce_cap]
  · iexact Hce_cap
  isplitr
  · iexact Hrdsoft
  iunfold ownRaftPhysReady at Hphys
  icases Hphys with ⟨%rsl, %sl1, %sl2, %ms1, %ms2, Hphys⟩
  iNamed Hphys
  icases Hundo $$ Hmsgs Hmsgs_cap with ⟨Hm1, Hc1⟩
  simp only [Bool.false_eq_true, ↓reduceIte]
  let g : NGhost := { outlb := ms1.length + ms2.length,
                      unst := decide (nextUnstable s.logst ≠ []) }
  ihave Hphys := Hclose $$ %sl1 %sl2 %ms1 %ms2 %s.outbox %s.logst %g %rsl %s.rd Hf_Term Hf_Vote
    Hf_readStates HreadStates HreadStates_cap %(And.intro rfl rfl) Hf_raftLog Hf_state Hf_lead Hf_msgs Hm1 Hc1 Hf_msgsAA HmsgsAA HmsgsAA_cap
    Houtbox %HmsgsAA_ok %Hout_term %(Nat.le_refl _)
    %(fun h => .inl (of_decide_eq_true h)) Hlog
  ihave #Hdeliv : isCommitted γ rs.delivered $$ []
  · iapply isCommitted_mono γ rs.delivered (rs.delivered ++ ce) (List.prefix_append _ _)
      $$ Hcommitted
  ihave Hpend : ([∗list] _k ↦ m;p ∈ ([] : List raftpb.Message);rs.steps,
      pendingRel γ id m p) $$ []
  · rw [Hsteps0]
    iapply (BigSepL2.bigSepL2_nil (Φ := fun _ m p => pendingRel (GF := GF) γ id m p)).2
    iempintro
  ihave Hpown : ([∗list] _k ↦ m;p ∈ ([] : List raftpb.Message);rs.steps,
      pendingOwn (GF := GF) m p) $$ []
  · rw [Hsteps0]
    iapply (BigSepL2.bigSepL2_nil (Φ := fun _ m p => pendingOwn (GF := GF) m p)).2
    iempintro
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
  iapply ownRawNode_intro γ rn id rs' s' ps rnv sv [] Hrel Hin Hasync Hdlen
    (Hunp0.trans Hunp.symm) Hsnap (by show StepsOk _ rs.steps; rw [Hsteps0]; trivial) Htrm
    Hstor Hpvoff rfl rfl
    (Int.le_refl _)
    $$ Hrn Hphys Hghost Hsoft Hsteps Hsteps_cap Hpend Hpown Hdeliv Hstrecs

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
local macro "not_net" : tactic => `(tactic| (intro h; first | exact h.elim |
  (rw [h] at Hty; simp [netStepTypes,
  MsgApp, MsgAppResp, MsgVote, MsgVoteResp, MsgHeartbeat, MsgHeartbeatResp, MsgHup,
  MsgPreVote, MsgPreVoteResp, MsgSnap, MsgBeat, MsgProp, MsgStorageAppendResp,
  MsgStorageApplyResp, MsgReadIndex, MsgReadIndexResp, MsgForgetLeader, MsgUnreachable, MsgSnapStatus, MsgTimeoutNow, MsgTransferLeader] at Hty)))

/-- A stamped type is not one of the unstamped ones. -/
local macro "ty_ne" : tactic => `(tactic| (simp [UnstampedType, MsgApp, MsgAppResp, MsgVote,
  MsgVoteResp, MsgHeartbeat, MsgHeartbeatResp, MsgReadIndex, MsgReadIndexResp,
  MsgForgetLeader, MsgUnreachable, MsgSnapStatus, MsgTimeoutNow, MsgTransferLeader]))

/-- `r.Step(m)` on a message from the network, `r` the node's raft struct: the tail of
`RawNode.Step` (its guards are `run`'s own code). -/
theorem wp_rn_raft_Step_net (wp_raft_Step : raft.Step.spec (GF := GF) (hG := hG))
    (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (r : Loc) (m : raftpb.Message)
    (ents : List raftpb.Entry) (ctx : List w8) (Hok : NetMsgOk id m)
    (Hsing : m.Type' = MsgReadIndex → 1 < GMap.size γ.reCfg)
    (Htn : m.Type' = MsgTimeoutNow → uint.Z rs.term + 1 < 2 ^ 64 ∧ uint.Z m.Term' + 1 < 2 ^ 64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        ownRawNode γ rn id rs ∗ rn.[RawNode, go!"raft"] ↦□ r ∗
        m.Entries' ↦*□ ents ∗ ownSliceCap raftpb.Entry m.Entries' (DFrac.own 1) ∗
        m.Context' ↦*□ ctx ∗
        □ (∀ ty, ⌜mtypeOf m.Type' = some ty⌝ -∗ isMessage γ (absMsg ty m ents ctx)) ∗
        rdCred γ (if m.Type' = MsgReadIndex then 1 else 0) }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #m))
    {{ (err : GoInterface) (t : w64), RET #err;
        ownRawNode γ rn id { rs with term := t } ∗
        ⌜uint.Z rs.term ≤ uint.Z t ∧ uint.Z t ≤ max (uint.Z rs.term) (uint.Z m.Term') +
          (if m.Type' = MsgTimeoutNow then 1 else 0)⌝ }} := by
  have Hok0 := Hok
  obtain ⟨Hty, Hnri, Hri, Hself, Hrej, -⟩ := Hok0
  have Hnr : ∀ {t : w32}, m.Type' = t → ¬ UnstampedType t →
      m.To' = id ∧ m.Term' ≠ W64 0 ∧ m.From' ≠ W64 0 :=
    fun h ht => Hnri (h ▸ ht)
  iintro %Φ ⟨#Hpkg, Hrn, #Hr, #Hents, Hents_cap, #Hctx, #Hmsg, Hcred⟩ HΦ
  iNamed Hrn
  ihave #Hr' := rawNodeOwn_raft rn rnv $$ Hrn
  icombine Hr Hr' gives %Heq
  subst Heq
  have HnP : m.Type' ≠ MsgProp := by not_net
  have Hsm : StepMsg m := netStepTypes_stepMsg Hty
  have Hrest : RestMsgOk s m := Hok.restMsgOk (by rw [← Htrm]; exact Htn)
  have P1 : m.Type' = MsgHup → m.Term' = W64 0 ∧ uint.Z s.term + 1 < 2 ^ 64 := by not_net
  have P2 : m.Type' = MsgPreVote → m.To' = id ∧ m.Term' ≠ W64 0 ∧ m.From' ≠ W64 0 ∧
      m.From' ≠ id ∧ (s.term = W64 0 → plogUpToDate s.logst.prev
        (s.logst.sents ++ s.logst.uents) (entryID.mk m.LogTerm' m.Index') = true) ∧
      s.prevote = true := by
    not_net
  have P3 : m.Type' = MsgPreVoteResp → m.To' = id ∧ m.Term' ≠ W64 0 ∧ m.From' ≠ W64 0 ∧
      (s.role = .preCandidate → uint.Z s.term + 1 < 2 ^ 64) := by not_net
  have P4 : m.Type' = MsgSnap → m.To' = id ∧ m.Term' ≠ W64 0 ∧ m.From' ≠ W64 0 ∧
      m.From' ≠ id := by not_net
  have P5 : m.Type' = MsgBeat → m.Term' = W64 0 := by not_net
  have P6 : m.Type' = MsgProp → m.Term' = W64 0 ∧ (m.From' = W64 0 ∨ m.From' = id) := by
    not_net
  have P7 : m.Type' = MsgStorageAppendResp → m.Snapshot' = null ∧
      uint.Z m.Term' ≤ uint.Z s.term ∧
      (m.Term' = W64 0 ∨ m.Term' = s.term → m.Index' ≠ W64 0 →
        StableOk s.logst (entryID.mk m.LogTerm' m.Index')) ∧ s.gh.unst = false := by
    not_net
  have P8 : m.Type' = MsgStorageApplyResp → m.Term' = W64 0 := by not_net
  wp_apply wp_raft_Step γ.reCfg γ _ id s ps m ents ctx rfl Hsm (fun _ => Hin) P1
    (fun h => Hnr h (by ty_ne))
    (fun h => ⟨(Hnr h (by ty_ne)).1, (Hnr h (by ty_ne)).2.1⟩) P2 P3
    (fun h => ⟨(Hnr h (by ty_ne)).1, (Hnr h (by ty_ne)).2.1, (Hnr h (by ty_ne)).2.2,
      Hself (.inl h)⟩)
    (fun h => ⟨(Hnr h (by ty_ne)).1, (Hnr h (by ty_ne)).2.1, (Hnr h (by ty_ne)).2.2,
      Hself (.inr (.inl h))⟩)
    (fun h => ⟨(Hnr h (by ty_ne)).1, (Hnr h (by ty_ne)).2.1, (Hnr h (by ty_ne)).2.2,
      Hrej h⟩)
    (fun h => ⟨(Hnr h (by ty_ne)).1, (Hnr h (by ty_ne)).2.1, (Hnr h (by ty_ne)).2.2,
      Hself (.inr (.inr (.inl h)))⟩)
    P4 P5 P6 P7 P8 (fun h => ⟨Hri (.inl h), Hsing h⟩)
    (fun h => ⟨(Hnr h (by ty_ne)).1, (Hnr h (by ty_ne)).2.1, (Hnr h (by ty_ne)).2.2,
      Hself (.inr (.inr (.inr h)))⟩) Hrest Hrel
    $$ [$Hphys $Hghost Hents_cap Hcred]
  · simp only [HnP, ↓reduceIte, named]
    isplitl [Hents_cap]
    · isplitr
      · iexact Hents
      isplitl [Hents_cap]
      · iexact Hents_cap
      isplitr
      · ipureintro; not_net
      isplitr
      · ipureintro; not_net
      imodintro
      iintro %ty %Hty' _
      iapply Hmsg $$ %ty %Hty'
    isplitr
    · iexact Hctx
    isplitl [Hcred]
    · iexact Hcred
    imodintro
    iintro %h
    exfalso
    revert h
    not_net
  simp only [HnP, ↓reduceIte]
  iintro %err %s' %ps' ⟨Hphys, Hghost, %Hrel', %Href, -, %Hfr, %Htm, -, -⟩
  obtain ⟨Ha, Hsn, Hu, Hpv, Hsd, Hsg, Hpre, Hgh⟩ := Hfr (by not_net) (by not_net)
  obtain ⟨Ht1, -, Ht3, -, Ht5⟩ := Htm (by not_net)
  have Ht3 : uint.Z s'.term ≤ max (uint.Z s.term) (uint.Z m.Term') +
      (if m.Type' = MsgTimeoutNow then 1 else 0) := by
    by_cases h : m.Type' = MsgTimeoutNow
    · rw [if_pos h]; exact Ht5 h
    · rw [if_neg h]; have := Ht3 (by not_net) (by not_net) h; omega
  have Hc : uint.Z s.logst.committed ≤ uint.Z s'.logst.committed := by
    obtain ⟨recv, Hst⟩ := Href
    have H := Step.commit_mono Hst
    rw [← Hrel.1, ← Hrel'.1] at H
    exact H
  have Hstok' : StepsOk s' rs.steps := stepsOk_mono_le s s' _ Ht1 ⟨Hpv, Hsd⟩ Hc Ha Hpre Hstok
  ihave #Hstr' := storedRecs_eq γ _ s'.logst.prev _ s'.logst.stored Hpv Hsd $$ Hstrecs
  iapply HΦ $$ %err %s'.term
  isplitl
  · iapply ownRawNode_intro γ rn id { rs with term := s'.term } s' ps' rnv sv steps Hrel' Hin
      Hasync (by rw [Ha]; exact Hdlen) (by rw [Hu]; exact Hunp) (by rw [Hsn]; exact Hsnap)
      Hstok' rfl (by rw [Hsg]; exact Hstor) (by rw [Hpre]; exact Hpvoff)
      (by rw [Hgh]; exact Hrs_out) (by rw [Hgh]; exact Hrs_unst) (Int.le_trans Hrs_clb Hc)
      $$ Hrn Hphys Hghost Hsoft Hsteps Hsteps_cap Hpend Hpown Hdeliv Hstr'
  ipureintro
  rw [Htrm]
  exact ⟨Ht1, Ht3⟩

/-- A premise of `Step` about another message type: `MsgProp` (`W32 2`) is not it. -/
local macro "msg_ne" : tactic => `(tactic| (intro Hc; simp [MsgHup, MsgVote, MsgVoteResp,
  MsgPreVote, MsgPreVoteResp, MsgApp, MsgHeartbeat, MsgAppResp, MsgHeartbeatResp, MsgSnap,
  MsgBeat, MsgStorageAppendResp, MsgStorageApplyResp, propMsg, MsgProp, MsgForgetLeader, MsgUnreachable, MsgSnapStatus, MsgTimeoutNow, MsgTransferLeader] at Hc))

set_option hygiene false in
/-- A premise of `Step` about another message type, for a message of type `MsgProp`
(`Hty'` in context). -/
local macro "msg_ne'" : tactic => `(tactic| (intro Hc; rw [Hty'] at Hc; simp [MsgHup, MsgVote,
  MsgVoteResp, MsgPreVote, MsgPreVoteResp, MsgApp, MsgHeartbeat, MsgAppResp, MsgHeartbeatResp,
  MsgSnap, MsgBeat, MsgStorageAppendResp, MsgStorageApplyResp, MsgProp, MsgReadIndex,
  MsgReadIndexResp, MsgForgetLeader, MsgUnreachable, MsgSnapStatus, MsgTimeoutNow, MsgTransferLeader] at Hc))

/-- A proposal's abstraction is legitimately sent, from the node's: `isMessage` of a
proposal reads only its term and entries, not its sender (2026-10-10). -/
theorem isMessage_propose_from (γ : RaftNames) (m : raftpb.Message) (ents : List raftpb.Entry)
    (x : w64) :
    ⊢ isMessage (GF := GF) γ (absMsg .propose m ents) -∗
      isMessage γ (absMsg .propose { m with From' := x } ents) := by
  iintro H
  unfold isMessage absMsg absMsgFrom at *
  iexact H

theorem isMessage_propose_pure (γ : RaftNames) (m : raftpb.Message) (ents : List raftpb.Entry) :
    ⊢ isMessage (GF := GF) γ (absMsg .propose m ents) -∗
      ⌜m.Term' = W64 0 ∧ ents ≠ [] ∧ (ents.length : Int) < 2 ^ 61⌝ := by
  unfold isMessage absMsg absMsgFrom
  iintro ⟨%H, -⟩
  ipureintro; exact H

/-- The proposal `Propose` builds is legitimately sent, given its entry's data. -/
theorem isMessage_propMsg (γ : RaftNames) (esl data_sl : GoSlice) :
    ⊢ entData (GF := GF) γ (propEntry data_sl) -∗
      isMessage γ (absMsg .propose (propMsg esl) [propEntry data_sl]) := by
  iintro #Hent
  unfold isMessage absMsg absMsgFrom
  isplitr
  · ipureintro
    exact ⟨rfl, List.cons_ne_nil _ _, by simp⟩
  iapply (BigSepL.bigSepL_singleton (Φ := fun _ e => entData (GF := GF) γ e)).2
  iexact Hent

/-- The proposed slices' invariant, out of a node (2026-10-13). -/
theorem isNode_propDataInv (γ : NodeNames) (id : w64) (n : Loc) :
    ⊢ isNode (GF := GF) γ id n -∗ inv propDataN (propDataInv γ.raft) := by
  iintro #H
  iunfold isNode at H
  iNamed H
  iexact Hpdinv

/-- A proposal's conf-change entries' bytes, from their data's records (2026-10-13): each
entry of a proposal has its data (`entData`), which for a conf-change entry is a proposed
slice whose bytes decode as its type says (`CCDecodes`); the proposed slices' invariant
gives the bytes (`propData_heap`). What `raft.Step` needs of a proposal (`ccEntsOk`). -/
theorem propData_ccEnts (γ : RaftNames) (ents : List raftpb.Entry) (E : CoPset)
    (HE : ↑propDataN ⊆ E) :
    ⊢ inv propDataN (propDataInv (GF := GF) γ) -∗ ([∗list] e ∈ ents, entData γ e) ={E}=∗
      ∃ cs, ccEntsOk ents cs := by
  induction ents with
  | nil =>
    iintro #Hinv #Hes
    imodintro
    iexists []
    unfold ccEntsOk
    iapply (BigSepL2.bigSepL2_nil (Φ := fun _ e o => ccEntOk (GF := GF) e o)).2
    iempintro
  | cons e es ih =>
    iintro #Hinv #Hes
    icases (BigSepL.bigSepL_cons (Φ := fun _ e => entData (GF := GF) γ e)).1 $$ Hes
      with ⟨#He, #Hes'⟩
    ihave Hih := ih $$ Hinv Hes'
    imod Hih with ⟨%cs, #Hcs⟩
    ihave Hone : iprop(|={E}=> ∃ c, ccEntOk e c) $$ []
    · iunfold entData at He
      icases He with ⟨%o, #He⟩
      cases o with
      | some d =>
        iunfold entDataIs at He
        icases He with ⟨%Hd, -⟩
        imodintro
        iexists none
        unfold ccEntOk
        ipureintro
        unfold IsConfEnt; rw [Hd.2]
        rintro (h | h) <;> revert h <;> word
      | none =>
        iunfold entDataIs at He
        icases He with (%Hz | ⟨%Hty, %bs, #Hpd, %Hdec⟩)
        · imodintro
          iexists none
          unfold ccEntOk
          ipureintro
          unfold IsConfEnt; rw [Hz.1]
          rintro (h | h) <;> revert h <;> word
        · imod propData_heap γ e.Data' bs E HE $$ Hinv Hpd with #Hbs
          imodintro
          by_cases H1 : e.Type' = W32 1
          · obtain ⟨m, Hm⟩ := Hdec.1 H1
            iexists some (.v1 m)
            simp only [ccEntOk]
            isplitr
            · ipureintro; exact H1
            iexists bs
            iframe Hbs
            ipureintro; exact Hm
          by_cases H2 : e.Type' = W32 2
          · obtain ⟨m, Hm⟩ := Hdec.2 H2
            iexists some (.v2 m)
            simp only [ccEntOk]
            isplitr
            · ipureintro; exact H2
            iexists bs
            iframe Hbs
            ipureintro; exact Hm
          iexists none
          unfold ccEntOk
          ipureintro
          rintro (h | h)
          · exact H1 h
          · exact H2 h
    imod Hone with ⟨%c, #Hc⟩
    imodintro
    iexists c :: cs
    unfold ccEntsOk
    iapply (BigSepL2.bigSepL2_cons (Φ := fun _ e o => ccEntOk (GF := GF) e o)).2
    iframe Hc
    iexact Hcs

/-- `r.Step(m)` on a proposal (`m.From` set to the node's id, as `run` does), `r` the
node's raft struct: the batch owned, the proposal legitimately sent (its entries' data:
their updates deposited), its context. Either the one `Propose` built, or (2026-10-10)
one forwarded by a peer. -/
theorem wp_rn_raft_Step_prop (wp_raft_Step : raft.Step.spec (GF := GF) (hG := hG))
    (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (r : Loc) (m : raftpb.Message)
    (ents : List raftpb.Entry) (Hty : m.Type' = MsgProp) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        -- (2026-10-13) for a forwarded conf change's bytes
        inv propDataN (propDataInv γ) ∗
        ownRawNode γ rn id rs ∗ rn.[RawNode, go!"raft"] ↦□ r ∗
        m.Entries' ↦* ents ∗ ownSliceCap raftpb.Entry m.Entries' (DFrac.own 1) ∗
        isMessage γ (absMsg .propose m ents) ∗
        (∃ ctx : List w8, m.Context' ↦*□ ctx) }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step"))
        (Val #({ m with From' := id })))
    {{ (err : GoInterface), RET #err; ownRawNode γ rn id rs }} := by
  iintro %Φ ⟨#Hpkg, #Hpdinv, Hrn, #Hr, Hes, Hcap, #Hm, ⟨%ctx, #Hctx⟩⟩ HΦ
  iNamed Hrn
  ihave #Hr' := rawNodeOwn_raft rn rnv $$ Hrn
  icombine Hr Hr' gives %Heq
  subst Heq
  ihave #Hm' := isMessage_propose_from γ m ents id $$ Hm
  ihave %Hpm := isMessage_propose_pure γ m ents $$ Hm
  obtain ⟨Hterm, Hne, Hlen⟩ := Hpm
  ihave #Hed : iprop([∗list] e ∈ ents, entData γ e) $$ []
  · iunfold isMessage at Hm
    simp only [absMsg, absMsgFrom]
    icases Hm with ⟨-, #Hed⟩
    iexact Hed
  imod propData_ccEnts γ ents ⊤ CoPset.subseteq_top $$ Hpdinv Hed with ⟨%cs, #Hcc⟩
  have Hty' : ({ m with From' := id } : raftpb.Message).Type' = MsgProp := Hty
  imod rdCred_zero_upd (GF := GF) γ with Hcr
  wp_apply wp_raft_Step γ.reCfg γ _ id s ps ({ m with From' := id }) ents ctx rfl
    (by simp only [StepMsg, stepMsgTypes]; rw [Hty']; simp [MsgProp]) (fun _ => Hin)
    (by msg_ne') (by msg_ne')
    (by msg_ne') (by msg_ne')
    (by msg_ne') (by msg_ne')
    (by msg_ne') (by msg_ne')
    (by msg_ne') (by msg_ne')
    (by msg_ne')
    (fun _ => ⟨Hterm, .inr rfl⟩) (by msg_ne') (by msg_ne') (by msg_ne') (by msg_ne') (RestMsgOk.of_ne ⟨by msg_ne', by msg_ne', by msg_ne', by msg_ne', by msg_ne'⟩) Hrel
    $$ [$Hphys $Hghost Hes Hcap Hcr]
  · rw [Hty']
    simp only [ite_true]
    isplitl [Hes Hcap]
    · simp only [named]
      isplitl [Hes]
      · iframe Hes
        iexists cs
        iexact Hcc
      isplitl [Hcap]
      · iexact Hcap
      isplitr
      · ipureintro
        intro _
        exact ⟨Hne, Hlen⟩
      isplitr
      · ipureintro
        intro Hc
        simp [Hty', MsgProp, MsgStorageApplyResp] at Hc
      · imodintro
        iintro %ty %Hty2 _
        try rw [Hty'] at Hty2
        rw [show mtypeOf MsgProp = some .propose from rfl] at Hty2
        cases Hty2
        iapply isMessage_ctx_intro _ .propose _ _ _ ⟨nofun, nofun⟩
        iexact Hm'
    isplitr
    · iexact Hctx
    isplitl [Hcr]
    · simp [MsgProp, MsgReadIndex]; iexact Hcr
    · imodintro
      iintro %Hc
      simp [Hty', MsgProp, MsgSnap] at Hc
  iintro %err %s' %ps' ⟨Hphys, Hghost, %Hrel', %Href, %Hloc, %_, %_, %_, -⟩
  obtain ⟨Hfr, Hap⟩ := Hloc (.inl Hty')
  have Hap' := Hap (fun Hc => by rw [Hty'] at Hc; simp [MsgProp, MsgStorageApplyResp] at Hc)
  have Hc : uint.Z s.logst.committed ≤ uint.Z s'.logst.committed := by
    obtain ⟨recv, Hst⟩ := Href
    have H := Step.commit_mono Hst
    rw [← Hrel.1, ← Hrel'.1] at H
    exact H
  ihave #Hstr' := storedRecs_eq γ _ s'.logst.prev _ s'.logst.stored Hfr.2.2.2.2.1
    Hfr.2.2.2.2.2.1 $$ Hstrecs
  iapply HΦ
  iapply ownRawNode_intro γ rn id rs s' ps' rnv sv steps Hrel' Hin Hasync
    (by rw [Hap']; exact Hdlen) (by rw [Hfr.2.2.1]; exact Hunp)
    (by rw [Hfr.2.2.2.1]; exact Hsnap)
    (stepsOk_mono s s' _ Hfr.1 ⟨Hfr.2.2.2.2.1, Hfr.2.2.2.2.2.1⟩ Hc Hap'
      Hfr.2.2.2.2.2.2.2.1 Hstok)
    (by rw [Hfr.1]; exact Htrm) (by rw [Hfr.2.2.2.2.2.2.1]; exact Hstor)
    (by rw [Hfr.2.2.2.2.2.2.2.1]; exact Hpvoff)
    (by rw [Hfr.2.2.2.2.2.2.2.2]; exact Hrs_out) (by rw [Hfr.2.2.2.2.2.2.2.2]; exact Hrs_unst)
    (Int.le_trans Hrs_clb Hc)
    $$ Hrn Hphys Hghost Hsoft Hsteps Hsteps_cap Hpend Hpown Hdeliv Hstr'

end step

/-! ## `r.applyConfChange`, on the node (2026-10-13) -/

section applycc
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- After `applyConfChange`: the ghost step its result is (`applyCCOk_step`,
`ownRaftGhost_step_0`), and `ownRawNode` re-sealed at the same client-facing state. -/
theorem rawNode_applyCC_reseal (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState)
    (s s' : NState) (ps : PState) (rnv : RawNode) (sv : SoftState) (steps : List raftpb.Message)
    (Hrel : NStateRel s ps) (Hin : id ∈ γ.reCfg) (Hasync : rnv.asyncStorageWrites' = false)
    (Hdlen : rs.delivered.length = (uint.Z s.logst.applying).toNat)
    (Hunp : rs.unpersisted = s.logst.unpersisted) (Hsnap : s.logst.snap = none)
    (Hstok : StepsOk s rs.steps) (Htrm : rs.term = s.term) (Hstor : rs.storage = s.logst.storage)
    (Hpvoff : s.prevote = false) (Hrs_out : rs.outlb = s.gh.outlb)
    (Hrs_unst : rs.unst = s.gh.unst) (Hrs_clb : uint.Z rs.clb ≤ uint.Z s.logst.committed)
    (Hok : ApplyCCOk γ.reCfg id s s') :
    ⊢ rawNodeOwn rn rnv -∗ ownRaftPhys γ.reCfg rnv.raft' id s' -∗ ownRaftGhost (GF := GF) γ id ps -∗
      rnv.prevSoftSt' ↦□ sv -∗ rnv.stepsOnAdvance' ↦* steps -∗
      ownSliceCap raftpb.Message rnv.stepsOnAdvance' (DFrac.own 1) -∗
      ([∗list] _k ↦ m;p ∈ steps;rs.steps, pendingRel γ id m p) -∗
      ([∗list] _k ↦ m;p ∈ steps;rs.steps, pendingOwn m p) -∗
      isCommitted γ rs.delivered -∗
      storedRecs γ s.logst.prev s.logst.stored ={⊤}=∗
      ownRawNode γ rn id rs := by
  obtain ⟨Hst, Hro, Hsf, Htk, Htm, Hpv, Hgh, Hls, Hc⟩ := applyCCOk_step _ _ _ _ Hok
  have Hprev : s'.logst.prev = s.logst.prev := by rw [Hls]
  have Hstored : s'.logst.stored = s.logst.stored := by rw [Hls]
  have Happ : s'.logst.applying = s.logst.applying := by rw [Hls]
  have Hunp' : s'.logst.unpersisted = s.logst.unpersisted := by rw [Hls]
  have Hsnap' : s'.logst.snap = s.logst.snap := by rw [Hls]
  have Hstor' : s'.logst.storage = s.logst.storage := by rw [Hls]
  have Hwf' : NStateWf s' := by
    obtain ⟨-, H1, H2⟩ := Hrel
    exact ⟨by rw [Hsf, Hro]; exact H1, by rw [Htk]; exact H2⟩
  iintro Hrn Hphys Hghost #Hsoft Hsteps Hcap #Hpend Hpown #Hdeliv #Hstrecs
  rw [← Hrel.1] at *
  imod ownRaftGhost_step_0 γ id _ _ Hst $$ Hghost with Hghost
  ihave #Hstr' := storedRecs_eq γ _ s'.logst.prev _ s'.logst.stored Hprev Hstored $$ Hstrecs
  iapply ownRawNode_intro γ rn id rs s' (toPState s') rnv sv steps ⟨rfl, Hwf'⟩ Hin Hasync
    (by rw [Happ]; exact Hdlen) (by rw [Hunp']; exact Hunp) (by rw [Hsnap']; exact Hsnap)
    (stepsOk_mono_le s s' _ (by rw [Htm]; exact Int.le_refl _) ⟨Hprev, Hstored⟩ Hc Happ Hpv Hstok)
    (by rw [Htm]; exact Htrm) (by rw [Hstor']; exact Hstor) (by rw [Hpv]; exact Hpvoff)
    (by rw [Hgh]; exact Hrs_out) (by rw [Hgh]; exact Hrs_unst) (Int.le_trans Hrs_clb Hc)
    $$ Hrn Hphys Hghost Hsoft Hsteps Hcap Hpend Hpown Hdeliv Hstr'

/-- `r.applyConfChange(cc)` on the node's raft struct, for a change that leaves the
configuration unchanged (`node.run`'s `confc` arm); the ghost step inside. -/
theorem wp_rn_raft_applyConfChange
    (wp_raft_applyConfChange : raft.applyConfChange.spec (GF := GF) (hG := hG))
    (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (r : Loc) (cc : raftpb.ConfChangeV2)
    (ccs : List raftpb.ConfChangeSingle)
    (Hn : CCShrink γ.reCfg cc.Transition' ccs) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        ownRawNode γ rn id rs ∗ rn.[RawNode, go!"raft"] ↦□ r ∗ cc.Changes' ↦*□ ccs }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"applyConfChange")) (Val #cc))
    {{ (cs : raftpb.ConfState) (xs ls : List w64), RET #cs;
        ownRawNode γ rn id rs ∗ cs.Voters' ↦* xs ∗ cs.Learners' ↦* ls ∗
          ⌜xs ≡ₚ elements γ.reCfg ∧ (∀ k ∈ ls, k ∉ γ.reCfg) ∧
          cs.VotersOutgoing'.len = W64 0 ∧
          cs.LearnersNext'.len = W64 0 ∧ cs.AutoLeave' = false⌝ }} := by
  iintro %Φ ⟨#Hpkg, Hrn, #Hr, #Hccs⟩ HΦ
  iNamed Hrn
  ihave #Hr' := rawNodeOwn_raft rn rnv $$ Hrn
  icombine Hr Hr' gives %Heq
  subst Heq
  iapply wp_fupd
  icases ownRaftPhys_progress_dom γ.reCfg rnv.raft' id s $$ Hphys with ⟨%Hsub, Hphys⟩
  icases ownRaftPhys_progress_size γ.reCfg rnv.raft' id s $$ Hphys with ⟨%Hsz, Hphys⟩
  obtain ⟨lrn', Hd', Hsz', Hn'⟩ := applyCC_of_shrink γ.reCfg s.progress _ _ Hn Hsub Hsz
  wp_apply +noauto wp_raft_applyConfChange γ.reCfg rnv.raft' id s cc ccs DFrac.discard lrn' Hd'
      Hsz' Hn'
    $$ [$Hphys $Hccs] as %cs %xs %ls %s' ⟨Hphys, -, Hvoters, Hls, %Hcs0, %Hok⟩
  imod rawNode_applyCC_reseal γ rn id rs s s' ps rnv sv steps Hrel Hin Hasync Hdlen Hunp Hsnap
    Hstok Htrm Hstor Hpvoff Hrs_out Hrs_unst Hrs_clb Hok
    $$ Hrn Hphys Hghost Hsoft Hsteps Hsteps_cap Hpend Hpown Hdeliv Hstrecs with Hrn
  try wp_auto
  imodintro
  iapply HΦ $$ %cs %xs %ls
  iframe Hrn Hvoters Hls
  ipureintro
  exact ⟨Hcs0.1, fun k hk => Hd' k ((GMap.elem_of_elements _ _).1 (Hcs0.2.1.mem_iff.1 hk)),
    Hcs0.2.2⟩

/-- The struct out of the node with the node's membership (`ownRawNode_borrow`'s and
`Hin`): for `_, ok := r.trk.Progress[r.id]`, which finds the node. -/
theorem ownRawNode_borrow_in (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (r : Loc) :
    ⊢ ownRawNode (GF := GF) γ rn id rs -∗ rn.[RawNode, go!"raft"] ↦□ r -∗
      ∃ s : NState, ⌜id ∈ γ.reCfg⌝ ∗ ownRaftPhys γ.reCfg r id s ∗
        (ownRaftPhys γ.reCfg r id s -∗ ownRawNode γ rn id rs) := by
  iintro H #Hr
  iNamed H
  ihave #Hr' := rawNodeOwn_raft rn rnv $$ Hrn
  icombine Hr Hr' gives %Heq
  subst Heq
  iexists s
  isplitr
  · ipureintro; exact Hin
  isplitl [Hphys]
  · iexact Hphys
  iintro Hphys
  iapply ownRawNode_intro γ rn id rs s ps rnv sv steps Hrel Hin Hasync Hdlen Hunp Hsnap Hstok
    Htrm Hstor Hpvoff Hrs_out Hrs_unst Hrs_clb
    $$ Hrn Hphys Hghost Hsoft Hsteps Hsteps_cap Hpend Hpown Hdeliv Hstrecs

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
  iapply ownRawNode_intro γ rn id rs s ps rnv sv steps Hrel Hin Hasync Hdlen Hunp Hsnap Hstok
    Htrm Hstor Hpvoff Hrs_out Hrs_unst Hrs_clb
    $$ Hrn Hphys Hghost Hsoft Hsteps Hsteps_cap Hpend Hpown Hdeliv Hstrecs

/-- A `Ready` `run` computed and abandoned but keeps armed (`readyc` set): what
`ownRawNodeIdle_ready` needs of it, and, by the lower bounds of `rs`, that it holds no
messages (`SliceShape`, `k ≤ rs.outlb`) and no entries (`es ≠ [] → rs.unst`) once the
node is idle; and its read states with their facts (2026-10-13, persistent: from
`readyWithoutAccept`). -/
def staleOk (γ : NodeNames) (rd : Ready) (rs : RNState) : IProp GF :=
  iprop(∃ (ce es : List raftpb.Entry) (k : Nat),
    (⌜rd.SoftState' = null⌝ ∨ ∃ v : SoftState, rd.SoftState' ↦□ v) ∗
    rd.CommittedEntries' ↦*□ ce ∗ ownSliceCap raftpb.Entry rd.CommittedEntries' (DFrac.own 1) ∗
    isCommitted γ.raft (rs.delivered ++ ce) ∗ rd.Entries' ↦*□ es ∗
    (∃ sts : List ReadState, rd.ReadStates' ↦*□ sts ∗ [∗list] st ∈ sts, readStateOk γ.raft st) ∗
    ⌜rd.Snapshot' = zero_val raftpb.Snapshot ∧
      (es ≠ [] → rs.unst = true) ∧ SliceShape rd.Messages' k ∧ k ≤ rs.outlb ∧
      (∀ e, ce.getLast? = some e → uint.Z e.Index' ≤ uint.Z rs.clb ∧
        uint.Z e.Index' = (rs.delivered.length : Int) + (ce.length : Int))⌝)

/-- A `Ready` `readyWithoutAccept` just computed: its outputs. -/
def freshOk (γ : NodeNames) (rd : Ready) (rs : RNState) (ce es : List raftpb.Entry)
    (ms : List raftpb.Message) : IProp GF :=
  iprop(rd.CommittedEntries' ↦*□ ce ∗ isCommitted γ.raft (rs.delivered ++ ce) ∗
    rd.Entries' ↦*□ es ∗ rd.Messages' ↦* ms ∗
    ownSliceCap raftpb.Message rd.Messages' (DFrac.own 1) ∗
    ([∗list] m ∈ ms, isRaftMsg γ.raft m) ∗
    (∃ sts : List ReadState, rd.ReadStates' ↦*□ sts ∗ [∗list] st ∈ sts, readStateOk γ.raft st) ∗
    ⌜(∀ m ∈ ms, uint.Z m.Term' ≤ uint.Z rs.term) ∧
     rd.Snapshot' = zero_val raftpb.Snapshot⌝)

/-- Both halves of `rof`: no `Ready` handed out. -/
def rofFull (γ : NodeNames) : IProp GF :=
  iprop(∃ x : List raftpb.Entry × List raftpb.Entry × List raftpb.Entry,
    dghostVar γ.rof (DFrac.own (1 : Qp).half) x ∗ dghostVar γ.rof (DFrac.own (1 : Qp).half) x)

/-- `run`'s state besides the node, at the loop's head (`ac`: `advancec`, `rc`: `readyc`,
`rd`: `rd`): no `Ready` handed out (`ac` nil; then `rc` is nil or a stale `Ready` is
armed), or one handed out and its `Advance` awaited (`ac` is `n.advancec`). -/
def headRest (γ : NodeNames) (nv : node) (rs : RNState) (ac rc : GoChan) (rd : Ready) :
    IProp GF :=
  iprop(termLB γ.bud rs.term ∗ ⌜rs.storage = γ.stor⌝ ∗
    ((⌜ac = chan.nil ∧ rs.steps = [] ∧ rs.unpersisted = []⌝ ∗
        dghostVar γ.dlv (DFrac.own (1 : Qp).half) rs.delivered ∗ rofFull γ ∗
        (⌜rc = chan.nil⌝ ∨ (⌜rc = nv.readyc'⌝ ∗ staleOk γ rd rs)))
     ∨ (⌜ac = nv.advancec' ∧ rc = chan.nil ∧ rs.unst = false⌝ ∗
        ∃ d ce : List raftpb.Entry, ⌜rs.delivered = d ++ ce⌝ ∗
          dghostVar γ.rof (DFrac.own (1 : Qp).half) (d, ce, rs.unpersisted))))

/-- `run`'s loop invariant, but for its local variables. -/
def runHead (γ : NodeNames) (id : w64) (nv : node) (ac rc : GoChan) (rd : Ready) : IProp GF :=
  iprop(∃ rs : RNState, ownRawNode γ.raft nv.rn' id rs ∗ headRest γ nv rs ac rc rd)

/-- `run`'s state after its first statement (`HasReady`, `readyWithoutAccept`): the node
may also be at a fresh `Ready` (`ownRawNodeReady`) or idle with a stale one armed. -/
def runMid (γ : NodeNames) (id : w64) (nv : node) (ac rc : GoChan) (rd : Ready) : IProp GF :=
  iprop((⌜ac = nv.advancec'⌝ ∗ runHead γ id nv ac rc rd) ∨
    (⌜ac = chan.nil⌝ ∗ ∃ rs : RNState, termLB γ.bud rs.term ∗
      ⌜rs.storage = γ.stor ∧ rs.steps = [] ∧ rs.unpersisted = []⌝ ∗
      dghostVar γ.dlv (DFrac.own (1 : Qp).half) rs.delivered ∗ rofFull γ ∗
      ((⌜rc = chan.nil⌝ ∗ ownRawNode γ.raft nv.rn' id rs) ∨
       (⌜rc = nv.readyc'⌝ ∗ ∃ (ce es : List raftpb.Entry) (ms : List raftpb.Message),
          ownRawNodeReady γ.raft nv.rn' id rs rd ce es ms false ∗ freshOk γ rd rs ce es ms) ∨
       (⌜rc = nv.readyc'⌝ ∗ ownRawNodeIdle γ.raft nv.rn' id rs ∗ staleOk γ rd rs))))

theorem headRest_termLB (γ : NodeNames) (nv : node) (rs : RNState) (ac rc : GoChan)
    (rd : Ready) :
    ⊢ headRest (GF := GF) γ nv rs ac rc rd -∗ termLB γ.bud rs.term ∗ headRest γ nv rs ac rc rd := by
  iintro H
  unfold headRest
  icases H with ⟨#Hlb, H⟩
  iframe Hlb H

/-- A step changes only the node's term. -/
theorem headRest_term (γ : NodeNames) (nv : node) (rs : RNState) (ac rc : GoChan) (rd : Ready)
    (t : w64) :
    ⊢ headRest (GF := GF) γ nv rs ac rc rd -∗ termLB γ.bud t -∗
      headRest γ nv { rs with term := t } ac rc rd := by
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
      termLB γ.bud rs.term ∗ ⌜rs.storage = γ.stor ∧ rs.steps = [] ∧ rs.unpersisted = []⌝ ∗
      dghostVar γ.dlv (DFrac.own (1 : Qp).half) rs.delivered ∗ rofFull γ ∗
      (⌜rc = chan.nil⌝ ∨ (⌜rc = nv.readyc'⌝ ∗ staleOk γ rd rs)) := by
  iintro H
  unfold headRest
  icases H with ⟨#Hlb, %Hst, (⟨%Hs, Hdlv, Hrof, Hrc⟩ | ⟨%Hs, -⟩)⟩
  · iframe Hlb Hdlv Hrof Hrc
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
  icases Hrest with ⟨#Hlb, %Hst, (⟨%Hs, Hdlv, Hrof, Hrc⟩ | ⟨%Hs, Hd⟩)⟩
  · exact absurd Hs.1 Hac
  isplitr
  · ipureintro; exact Hs.1
  iexists rs
  iframe Hrn Hlb
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
  icases H with (⟨-, H⟩ | ⟨%Hac, %rs, #Hlb, %Hrs, Hdlv, Hrof, H⟩)
  · iexact H
  obtain ⟨Hst, Hsteps, Hunp⟩ := Hrs
  unfold runHead
  icases H with (⟨%Hrc, Hrn⟩ | ⟨%Hrc, %ce, %es, %ms, Hrn, Hf⟩ | ⟨%Hrc, Hrn, Hstale⟩)
  · iexists rs
    iframe Hrn
    unfold headRest
    iframe Hlb
    isplitr
    · ipureintro; exact Hst
    ileft
    iframe Hdlv Hrof
    isplitr
    · ipureintro; exact ⟨Hac, Hsteps, Hunp⟩
    ileft; ipureintro; exact Hrc
  · unfold freshOk
    icases Hf with ⟨#Hce, #Hcommitted, #Hents, Hmsgs, Hmsgs_cap, #Hmsgs_ok, #Hrsts, %Hfacts⟩
    ihave %Hshape := ownSlice_shape _ _ _ $$ Hmsgs
    icases ownRawNodeReady_abandon_keep γ.raft nv.rn' id rs rd ce es ms Hsteps Hunp
      $$ Hmsgs Hmsgs_cap Hrn with ⟨Hce_cap, #Hrdsoft, %n, %u, %c, %Hnuc, Hrn⟩
    iexists { rs with outlb := n, unst := u, clb := c }
    iframe Hrn
    unfold headRest
    iframe Hlb
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
    iexists ce, es, ms.length
    iframe Hrdsoft Hce Hce_cap Hcommitted Hents Hrsts
    ipureintro
    exact ⟨Hfacts.2, Hnuc.2.1, Hshape, Hnuc.1, Hnuc.2.2⟩
  · iexists rs
    ihave Hrn := ownRawNodeIdle_ownRawNode γ.raft nv.rn' id rs $$ Hrn
    iframe Hrn
    unfold headRest
    iframe Hlb
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

/-- A `Ready`'s messages are of terms within the budget: at most the node's. -/
theorem readyMsgs_termLB (γ : NodeNames) (t : w64) (ms : List raftpb.Message)
    (H : ∀ m ∈ ms, uint.Z m.Term' ≤ uint.Z t) :
    ⊢ ([∗list] m ∈ ms, isRaftMsg (GF := GF) γ.raft m) -∗ termLB γ.bud t -∗
      [∗list] m ∈ ms, isRaftMsg γ.raft m ∗ termLB γ.bud m.Term' := by
  induction ms with
  | nil =>
    iintro - -
    iapply BigSepL.bigSepL_nil.2
    iempintro
  | cons m ms ih =>
    iintro Hl #Hlb
    icases BigSepL.bigSepL_cons.1 $$ Hl with ⟨Hm, Hl⟩
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hm]
    · iframe Hm
      iapply termLB_le γ.bud t m.Term' (H m (List.mem_cons_self ..)) $$ Hlb
    · iapply ih (fun m' hm => H m' (List.mem_cons_of_mem _ hm)) $$ Hl Hlb

/-- What `readyc` and `advancec` may be. -/
theorem runMid_chans (γ : NodeNames) (id : w64) (nv : node) (ac rc : GoChan) (rd : Ready) :
    ⊢ runMid (GF := GF) γ id nv ac rc rd -∗
      ⌜(rc = chan.nil ∨ rc = nv.readyc') ∧ (ac = chan.nil ∨ ac = nv.advancec')⌝ := by
  iintro H
  unfold runMid
  icases H with (⟨%Hac, H⟩ | ⟨%Hac, %rs, -, -, -, -, H⟩)
  · unfold runHead
    icases H with ⟨%rs, -, Hrest⟩
    unfold headRest
    icases Hrest with ⟨-, -, (⟨%Hs, -, -, (%Hrc | ⟨%Hrc, -⟩)⟩ | ⟨%Hs, -⟩)⟩
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
      ⌜ac = chan.nil⌝ ∗ ∃ rs : RNState, termLB γ.bud rs.term ∗
        ⌜rs.storage = γ.stor ∧ rs.steps = [] ∧ rs.unpersisted = []⌝ ∗
        dghostVar γ.dlv (DFrac.own (1 : Qp).half) rs.delivered ∗ rofFull γ ∗
        ((∃ (ce es : List raftpb.Entry) (ms : List raftpb.Message),
            ownRawNodeReady γ.raft nv.rn' id rs rd ce es ms false ∗ freshOk γ rd rs ce es ms) ∨
         (ownRawNodeIdle γ.raft nv.rn' id rs ∗ staleOk γ rd rs)) := by
  iintro H
  unfold runMid
  icases H with (⟨%Hac, H⟩ | ⟨%Hac, %rs, #Hlb, %Hrs, Hdlv, Hrof, H⟩)
  · unfold runHead
    icases H with ⟨%rs, -, Hrest⟩
    unfold headRest
    icases Hrest with ⟨-, -, (⟨%Hs, -⟩ | ⟨%Hs, -⟩)⟩
    · exact absurd (Hac.symm.trans Hs.1) Hnn'
    · exact absurd Hs.2.1 Hnn
  isplitr
  · ipureintro; exact Hac
  iexists rs
  iframe Hlb Hdlv Hrof
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
      ∃ (rs : RNState) (d ce : List raftpb.Entry), ownRawNode γ.raft nv.rn' id rs ∗
        termLB γ.bud rs.term ∗
        ⌜rs.storage = γ.stor ∧ rc = chan.nil ∧ rs.unst = false ∧ rs.delivered = d ++ ce⌝ ∗
        dghostVar γ.rof (DFrac.own (1 : Qp).half) (d, ce, rs.unpersisted) := by
  iintro H
  unfold runMid
  icases H with (⟨-, H⟩ | ⟨%Hac, -⟩)
  · unfold runHead
    icases H with ⟨%rs, Hrn, Hrest⟩
    unfold headRest
    icases Hrest with ⟨#Hlb, %Hst, (⟨%Hs, -⟩ | ⟨%Hs, %d, %ce, %Hd, Hrof⟩)⟩
    · exact absurd Hs.1 Hnn
    iexists rs, d, ce
    iframe Hrn Hlb Hrof
    ipureintro; exact ⟨Hst, Hs.2.1, Hs.2.2, Hd⟩
  · exact absurd Hac Hnn

/-- The leader fields, in any of `run`'s states. -/
theorem runMid_lead (γ : NodeNames) (id : w64) (nv : node) (ac rc : GoChan) (rd : Ready)
    (r : Loc) :
    ⊢ runMid (GF := GF) γ id nv ac rc rd -∗ nv.rn'.[RawNode, go!"raft"] ↦□ r -∗
      leadFields r (runMid γ id nv ac rc rd) := by
  iintro H #Hr
  unfold runMid
  icases H with (⟨%Hac, H⟩ | ⟨%Hac, %rs, #Hlb, %Hrs, Hdlv, Hrof, H⟩)
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
    iframe Hlb Hdlv Hrof
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
    iframe Hlb Hdlv Hrof
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
    iframe Hlb Hdlv Hrof
    isplitr
    · ipureintro; exact Hrs
    iright; iright
    isplitr
    · ipureintro; exact Hrc
    iframe Hstale
    iapply Hback $$ Hl Ht

end states

end EtcdGrove
end Perennial
