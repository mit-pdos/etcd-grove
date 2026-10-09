/- Port of election_proof/proof_RawNode__Advance.v (857d09190).

Each queued message goes through `Step`'s spec; `StepsOk` (`InvRawnode.lean`) is the loop
invariant on the rest of the queue, carried across each step by `Step`'s `LocalStepOk`
(`applying` kept) and `Step.commit_mono` (`committed` not moving back).

Lean notes: like its spec, the section fixes `hlc := HasLC.hasLC` and has `[AllG GF]`.
`wp_step_pending` is Rocq's; `pending_ok`, `apply_ack_ok_mono`, `advance_ok_cons` are
`PendingOk`, `applyAckOk_mono`, `stepsOk_cons` (`InvRawnode.lean`). Rocq's local
`in_types`/`not_ty` are the local macros `msg_ne`.
-/
module

public import Spec.go_etcd_io.raft.v3.RawNode__Advance
public import Spec.go_etcd_io.raft.v3.raft__Step
-- `Step.commit_mono`
public import Proof.go_etcd_io.raft.v3.Protocol.Facts

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

private theorem drop_cons_of_lookup {α : Type _} {l : List α} {k : Nat} {x : α}
    (h : l[k]? = some x) : l.drop k = x :: l.drop (k + 1) := by
  obtain ⟨hk, rfl⟩ := List.getElem?_eq_some_iff.1 h
  exact List.drop_eq_getElem_cons hk

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]
variable [AllG GF]

/-- A premise of `Step` about another message type: the type is not it. -/
local macro "msg_ne" : tactic => `(tactic| (intro Hc; simp [MsgHup, MsgVote, MsgVoteResp,
  MsgPreVote, MsgPreVoteResp, MsgApp, MsgHeartbeat, MsgAppResp, MsgHeartbeatResp, MsgSnap,
  MsgBeat, MsgProp, MsgStorageAppendResp, MsgStorageApplyResp, appendAckMsg,
  applyAckMsg] at Hc))

/-- One pending message through `Step`'s spec: the `MsgStorageAppendResp` acknowledges
persisted entries (`StableOk`) because its index is in progress, nothing is unpersisted
and no snapshot is pending -- Rocq's `ready_stable_ok`. -/
private theorem wp_step_pending
    (wp_raft_Step : raft.Step.spec (GF := GF) (hG := hG))
    (γ : RaftNames) (r : Loc) (id : w64) (s : NState)
    (ps : PState) (m : raftpb.Message) (p : Pending)
    (Hin : id ∈ γ.reCfg) (Hrel : NStateRel s ps) (Hok : PendingOk s p)
    (Hsnap : s.logst.snap = none) (Hunp : s.logst.unpersisted = []) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhys γ.reCfg r id s ∗
        ownRaftGhost γ id ps ∗ pendingRel id m p ∗ pendingOwn m p }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #m))
    {{ (err : GoInterface) (s' : NState) (ps' : PState), RET #err;
        ownRaftPhys γ.reCfg r id s' ∗ ownRaftGhost γ id ps' ∗
        ⌜NStateRel s' ps' ∧ (∃ recv, Step γ.reCfg id ps recv ps') ∧
         s'.logst.applying = s.logst.applying ∧
         s'.logst.unpersisted = s.logst.unpersisted ∧ s'.logst.snap = s.logst.snap ∧
         s'.term = s.term⌝ }} := by
  iintro %Φ ⟨#Hinit, Hphys, Hghost, #Hp, Hown⟩ HΦ
  cases p with
  | self a => exact Hok.elim
  | appendAck t e =>
    unfold pendingRel
    icases Hp with %Hm
    subst Hm
    obtain ⟨Hle, Hlt⟩ := Hok
    iapply wp_raft_Step γ.reCfg γ r id s ps (appendAckMsg id t e) [] [] rfl
      (by simp [StepMsg, stepMsgTypes, appendAckMsg]) Hin
      (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne)
      (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne)
      (fun _ => ⟨rfl, Hle, fun _ _ _ => ⟨Hsnap, Hlt, Hunp⟩⟩) (by msg_ne) Hrel
      $$ [$Hinit $Hphys $Hghost]
    · have hP : (appendAckMsg id t e).Type' ≠ MsgProp := by msg_ne
      simp only [hP, ↓reduceIte, named]
      have Hty0 : mtypeOf (appendAckMsg id t e).Type' = none := rfl
      simp only [appendAckMsg] at Hty0 ⊢
      isplitr
      · isplitr
        · iapply ownSlice_nil
        isplitr
        · iapply ownSliceCap_nil
        isplitr
        · ipureintro; msg_ne
        isplitr
        · ipureintro; msg_ne
        imodintro
        iintro %ty %Hty
        rw [Hty0] at Hty
        cases Hty
      isplitr
      · itrivial
      isplitr
      · iexists []
        isplitr
        · iapply ownSlice_nil
        ipureintro
        exact ⟨by simp [campaignTransfer], fun _ => rfl⟩
      imodintro
      iintro %Hc
      exfalso
      revert Hc
      msg_ne
    · inext
      iintro %err %s' %ps' ⟨Hphys, Hghost, %Hrel', %Hstp, %Hloc, -⟩
      obtain ⟨Hfr, Hap⟩ := Hloc (.inr (.inl rfl))
      iapply HΦ $$ %err %s' %ps'
      iframe Hphys Hghost
      ipureintro
      exact ⟨Hrel', Hstp, Hap (fun Hc => absurd Hc (by msg_ne)), Hfr.2.2.1, Hfr.2.2.2, Hfr.1⟩
  | applyAck ce =>
    unfold pendingRel
    icases Hp with ⟨%sl, %Hm, #Hsl⟩
    subst Hm
    unfold pendingOwn
    iapply wp_raft_Step γ.reCfg γ r id s ps (applyAckMsg id sl) ce [] rfl
      (by simp [StepMsg, stepMsgTypes, applyAckMsg]) Hin
      (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne)
      (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne)
      (by msg_ne) (fun _ => rfl) Hrel $$ [$Hinit $Hphys $Hghost Hown]
    · have hP : (applyAckMsg id sl).Type' ≠ MsgProp := by msg_ne
      simp only [hP, ↓reduceIte, named]
      have Hty0 : mtypeOf (applyAckMsg id sl).Type' = none := rfl
      simp only [applyAckMsg] at Hty0 ⊢
      isplitl [Hown]
      · isplitr
        · iexact Hsl
        isplitl [Hown]
        · iexact Hown
        isplitr
        · ipureintro; msg_ne
        isplitr
        · ipureintro; intro _ e He; exact (Hok e He).1
        imodintro
        iintro %ty %Hty
        rw [Hty0] at Hty
        cases Hty
      isplitr
      · itrivial
      isplitr
      · iexists []
        isplitr
        · iapply ownSlice_nil
        ipureintro
        exact ⟨by simp [campaignTransfer], fun _ => rfl⟩
      imodintro
      iintro %Hc
      exfalso
      revert Hc
      msg_ne
    · inext
      iintro %err %s' %ps' ⟨Hphys, Hghost, %Hrel', %Hstp, %Hloc, -⟩
      obtain ⟨Hfr, Hap⟩ := Hloc (.inr (.inr rfl))
      iapply HΦ $$ %err %s' %ps'
      iframe Hphys Hghost
      ipureintro
      exact ⟨Hrel', Hstp, Hap (fun _ e He => (Hok e He).2), Hfr.2.2.1, Hfr.2.2.2, Hfr.1⟩

theorem RawNode.Advance.wp_proof
    (wp_raft_Step : raft.Step.spec (GF := GF) (hG := hG)) :
    RawNode.Advance.spec (GF := GF) (hG := hG) := by
  intro γ rn id rs rd Hadv0 Hunp0
  wp_start as H
  iNamed H
  iNamed Hrn
  have Hok := Hadv Hadv0
  have Hunp' : s.logst.unpersisted = [] := Hunp ▸ Hunp0
  wp_auto
  rw [Hasync]
  wp_auto
  ihave %Hlen := BigSepL2.bigSepL2_length $$ Hpend
  ihave %Hsl := ownSlice_len _ _ _ $$ Hsteps
  -- the range construct's own counter `i_ptr` (Rocq's `j`) and the body's `i` share a
  -- Go name; rename the body's
  rename_i ibp
  irename: (ibp ↦ (_ : w64)) => ib
  ihave IH : iprop(∃ (n : w64) (s1 : NState) (ps1 : PState) (steps1 : List raftpb.Message)
        (mv : raftpb.Message) (iv : w64),
      "i" ∷ i_ptr ↦ n ∗ "m" ∷ m_ptr ↦ mv ∗ "ib" ∷ ibp ↦ iv ∗
      "Hphys" ∷ ownRaftPhys γ.reCfg rnv.raft' id s1 ∗ "Hghost" ∷ ownRaftGhost γ id ps1 ∗
      "Hsteps" ∷ rnv.stepsOnAdvance' ↦* steps1 ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (steps.length : Int)⌝ ∗
      "%Hsteps1" ∷ ⌜steps1.length = steps.length ∧
                    steps1.drop (sint.nat n) = steps.drop (sint.nat n)⌝ ∗
      "%Hrel1" ∷ ⌜NStateRel s1 ps1⌝ ∗
      "%Hs1" ∷ ⌜s1.logst.applying = s.logst.applying ∧
                s1.logst.unpersisted = s.logst.unpersisted ∧ s1.logst.snap = s.logst.snap ∧
                s1.term = s.term⌝ ∗
      "%Hok1" ∷ ⌜StepsOk s1 (rs.steps.drop (sint.nat n))⌝ ∗
      "Hpown" ∷ ([∗list] _k ↦ m;p ∈ steps.drop (sint.nat n);rs.steps.drop (sint.nat n),
                   pendingOwn m p))
    $$ [i m ib Hphys Hghost Hsteps Hpown]
  · iexists W64 0, s, ps, steps, zero_val raftpb.Message, zero_val w64
    have H0 : sint.nat (W64 0) = 0 := rfl
    rw [H0, List.drop_zero, List.drop_zero]
    simp only [named]
    iframe
    ipureintro
    exact ⟨by word, ⟨trivial, trivial⟩, Hrel, by simp, Hok⟩
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.Z n < sint.Z rnv.stepsOnAdvance'.len := Hif
    clear Hif
    -- the next pending message
    list_elem steps (sint.nat n) as mm
    list_elem rs.steps (sint.nat n) as p
    have Hmm1 : steps1[sint.nat n]? = some mm := by
      have H := congrArg (fun l => l[0]?) Hsteps1.2
      simp only [List.getElem?_drop, Nat.add_zero] at H
      rw [H]; exact Hmm_lookup
    ihave #Hpm := BigSepL2.bigSepL2_lookup (Φ := fun _ m p => pendingRel (GF := GF) id m p)
      Hmm_lookup Hp_lookup $$ Hpend
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hn.1, Hlt⟩)]
    wp_apply wp_load_slice_index rnv.stepsOnAdvance' (sint.Z n) steps1 (DFrac.own 1) mm Hn.1
      $$ [Hsteps] with Hsteps
    · iframe
      ipureintro
      exact Hmm1
    rw [drop_cons_of_lookup Hp_lookup] at Hok1
    rw [drop_cons_of_lookup Hmm_lookup, drop_cons_of_lookup Hp_lookup]
    icases Hpown with ⟨Hpo, Hpown⟩
    have HnS : sint.nat n + 1 = sint.nat (n + W64 1) := by word
    rw [HnS] at Hok1 ⊢
    obtain ⟨Hpok, Hrest⟩ := stepsOk_cons _ _ _ Hok1
    wp_apply wp_step_pending wp_raft_Step γ rnv.raft' id s1 ps1 mm p Hin
      Hrel1 Hpok (Hs1.2.2.1.trans Hsnap) (Hs1.2.1.trans Hunp')
      $$ [$Hphys $Hghost $Hpm $Hpo] as %err %s2 %ps2 ⟨Hphys, Hghost, %Hst2⟩
    obtain ⟨Hrel2, ⟨recv2, Hst2⟩, Ha2, Hu2, Hsn2, Ht2⟩ := Hst2
    -- `stepsOnAdvance[i] = pb.Message{}`
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hn.1, Hlt⟩)]
    wp_apply wp_store_slice_index rnv.stepsOnAdvance' (sint.Z n) steps1 (zero_val raftpb.Message)
      $$ [Hsteps] with Hsteps
    · iframe
      ipureintro
      constructor <;> word
    wp_for_post
    have Hc12 : uint.Z s1.logst.committed ≤ uint.Z s2.logst.committed := by
      have H := Step.commit_mono Hst2
      rw [← Hrel1.1, ← Hrel2.1] at H
      exact H
    iframe
    iexists n + W64 1, s2, ps2, steps1.set (sint.Z n).toNat (zero_val raftpb.Message), mm, n
    iframe
    ipureintro
    refine ⟨by word, ⟨by rw [List.length_set]; exact Hsteps1.1, ?_⟩, Hrel2,
      ⟨Ha2.trans Hs1.1, Hu2.trans Hs1.2.1, Hsn2.trans Hs1.2.2.1, Ht2.trans Hs1.2.2.2⟩,
      Hrest s2 Hc12 Ha2⟩
    rw [← HnS, List.drop_set_of_lt (by simp [sint.nat]), ← List.drop_drop, ← List.drop_drop,
      Hsteps1.2]
  · -- the loop is done: `stepsOnAdvance = stepsOnAdvance[:0]`
    ihave %Hwf := ownSlice_wf _ _ _ $$ Hsteps
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by word))]
    wp_auto
    icases (ownSlice_slice (W64 0) (W64 0) _ _ _ (by word)).1 $$ Hsteps with ⟨-, Hsl0, Hrest⟩
    ihave Hcap0 := ownSlice_slice_absorb_capacity _ _ (W64 0) (W64 0) (by word)
      $$ [$Hrest $Hsteps_cap]
    have Hsub : subslice (sint.nat (W64 0)) (sint.nat (W64 0)) steps1 = [] := by
      simp [subslice]
    rw [Hsub]
    iapply HΦ
    iapply ownRawNode_intro γ rn id { rs with steps := [] } s1 ps1
      { rnv with stepsOnAdvance' := slice.slice rnv.stepsOnAdvance' raftpb.Message (W64 0) (W64 0) }
      sv [] Hrel1 Hin Hasync (by rw [Hs1.1]; exact Hdlen) (by rw [Hs1.2.1]; exact Hunp)
      (by rw [Hs1.2.2.1]; exact Hsnap) (fun _ => by simp [StepsOk])
      (by rw [Hs1.2.2.2]; exact Htrm)
      $$ Hrn Hphys Hghost Hsoft Hsl0 Hcap0 [] [] Hdeliv
    · iempintro
    · iempintro

end proof

end EtcdGrove
end Perennial
