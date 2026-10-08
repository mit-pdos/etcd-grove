/- Port of election_proof/proof_RawNode__Advance.v (857d09190).

Lean notes: like its spec, the section fixes `hlc := HasLC.hasLC` and has `[AllG GF]`.
`pending_ok`, `wp_step_pending`, `apply_ack_ok_mono`, `advance_ok_cons` are
`PendingOk`, `wp_step_pending`, `applyAckOk_mono`, `advanceOk_cons` (private). Rocq's
local `in_types`/`not_ty` are the local macros `msg_ne`.
-/
import EtcdGrove.Raft.Spec.RawNode__Advance
import EtcdGrove.Raft.Spec.raft__Step

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-- What `AdvanceOk` says about one pending message, at the state it is stepped in. -/
private def PendingOk [FfiSyntax] (s : NState) (p : Pending) : Prop :=
  match p with
  | .appendAck t e =>
      uint.Z t ≤ uint.Z s.term ∧
      (t = W64 0 ∨ t = s.term → e.index' ≠ W64 0 → StableOk s.logst e)
  | .applyAck _ => ApplyAckOk s p
  | .self _ => False

private theorem applyAckOk_mono [FfiSyntax] (s s' : NState) (p : Pending)
    (Hc : uint.Z s.logst.committed ≤ uint.Z s'.logst.committed) :
    ApplyAckOk s p → ApplyAckOk s' p := by
  cases p with
  | applyAck ce =>
    intro H e He
    have := H e He
    omega
  | _ => intro H; exact H

/-- The head of an `AdvanceOk` queue is steppable now, and the rest stays `AdvanceOk`
at any state with a commit index no smaller. -/
private theorem advanceOk_cons [FfiSyntax] (s : NState) (p : Pending) (rest : List Pending) :
    AdvanceOk s (p :: rest) →
    PendingOk s p ∧
    ∀ s' : NState, uint.Z s.logst.committed ≤ uint.Z s'.logst.committed →
      AdvanceOk s' rest := by
  have Hrest : ∀ s' : NState, uint.Z s.logst.committed ≤ uint.Z s'.logst.committed →
      (∀ q ∈ rest, ApplyAckOk s q) → AdvanceOk s' rest := by
    intro s' Hc Hr
    have Hr' : ∀ q ∈ rest, ApplyAckOk s' q := fun q Hq => applyAckOk_mono s s' q Hc (Hr q Hq)
    cases rest with
    | nil => intro q Hq; cases Hq
    | cons q rest =>
      cases q with
      | appendAck t e => exact absurd (Hr' _ List.mem_cons_self) id
      | self a => exact Hr' _ List.mem_cons_self |>.elim
      | applyAck ce => exact Hr'
  cases p with
  | self a =>
    intro H
    exact (H _ List.mem_cons_self).elim
  | appendAck t e =>
    intro ⟨Hh, Hr⟩
    exact ⟨Hh, fun s' Hc => Hrest s' Hc Hr⟩
  | applyAck ce =>
    intro H
    exact ⟨H _ List.mem_cons_self, fun s' Hc =>
      Hrest s' Hc (fun q Hq => H q (List.mem_cons_of_mem _ Hq))⟩

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

/-- One pending message through `Step`'s spec. -/
private theorem wp_step_pending
    (wp_raft_Step : raft.Step.spec (GF := GF) (hG := hG))
    (cfg : GSet w64) (γ : RaftNames) (r : Loc) (id : w64) (s : NState)
    (ps : PState) (m : raftpb.Message) (p : Pending)
    (Hcfg : γ.reCfg = cfg) (Hin : id ∈ cfg) (Hrel : NStateRel s ps) (Hok : PendingOk s p) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhys cfg r id s ∗
        ownRaftGhost γ id ps ∗ pendingRel id m p ∗ pendingOwn m p }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #m))
    {{ (err : GoInterface) (s' : NState) (ps' : PState), RET #err;
        ownRaftPhys cfg r id s' ∗ ownRaftGhost γ id ps' ∗
        ⌜NStateRel s' ps' ∧ ∃ recv, Step cfg id ps recv ps'⌝ }} := by
  iintro %Φ ⟨#Hinit, Hphys, Hghost, #Hp, Hown⟩ HΦ
  cases p with
  | self a => exact Hok.elim
  | appendAck t e =>
    unfold pendingRel
    icases Hp with %Hm
    subst Hm
    obtain ⟨Hle, Hst⟩ := Hok
    iapply wp_raft_Step cfg γ r id s ps (appendAckMsg id t e) [] [] Hcfg
      (by simp [StepMsg, stepMsgTypes, appendAckMsg]) Hin
      (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne)
      (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne)
      (fun _ => ⟨rfl, Hle, Hst⟩) (by msg_ne) Hrel $$ [$Hinit $Hphys $Hghost]
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
      iintro %err %s' %ps' ⟨Hphys, Hghost, %Hrel', %Hstp, -⟩
      iapply HΦ $$ %err %s' %ps'
      iframe Hphys Hghost
      ipureintro
      exact ⟨Hrel', Hstp⟩
  | applyAck ce =>
    unfold pendingRel
    icases Hp with ⟨%sl, %Hm, #Hsl⟩
    subst Hm
    unfold pendingOwn
    iapply wp_raft_Step cfg γ r id s ps (applyAckMsg id sl) ce [] Hcfg
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
        · ipureintro; intro _; exact Hok
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
      iintro %err %s' %ps' ⟨Hphys, Hghost, %Hrel', %Hstp, -⟩
      iapply HΦ $$ %err %s' %ps'
      iframe Hphys Hghost
      ipureintro
      exact ⟨Hrel', Hstp⟩

theorem RawNode.Advance.wp_proof
    (wp_raft_Step : raft.Step.spec (GF := GF) (hG := hG)) :
    RawNode.Advance.spec (GF := GF) (hG := hG) := by
  intro cfg γ rn id s ps rs rd Hcfg Hin Hrel Hmono Hok
  wp_start as H
  iNamed H
  iNamed Hrn
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
      "Hphys" ∷ ownRaftPhys cfg rnv.raft' id s1 ∗ "Hghost" ∷ ownRaftGhost γ id ps1 ∗
      "Hsteps" ∷ rnv.stepsOnAdvance' ↦* steps1 ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (steps.length : Int)⌝ ∗
      "%Hsteps1" ∷ ⌜steps1.length = steps.length ∧
                    steps1.drop (sint.nat n) = steps.drop (sint.nat n)⌝ ∗
      "%Hrel1" ∷ ⌜NStateRel s1 ps1 ∧ ∃ recv, Step cfg id ps recv ps1⌝ ∗
      "%Hok1" ∷ ⌜AdvanceOk s1 (rs.steps.drop (sint.nat n))⌝ ∗
      "Hpown" ∷ ([∗list] _k ↦ m;p ∈ steps.drop (sint.nat n);rs.steps.drop (sint.nat n),
                   pendingOwn m p))
    $$ [i m ib Hphys Hghost Hsteps Hpown]
  · iexists W64 0, s, ps, steps, zero_val raftpb.Message, zero_val w64
    have H0 : sint.nat (W64 0) = 0 := rfl
    rw [H0, List.drop_zero, List.drop_zero]
    simp only [named]
    iframe
    ipureintro
    exact ⟨by word, ⟨trivial, trivial⟩, ⟨Hrel, [], Step.refl _⟩, Hok⟩
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
    obtain ⟨Hpok, Hrest⟩ := advanceOk_cons _ _ _ Hok1
    obtain ⟨Hrel1, recv1, Hst1⟩ := Hrel1
    wp_apply wp_step_pending wp_raft_Step cfg γ rnv.raft' id s1 ps1 mm p Hcfg Hin
      Hrel1 Hpok $$ [$Hphys $Hghost $Hpm $Hpo] as %err %s2 %ps2 ⟨Hphys, Hghost, %Hst2⟩
    obtain ⟨Hrel2, recv2, Hst2⟩ := Hst2
    -- `stepsOnAdvance[i] = pb.Message{}`
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hn.1, Hlt⟩)]
    wp_apply wp_store_slice_index rnv.stepsOnAdvance' (sint.Z n) steps1 (zero_val raftpb.Message)
      $$ [Hsteps] with Hsteps
    · iframe
      ipureintro
      constructor <;> word
    wp_for_post
    have Hc12 : uint.Z s1.logst.committed ≤ uint.Z s2.logst.committed := by
      have H := Hmono _ _ _ Hst2
      rw [← Hrel1.1, ← Hrel2.1] at H
      exact H
    iframe
    iexists n + W64 1, s2, ps2, steps1.set (sint.Z n).toNat (zero_val raftpb.Message), mm, n
    iframe
    ipureintro
    refine ⟨by word, ⟨by rw [List.length_set]; exact Hsteps1.1, ?_⟩,
      ⟨Hrel2, recv1 ++ recv2, Step.trans _ _ _ _ _ Hst1 Hst2⟩, Hrest s2 Hc12⟩
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
    iframe Hghost
    isplitl
    · unfold ownRawNode
      iexists _, sv, []
      simp only [named]
      iframe Hrn Hphys Hsoft Hsl0 Hcap0
      isplitr
      · ipureintro; exact Hasync
      isplitr
      · ipureintro; exact Hsoftv
      isplitr
      · ipureintro; exact Hhard
      isplitr <;> iempintro
    · ipureintro; exact Hrel1

end proof

end EtcdGrove
end Perennial
