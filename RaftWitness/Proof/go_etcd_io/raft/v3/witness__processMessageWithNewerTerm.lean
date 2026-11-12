/-
Proof of `Spec/go_etcd_io/raft/v3/witness__processMessageWithNewerTerm.lean`.
-/
module

public import RaftWitness.Spec.go_etcd_io.raft.v3.witness__processMessageWithNewerTerm

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

set_option hygiene false in
/-- `whsOwn q st'` from its pieces, the term, vote and lead cells given. -/
local macro "reseal_whsOwn" : tactic => `(tactic| (
  unfold whsOwn
  iexists ps
  iframe HS
  isplitl [HT HV HC]
  · unfold hsF
    iexists _, _, _, _
    isplitr
    · ipureintro; exact Hsn
    iframe HT cT HV cV HC cC Hpbs
  unfold whsRest
  iexists pli, plt, pls, _, srs, sro, _
  isplitr
  · ipureintro; exact Hnn
  iframe HLi cLi HLt cLt HLs cLs HLd cLd HRs Hrs HRo Hro Hpb))

/-- A pre-vote changes nothing; else fresh cells for the term (the request's), the vote (none)
and the leader (the sender of a leader's message, none for others). -/
theorem witness.processMessageWithNewerTerm.wp_proof :
    witness.processMessageWithNewerTerm.spec (GF := GF) (hG := hG) := by
  intro w mv μ q st
  wp_start as ⟨#Hm, Hq⟩
  iunfold ownWMsg at Hm
  icases Hm with ⟨%s0, %s1, %Hmv, -, -, -, -⟩
  obtain ⟨Hty, Hfr, Hto, Hte, Hlt, Hls, Hli, Hrs⟩ := Hmv
  iunfold whsOwn at Hq
  iNamed Hq
  iunfold hsF at Hhs
  iNamed Hhs
  iunfold whsRest at Hr
  iNamed Hr
  iapply wp_fupd
  wp_auto
  by_cases hpv : mv.Type' = W32 17
  · -- a pre-vote: nothing
    rw [show decide (true = decide (mv.Type' = W32 17)) = true by simp [hpv]]
    wp_auto
    have hw : wNewer st μ = st := by
      unfold wNewer; rw [if_pos (show μ.ty = MsgPreVote by rw [← Hty]; exact hpv)]
    rw [hw]
    imodintro
    iapply HΦ
    reseal_whsOwn
  rw [show decide (true = decide (mv.Type' = W32 17)) = false by rw [decide_eq_false hpv]; rfl]
  wp_auto
  -- `m.Type == MsgApp || m.Type == MsgHeartbeat || m.Type == MsgSnap`
  wp_bind (If (If _ (Val #true) _) (Val #true) _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = #(decide (mv.Type' = W32 3 ∨ mv.Type' = W32 8 ∨
      mv.Type' = W32 7))⌝ ∗ m_ptr ↦ mv))) $$ [m]
  · try wp_auto
    try rw [show raftpb.MsgApp = #((W32 3 : raftpb.MessageType)) from rfl]
    by_cases h3 : mv.Type' = W32 3
    · rw [decide_eq_true h3]
      wp_auto
      iframe m
      ipureintro; simp [h3]
    rw [decide_eq_false h3]
    wp_auto
    try rw [show raftpb.MsgHeartbeat = #((W32 8 : raftpb.MessageType)) from rfl]
    by_cases h8 : mv.Type' = W32 8
    · rw [decide_eq_true h8]
      wp_auto
      iframe m
      ipureintro; simp [h8]
    rw [decide_eq_false h8]
    wp_auto
    try rw [show raftpb.MsgSnap = #((W32 7 : raftpb.MessageType)) from rfl]
    iframe m
    ipureintro
    congr 1
    exact decide_eq_decide.2 ⟨fun h => Or.inr (Or.inr h),
      fun h => h.elim (fun h' => absurd h' h3) (fun h' => h'.elim (fun h'' => absurd h'' h8) id)⟩
  iintro %v ⟨%Hv, m⟩
  subst Hv
  wp_if_destruct
  · -- a leader's message: its term, no vote, its sender the leader
    have hl := Hif
    have hw : wNewer st μ = { st with term := μ.term, vote := W64 0, lead := μ.frm } := by
      unfold wNewer
      rw [if_neg (show ¬ μ.ty = MsgPreVote by rw [← Hty]; exact hpv),
        if_pos (show μ.ty = MsgApp ∨ μ.ty = MsgHeartbeat ∨ μ.ty = MsgSnap by rw [← Hty]; exact hl)]
    rw [hw]
    simp only [None']
    wp_auto
    rename_i pte pvo
    irename : (pte ↦ mv.Term' : IProp GF) => Ht
    irename : (pvo ↦ W64 0 : IProp GF) => Hv0
    iclear cT cV cLd
    imod cellRO_alloc $$ Ht with #cT
    imod cellRO_alloc $$ Hv0 with #cV
    imod cellRO_alloc $$ «$r0» with #cLd
    rw [← Hte, ← Hfr]
    imodintro
    iapply HΦ
    reseal_whsOwn
  · -- another: its term, no vote, no leader
    have hl := Hif
    have hw : wNewer st μ = { st with term := μ.term, vote := W64 0, lead := W64 0 } := by
      unfold wNewer
      rw [if_neg (show ¬ μ.ty = MsgPreVote by rw [← Hty]; exact hpv),
        if_neg (show ¬ (μ.ty = MsgApp ∨ μ.ty = MsgHeartbeat ∨ μ.ty = MsgSnap) by rw [← Hty]; exact hl)]
    rw [hw]
    simp only [None']
    wp_auto
    rename_i pte pvo
    irename : (pte ↦ mv.Term' : IProp GF) => Ht
    irename : (pvo ↦ W64 0 : IProp GF) => Hv0
    iclear cT cV cLd
    imod cellRO_alloc $$ Ht with #cT
    imod cellRO_alloc $$ Hv0 with #cV
    imod cellRO_alloc $$ «$r0» with #cLd
    rw [← Hte]
    imodintro
    iapply HΦ
    reseal_whsOwn

end proof

end EtcdGrove
end Perennial
