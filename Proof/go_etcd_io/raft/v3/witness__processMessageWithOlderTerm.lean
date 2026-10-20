/-
Proof of `Spec/go_etcd_io/raft/v3/witness__processMessageWithOlderTerm.lean`.
-/
module

public import Spec.go_etcd_io.raft.v3.witness__processMessageWithOlderTerm
public import Spec.go_etcd_io.raft.v3.raftpb.MessageType__Enum
public import Proof.go_etcd_io.raft.v3.LemmasWitness
public import Proof.go_etcd_io.raft.v3.LemmasSendR

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The condition evaluated to the model's, then each answer built (its cells fresh). -/
theorem witness.processMessageWithOlderTerm.wp_proof
    (wp_MessageType_Enum : raftpb.MessageType.Enum.spec (GF := GF) (hG := hG))
    (wp_GetState : raftpb.WitnessHardState.GetState.spec (GF := GF) (hG := hG))
    (wp_GetTerm : raftpb.HardState.GetTerm.spec (GF := GF) (hG := hG)) :
    witness.processMessageWithOlderTerm.spec (GF := GF) (hG := hG) := by
  intro w id cq pv dq p σ mv μ
  wp_start as ⟨#Hid, #Hcq, #Hpv, Hst, #Hp, #Hm⟩
  iunfold ownWMsg at Hm
  icases Hm with ⟨%s0, %s1, %Hmv, #Hs0, #Hs1, #Hvot, #Hctx⟩
  obtain ⟨Hty, Hfr, Hto, Hte, Hlt, Hls, Hli, Hrs⟩ := Hmv
  wp_auto
  -- `(w.checkQuorum || w.preVote) && (m.Type == MsgHeartbeat || m.Type == MsgApp)`
  wp_bind (If (If (Val #cq) (Val #true) _) _ (Val #false))
  iapply (wp_wand (Φ := fun v => iprop(⌜v = #((cq || pv) &&
      decide (mv.Type' = MsgHeartbeat ∨ mv.Type' = MsgApp))⌝ ∗ m_ptr ↦ mv ∗ w_ptr ↦ w))) $$ [m w]
  · cases cq
    · wp_auto
      cases pv
      · wp_auto
        iframe m w
        ipureintro; rfl
      · wp_auto
        try rw [Hty, show raftpb.MsgHeartbeat = #((W32 8 : raftpb.MessageType)) from rfl]
        by_cases h1 : mv.Type' = W32 8
        · rw [decide_eq_true h1]
          wp_auto
          iframe m w
          ipureintro; simp [h1, MsgHeartbeat]
        · rw [decide_eq_false h1]
          wp_auto
          try rw [Hty, show raftpb.MsgApp = #((W32 3 : raftpb.MessageType)) from rfl]
          iframe m w
          ipureintro
          simp only [Bool.false_or, Bool.true_or, Bool.true_and, MsgHeartbeat, MsgApp]
          congr 1
          exact decide_eq_decide.2 ⟨Or.inr, fun h => h.resolve_left h1⟩
    · wp_auto
      try rw [Hty, show raftpb.MsgHeartbeat = #((W32 8 : raftpb.MessageType)) from rfl]
      by_cases h1 : mv.Type' = W32 8
      · rw [decide_eq_true h1]
        wp_auto
        iframe m w
        ipureintro; simp [h1, MsgHeartbeat]
      · rw [decide_eq_false h1]
        wp_auto
        try rw [Hty, show raftpb.MsgApp = #((W32 3 : raftpb.MessageType)) from rfl]
        iframe m w
        ipureintro
        simp only [Bool.false_or, Bool.true_or, Bool.true_and, MsgHeartbeat, MsgApp]
        congr 1
        exact decide_eq_decide.2 ⟨Or.inr, fun h => h.resolve_left h1⟩
  iintro %v ⟨%Hv, m, w⟩
  subst Hv
  iapply wp_fupd
  generalize hb : ((cq || pv) && decide (mv.Type' = MsgHeartbeat ∨ mv.Type' = MsgApp)) = b
  cases b
  · -- not a stale leader's message
    wp_auto
    try rw [Hty, show raftpb.MsgPreVote = #((W32 17 : raftpb.MessageType)) from rfl]
    wp_if_destruct
    · -- a pre-vote: rejected at the newer term
      have h2 := Hif
      have hw : wOlder id cq pv σ μ =
          some (respM MsgPreVoteResp μ.frm (W64 0) σ.term (W64 0) true, []) := by
        unfold wOlder; rw [← Hty, hb]
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [if_pos (show mv.Type' = MsgPreVote from h2)]
      rw [hw]
      wp_apply wp_whsOpt_GetState wp_GetState p σ $$ [$Hp] as %ps #Hhs
      wp_apply wp_hsOptW_GetTerm wp_GetTerm ps _ σ $$ [$Hhs] as -
      rw [show raftpb.MsgPreVoteResp = #((W32 18 : raftpb.MessageType)) from rfl]
      haveI : go.NotInterface go.int32 := ⟨by unfold go.int32; trivial⟩
      wp_apply wp_MessageType_Enum (W32 18) as %pty Hpty
      imod cellRO_alloc $$ Hpty with #cTy
      imod cellRO_alloc $$ «$v0» with #cTo
      imod cellRO_alloc $$ «$v1» with #cTe
      imod cellRO_alloc $$ «$v3» with #cRj
      imod msgOwn_lit _ _ (respM MsgPreVoteResp μ.frm (W64 0) σ.term (W64 0) true) [] ⊤ $$ [«$r0»]
        with Hmsg
      · simp only [respM, show MsgPreVoteResp = W32 18 from rfl, ← Hfr]
        ihave #Hnilb := ownSlice_nil (V := w8) (GF := GF) DFrac.discard
        iframe «$r0» Hnilb cTy cTo cTe cRj
        isplitr
        · ipureintro; exact ⟨rfl, rfl, rfl, rfl⟩
        msg_nulls
      imodintro
      iapply HΦ
      iframe Hst
      unfold respOpt
      iexact Hmsg
    · -- none
      have h2 := Hif
      have hw : wOlder id cq pv σ μ = none := by
        unfold wOlder; rw [← Hty, hb]
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [if_neg (show ¬ mv.Type' = MsgPreVote from h2)]
      rw [hw]
      imodintro
      iapply HΦ
      iframe Hst
      unfold respOpt
      ipureintro; rfl
  · -- a stale leader's message: `MsgAppResp` at the newer term
    have hw : wOlder id cq pv σ μ = some (respM MsgAppResp μ.frm id σ.term (W64 0) false, []) := by
      unfold wOlder; rw [← Hty, hb]; simp
    rw [hw]
    wp_auto
    wp_apply wp_whsOpt_GetState wp_GetState p σ $$ [$Hp] as %ps #Hhs
    wp_apply wp_hsOptW_GetTerm wp_GetTerm ps _ σ $$ [$Hhs] as -
    rw [show raftpb.MsgAppResp = #((W32 4 : raftpb.MessageType)) from rfl]
    haveI : go.NotInterface go.int32 := ⟨by unfold go.int32; trivial⟩
    wp_apply wp_MessageType_Enum (W32 4) as %pty Hpty
    imod cellRO_alloc $$ Hpty with #cTy
    imod cellRO_alloc $$ «$v0» with #cTo
    imod cellRO_alloc $$ «$v1» with #cFr
    imod cellRO_alloc $$ «$v2» with #cTe
    imod msgOwn_lit _ _ (respM MsgAppResp μ.frm id σ.term (W64 0) false) [] ⊤ $$ [«$r0»] with Hmsg
    · simp only [respM, show MsgAppResp = W32 4 from rfl, ← Hfr]
      ihave #Hnilb := ownSlice_nil (V := w8) (GF := GF) DFrac.discard
      iframe «$r0» Hnilb cTy cTo cFr cTe
      isplitr
      · ipureintro; exact ⟨rfl, rfl, rfl, rfl⟩
      msg_nulls
    imodintro
    iapply HΦ
    iframe Hst
    unfold respOpt
    iexact Hmsg

end proof

end EtcdGrove
end Perennial
