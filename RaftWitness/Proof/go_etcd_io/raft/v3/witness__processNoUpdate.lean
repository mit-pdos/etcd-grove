/-
Proof of `Spec/go_etcd_io/raft/v3/witness__processNoUpdate.lean`.
-/
module

public import RaftWitness.Spec.go_etcd_io.raft.v3.witness__processNoUpdate
public import RaftWitness.Spec.go_etcd_io.raft.v3.witness__isHealthy
public import RaftWitness.Spec.go_etcd_io.raft.v3.witness__processMessageWithOlderTerm
public import RaftWitness.Spec.go_etcd_io.raft.v3.witness__handleAppendNoUpdate
public import RaftWitness.Proof.go_etcd_io.raft.v3.LemmasWitness

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

/-- `wNoUpdate`'s three tests in order: an unhealthy heartbeat, an older term, an append of the
cache's term. -/
theorem witness.processNoUpdate.wp_proof
    (wp_isHealthy : witness.isHealthy.spec (GF := GF) (hG := hG))
    (wp_processMessageWithOlderTerm : witness.processMessageWithOlderTerm.spec (GF := GF) (hG := hG))
    (wp_handleAppendNoUpdate : witness.handleAppendNoUpdate.spec (GF := GF) (hG := hG))
    (wp_GetState : raftpb.WitnessHardState.GetState.spec (GF := GF) (hG := hG))
    (wp_GetTerm : raftpb.HardState.GetTerm.spec (GF := GF) (hG := hG)) :
    witness.processNoUpdate.spec (GF := GF) (hG := hG) := by
  intro w id cq pv dq dq' p σ e mv μ
  wp_start as ⟨#Hid, #Hcq, #Hpv, Hst, #Hp, He, #Hm⟩
  ihave #Hm' := Hm
  iunfold ownWMsg at Hm'
  icases Hm' with ⟨%s0, %s1, %Hmv, -, -, -, -⟩
  obtain ⟨Hty, Hfr, Hto, Hte, Hlt, Hls, Hli, Hrs⟩ := Hmv
  wp_auto
  wp_apply wp_isHealthy w dq' e $$ [$He] as He
  -- `!w.isHealthy() && m.Type == MsgHeartbeat`: no answer
  by_cases hu : (!decide (e = interface.nil) && decide (μ.ty = MsgHeartbeat)) = true
  · have hw : wNoUpdate id cq pv (decide (e = interface.nil)) σ μ = some none := by
      unfold wNoUpdate; rw [if_pos hu]
    rw [hw]
    have he : e ≠ interface.nil := by
      intro h; simp [h] at hu
    have ht : μ.ty = MsgHeartbeat := by simp at hu; exact hu.2
    rw [decide_eq_false he]
    wp_auto
    try rw [Hty]
    try rw [show raftpb.MsgHeartbeat = #((W32 8 : raftpb.MessageType)) from rfl]
    rw [decide_eq_true (show μ.ty = W32 8 from ht)]
    wp_auto
    iapply HΦ
    iframe Hst He
    iframe
    unfold respOpt
    ipureintro; exact ⟨rfl, rfl⟩
  wp_bind (If (Val #(!decide (e = interface.nil))) _ (Val #false))
  iapply (wp_wand (Φ := fun v => iprop(⌜v = #false⌝ ∗ m_ptr ↦ mv))) $$ [m]
  · by_cases he : e = interface.nil
    · rw [decide_eq_true he]
      wp_auto
      iframe m
      ipureintro; rfl
    · rw [decide_eq_false he]
      wp_auto
      try rw [Hty]
      try rw [show raftpb.MsgHeartbeat = #((W32 8 : raftpb.MessageType)) from rfl]
      have ht : ¬ μ.ty = W32 8 := fun h => hu (by simp [he, h, MsgHeartbeat])
      rw [decide_eq_false ht]
      iframe m
      ipureintro; rfl
  iintro %v ⟨%Hv, m⟩
  subst Hv
  wp_auto
  -- `m.Term < w.state.GetState().GetTerm()`: `processMessageWithOlderTerm`'s answer
  wp_apply wp_whsOpt_GetState wp_GetState p σ $$ [$Hp] as %ps #Hhs
  wp_apply wp_hsOptW_GetTerm wp_GetTerm ps _ σ $$ [$Hhs] as -
  try wp_auto
  rw [Hte]
  by_cases hlt : uint.Z μ.term < uint.Z σ.term
  · rw [decide_eq_true hlt]
    have hw : wNoUpdate id cq pv (decide (e = interface.nil)) σ μ = some (wOlder id cq pv σ μ) := by
      unfold wNoUpdate; rw [if_neg hu, if_pos hlt]
    rw [hw]
    wp_auto
    wp_apply wp_processMessageWithOlderTerm w id cq pv dq p σ mv μ $$ [$Hid $Hcq $Hpv $Hst $Hp $Hm]
      as %ml ⟨Hst, Hr⟩
    iapply HΦ
    simp only
    iframe Hst He Hr
  rw [decide_eq_false hlt]
  wp_auto
  -- `m.Term == w.state.GetState().GetTerm()` and an append: `handleAppendNoUpdate`'s
  wp_apply wp_whsOpt_GetState wp_GetState p σ $$ [$Hp] as %ps' #Hhs'
  wp_apply wp_hsOptW_GetTerm wp_GetTerm ps' _ σ $$ [$Hhs'] as -
  try wp_auto
  rw [Hte]
  by_cases heq : μ.term = σ.term
  · rw [decide_eq_true heq]
    wp_auto
    try rw [Hty]
    try rw [show raftpb.MsgApp = #((W32 3 : raftpb.MessageType)) from rfl]
    by_cases hap : μ.ty = W32 3
    · rw [decide_eq_true hap]
      wp_auto
      wp_apply wp_handleAppendNoUpdate w id dq p σ mv μ $$ [$Hid $Hst $Hp $Hm] as %ml ⟨Hst, Hr⟩
      iapply HΦ
      iframe Hst He
      have hc : μ.term = σ.term ∧ μ.ty = MsgApp := ⟨heq, hap⟩
      unfold wNoUpdate
      rw [if_neg hu, if_neg hlt, if_pos hc]
      cases hr : (wAppendNoUpdate id σ μ).2
      · simp only [hr, Bool.false_eq_true, ↓reduceIte]
        ipureintro; trivial
      · simp only [hr, ↓reduceIte]
        isplitr
        · ipureintro; trivial
        unfold respOpt
        iexact Hr
    · rw [decide_eq_false hap]
      wp_auto
      iapply HΦ
      iframe Hst He
      have hc : ¬ (μ.term = σ.term ∧ μ.ty = MsgApp) := fun h => hap h.2
      unfold wNoUpdate
      rw [if_neg hu, if_neg hlt, if_neg hc]
      ipureintro; rfl
  · rw [decide_eq_false heq]
    wp_auto
    iapply HΦ
    iframe Hst He
    have hc : ¬ (μ.term = σ.term ∧ μ.ty = MsgApp) := fun h => heq h.1
    unfold wNoUpdate
    rw [if_neg hu, if_neg hlt, if_neg hc]
    ipureintro; rfl

end proof

end EtcdGrove
end Perennial
