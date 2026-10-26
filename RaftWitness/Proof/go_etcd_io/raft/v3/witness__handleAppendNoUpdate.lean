/-
Proof of `Spec/go_etcd_io/raft/v3/witness__handleAppendNoUpdate.lean`.
-/
module

public import RaftWitness.Spec.go_etcd_io.raft.v3.witness__handleAppendNoUpdate
public import RaftWitness.Spec.go_etcd_io.raft.v3.raftpb.MessageType__Enum
public import RaftWitness.Proof.go_etcd_io.raft.v3.LemmasWitness
public import RaftWitness.Proof.go_etcd_io.raft.v3.LemmasSendR

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

/-- The answer built first (its cells fresh), then its `Index` set in the two handled cases. -/
theorem witness.handleAppendNoUpdate.wp_proof
    (wp_MessageType_Enum : raftpb.MessageType.Enum.spec (GF := GF) (hG := hG))
    (wp_GetState : raftpb.WitnessHardState.GetState.spec (GF := GF) (hG := hG))
    (wp_GetTerm : raftpb.HardState.GetTerm.spec (GF := GF) (hG := hG))
    (wp_GetLastLogIndex : raftpb.WitnessHardState.GetLastLogIndex.spec (GF := GF) (hG := hG))
    (wp_GetLastLogTerm : raftpb.WitnessHardState.GetLastLogTerm.spec (GF := GF) (hG := hG))
    (wp_GetLastLogSubterm : raftpb.WitnessHardState.GetLastLogSubterm.spec (GF := GF) (hG := hG)) :
    witness.handleAppendNoUpdate.spec (GF := GF) (hG := hG) := by
  intro w id dq p σ mv μ
  wp_start as ⟨#Hid, Hst, #Hp, #Hm⟩
  iunfold ownWMsg at Hm
  icases Hm with ⟨%s0, %s1, %Hmv, #Hs0, #Hs1, #Hvot, #Hctx⟩
  obtain ⟨Hty, Hfr, Hto, Hte, Hlt, Hls, Hli, Hrs⟩ := Hmv
  wp_auto
  rw [show raftpb.MsgAppResp = #((W32 4 : raftpb.MessageType)) from rfl]
  haveI : go.NotInterface go.int32 := ⟨by unfold go.int32; trivial⟩
  wp_apply wp_MessageType_Enum (W32 4) as %pty Hpty
  imod cellRO_alloc $$ Hpty with #cTy
  wp_apply wp_whsOpt_GetState wp_GetState p σ $$ [$Hp] as %ps #Hhs
  wp_apply wp_hsOptW_GetTerm wp_GetTerm ps _ σ $$ [$Hhs] as -
  imod cellRO_alloc $$ «$v1» with #cTo
  imod cellRO_alloc $$ «$v2» with #cFr
  imod cellRO_alloc $$ «$v3» with #cTe
  wp_apply wp_whsOpt_GetLastLogTerm wp_GetLastLogTerm p σ $$ [$Hp]
  -- `m.LastLogTerm == w.state.GetLastLogTerm() && m.LastLogSubterm == w.state.GetLastLogSubterm()`
  rw [Hlt]
  wp_bind (If (Val #(decide (μ.lt = σ.lt))) _ _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = #(decide (μ.lt = σ.lt ∧ μ.ls = σ.ls))⌝ ∗
      w.[witness, go!"state"] ↦{dq} p ∗ m_ptr ↦ mv ∗ w_ptr ↦ w))) $$ [Hst m w]
  · by_cases h : μ.lt = σ.lt
    · rw [decide_eq_true h]
      wp_auto
      wp_apply wp_whsOpt_GetLastLogSubterm wp_GetLastLogSubterm p σ $$ [$Hp]
      try wp_auto
      rw [Hls]
      iframe Hst m w
      ipureintro
      by_cases h' : μ.ls = σ.ls
      · rw [decide_eq_true h', decide_eq_true ⟨h, h'⟩]
      · rw [decide_eq_false h', decide_eq_false (fun hh => h' hh.2)]
    · rw [decide_eq_false h]
      wp_auto
      iframe Hst m w
      ipureintro
      rw [decide_eq_false (fun hh => h hh.1)]
  iintro %v ⟨%Hv, Hst, m, w⟩
  subst Hv
  iapply wp_fupd
  wp_if_destruct
  · -- the stored `(term, subterm)`: `resp.Index = new(m.LastLogIndex)`
    have h1 := Hif
    have hw : wAppendNoUpdate id σ μ =
        ((respM MsgAppResp μ.frm id σ.term μ.li false, []), true) := by
      simp only [wAppendNoUpdate, if_pos h1]
    rw [hw]
    rename_i mlp
    irename : («$r0_ptr» ↦ mv.LastLogIndex' : IProp GF) => Hix
    imod cellRO_alloc $$ Hix with #cIx
    imod msgOwn_lit mlp _ (respM MsgAppResp μ.frm id σ.term μ.li false) [] ⊤ $$ [«$r0»] with Hmsg
    · simp only [respM, show MsgAppResp = W32 4 from rfl, ← Hfr, ← Hli]
      ihave #Hnilb := ownSlice_nil (V := w8) (GF := GF) DFrac.discard
      iframe «$r0» Hnilb cTy cTo cFr cTe cIx
      isplitr
      · ipureintro; exact ⟨rfl, rfl, rfl, rfl⟩
      msg_nulls
    imodintro
    iapply HΦ
    iframe Hst Hmsg
  have h1 := Hif
  -- `m.LastLogTerm < w.state.GetLastLogTerm() || (== && m.LastLogSubterm < ...)`
  wp_bind (If _ (Val #true) _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = #(decide (ltPair μ.lt μ.ls σ.lt σ.ls))⌝ ∗
      w.[witness, go!"state"] ↦{dq} p ∗ m_ptr ↦ mv ∗ w_ptr ↦ w))) $$ [Hst m w]
  · wp_apply wp_whsOpt_GetLastLogTerm wp_GetLastLogTerm p σ $$ [$Hp]
    try wp_auto
    rw [Hlt]
    by_cases hlt : uint.Z μ.lt < uint.Z σ.lt
    · rw [decide_eq_true hlt]
      wp_auto
      iframe Hst m w
      ipureintro
      rw [show decide (ltPair μ.lt μ.ls σ.lt σ.ls) = true from decide_eq_true (Or.inl hlt)]
    · rw [decide_eq_false hlt]
      wp_auto
      wp_apply wp_whsOpt_GetLastLogTerm wp_GetLastLogTerm p σ $$ [$Hp]
      try wp_auto
      rw [Hlt]
      by_cases heq : μ.lt = σ.lt
      · rw [decide_eq_true heq]
        wp_auto
        wp_apply wp_whsOpt_GetLastLogSubterm wp_GetLastLogSubterm p σ $$ [$Hp]
        try wp_auto
        rw [Hls]
        iframe Hst m w
        ipureintro
        by_cases hls : uint.Z μ.ls < uint.Z σ.ls
        · rw [decide_eq_true hls,
            show decide (ltPair μ.lt μ.ls σ.lt σ.ls) = true from decide_eq_true (Or.inr ⟨heq, hls⟩)]
        · rw [decide_eq_false hls]
          rw [show decide (ltPair μ.lt μ.ls σ.lt σ.ls) = false from decide_eq_false (by
            rintro (h | ⟨-, h⟩) <;> contradiction)]
      · rw [decide_eq_false heq]
        wp_auto
        iframe Hst m w
        ipureintro
        rw [show decide (ltPair μ.lt μ.ls σ.lt σ.ls) = false from decide_eq_false (by
          rintro (h | ⟨h, -⟩) <;> contradiction)]
  iintro %v ⟨%Hv, Hst, m, w⟩
  subst Hv
  wp_if_destruct
  · -- below the stored pair: `resp.Index = new(w.state.GetLastLogIndex())`
    have h2 := Hif
    have hw : wAppendNoUpdate id σ μ =
        ((respM MsgAppResp μ.frm id σ.term σ.li false, []), true) := by
      simp only [wAppendNoUpdate, if_neg h1, if_pos h2]
    rw [hw]
    wp_apply wp_whsOpt_GetLastLogIndex wp_GetLastLogIndex p σ $$ [$Hp]
    try wp_auto
    irename : («$r0_ptr» ↦ σ.li : IProp GF) => Hix
    imod cellRO_alloc $$ Hix with #cIx
    imod msgOwn_lit _ _ (respM MsgAppResp μ.frm id σ.term σ.li false) [] ⊤ $$ [«$r0»] with Hmsg
    · simp only [respM, show MsgAppResp = W32 4 from rfl, ← Hfr]
      ihave #Hnilb := ownSlice_nil (V := w8) (GF := GF) DFrac.discard
      iframe «$r0» Hnilb cTy cTo cFr cTe cIx
      isplitr
      · ipureintro; exact ⟨rfl, rfl, rfl, rfl⟩
      msg_nulls
    imodintro
    iapply HΦ
    iframe Hst Hmsg
  · -- not handled: the state is to be written
    have h2 := Hif
    have hw : wAppendNoUpdate id σ μ =
        ((respM MsgAppResp μ.frm id σ.term (W64 0) false, []), false) := by
      simp only [wAppendNoUpdate, if_neg h1, if_neg h2]
    rw [hw]
    imod msgOwn_lit _ _ (respM MsgAppResp μ.frm id σ.term (W64 0) false) [] ⊤ $$ [«$r0»]
      with Hmsg
    · simp only [respM, show MsgAppResp = W32 4 from rfl, ← Hfr]
      ihave #Hnilb := ownSlice_nil (V := w8) (GF := GF) DFrac.discard
      iframe «$r0» Hnilb cTy cTo cFr cTe
      isplitr
      · ipureintro; exact ⟨rfl, rfl, rfl, rfl⟩
      msg_nulls
    imodintro
    iapply HΦ
    iframe Hst Hmsg

end proof

end EtcdGrove
end Perennial
