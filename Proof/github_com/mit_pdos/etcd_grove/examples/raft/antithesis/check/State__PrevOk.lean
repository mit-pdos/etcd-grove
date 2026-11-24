/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): the proof of `State.PrevOk`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__PrevOk
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.At
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.StateLaws

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

/-- `s.Log[k]`. -/
theorem State.PrevOk_logsRO_at (sl : GoSlice) (ls : List (List Entry)) (k : w64)
    (hk : 0 ≤ sint.Z k ∧ sint.Z k < ls.length) :
    logsRO (GF := GF) sl ls ⊢ ∃ v : GoSlice, sliceAt sl k v ∗ logRO v ls[sint.nat k]! := by
  iintro #H
  iunfold logsRO at H
  icases H with ⟨%gs, #Hgs, #Hb⟩
  iapply sliceRO_at (fun g l => logRO (GF := GF) g l) sl gs ls k hk
  iframe Hgs Hb

/-- A log's length. -/
theorem State.PrevOk_logRO_len (sl : GoSlice) (l : List Entry) :
    logRO (GF := GF) sl l ⊢ ⌜sint.Z sl.len = (l.length : Int)⌝ := by
  iintro #H
  iunfold logRO at H
  icases H with ⟨%es, #Hes, #Hle⟩
  ihave %Hel := ownSlice_len $$ Hes
  ihave %Hll := BigSepL2.bigSepL2_length $$ Hle
  ipureintro
  rw [← Hll, Hel.1]; word

theorem State.PrevOk.wp_proof (wp_At : At.spec (GF := GF) (hG := hG)) :
    State.PrevOk.spec (GF := GF) (hG := hG) := by
  intro p s j gm m b
  wp_start as ⟨#Hs, #Hm, %Hj0, %Hj1, %Hb⟩
  ihave #Hs' := Hs
  iunfold stateRO at Hs'
  iNamed Hs'
  iNamed Hf
  iStructNamed Hp
  icases State.PrevOk_logsRO_at g.Log' s.log j ⟨Hj0, by rw [HWf.len_log]; exact Hj1⟩ $$ HLog with ⟨%v, #Hva, #Hv⟩
  ihave %Hvl := State.PrevOk_logRO_len v _ $$ Hv
  iunfold appendFactRO at Hm
  icases Hm with ⟨%Hmf, -⟩
  obtain ⟨_, _, _, Hpi, Hpt, _⟩ := Hmf
  unfold State.prevOk at Hb
  wp_auto
  wp_if_destruct
  · try wp_auto
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by rw [← Hpi, Hif]; rfl))] at Hb
    cases Except.ok.inj Hb
    iapply HΦ; ipureintro; trivial
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (by
      rw [← Hpi, beq_iff_eq]; intro h; apply Hif; word))] at Hb
    wp_apply wp_load_at _ _ v Hj0 $$ [Hva]
    · iexact Hva
    try wp_auto
    wp_if_destruct
    · rw [ite_eq_left_of_eq_true _ _ (eq_true (by rw [← Hpi, ← Hvl]; exact Hif))] at Hb
      cases hx : atE s.log[sint.nat j]! m.prevLogIndex with
      | error _ => rw [hx] at Hb; cases Hb
      | ok x =>
      rw [hx] at Hb
      wp_apply wp_load_at _ _ v Hj0 $$ [Hva]
      · iexact Hva
      try wp_auto
      wp_apply wp_At v _ gm.PrevLogIndex' x $$ [Hv] as %e #He
      · iframe Hv; ipureintro; rw [Hpi]; exact hx
      iunfold entryRO at He
      icases He with ⟨%Hex, -⟩
      try wp_auto
      have : decide (e.Term' = gm.PrevLogTerm') = b := by
        rw [← Except.ok.inj Hb]
        by_cases h : e.Term' = gm.PrevLogTerm'
        · rw [decide_eq_true h]; symm; rw [beq_iff_eq, ← Hex.1, ← Hpt, h]
        · rw [decide_eq_false h]; symm; rw [beq_eq_false_iff_ne, ← Hex.1, ← Hpt]; intro h'; apply h; word
      rw [this]
      iapply HΦ; ipureintro; trivial
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (by rw [← Hpi, ← Hvl]; exact Hif))] at Hb
      cases Except.ok.inj Hb
      iapply HΦ; ipureintro; trivial

end proof

end AntCheck
end EtcdGrove
end Perennial
