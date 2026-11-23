/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): the proof of `State.UpToDate`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__UpToDate
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__LastTerm
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
theorem State.UpToDate_logsRO_at (sl : GoSlice) (ls : List (List Entry)) (k : w64)
    (hk : 0 ≤ sint.Z k ∧ sint.Z k < ls.length) :
    logsRO (GF := GF) sl ls ⊢ ∃ v : GoSlice, sliceAt sl k v ∗ logRO v ls[sint.nat k]! := by
  iintro #H
  iunfold logsRO at H
  icases H with ⟨%gs, #Hgs, #Hb⟩
  iapply sliceRO_at (fun g l => logRO (GF := GF) g l) sl gs ls k hk
  iframe Hgs Hb

/-- A log's length. -/
theorem State.UpToDate_logRO_len (sl : GoSlice) (l : List Entry) :
    logRO (GF := GF) sl l ⊢ ⌜sint.Z sl.len = (l.length : Int)⌝ := by
  iintro #H
  iunfold logRO at H
  icases H with ⟨%es, #Hes, #Hle⟩
  ihave %Hel := ownSlice_len $$ Hes
  ihave %Hll := BigSepL2.bigSepL2_length $$ Hle
  ipureintro
  rw [← Hll, Hel.1]; word

theorem State.UpToDate.wp_proof (wp_LastTerm : State.LastTerm.spec (GF := GF) (hG := hG)) :
    State.UpToDate.spec (GF := GF) (hG := hG) := by
  intro p s gm m i
  wp_start as ⟨#Hs, %Hm, %Hi0, %Hi1⟩
  ihave #Hs' := Hs
  iunfold stateRO at Hs'
  iNamed Hs'
  iNamed Hf
  iStructNamed Hp
  icases State.UpToDate_logsRO_at g.Log' s.log i ⟨Hi0, by rw [HWf.len_log]; exact Hi1⟩ $$ HLog with ⟨%v, #Hva, #Hv⟩
  ihave %Hvl := State.UpToDate_logRO_len v _ $$ Hv
  obtain ⟨_, _, _, _, Hli, Hlt, _⟩ := Hm
  wp_auto
  wp_apply wp_LastTerm p s i $$ [Hs] as %w %Hw
  · iframe Hs; ipureintro; exact ⟨Hi0, Hi1⟩
  try wp_auto
  wp_if_destruct
  · try wp_auto
    have : s.upToDate m (sint.nat i) = true := by
      unfold State.upToDate; simp only [Bool.or_eq_true, decide_eq_true_eq]; left; omega
    rw [this]
    iapply HΦ; ipureintro; trivial
  · wp_apply wp_LastTerm p s i $$ [Hs] as %w' %Hw'
    · iframe Hs; ipureintro; exact ⟨Hi0, Hi1⟩
    have hww : w' = w := by have := Hw'.trans Hw.symm; word
    subst hww
    try wp_auto
    wp_if_destruct
    · wp_apply wp_load_at _ _ v Hi0 $$ [Hva]
      · iexact Hva
      try wp_auto
      have : decide (sint.Z v.len ≤ sint.Z gm.LastLogIndex') = s.upToDate m (sint.nat i) := by
        unfold State.upToDate
        have : m.lastLogTerm = s.lastTerm (sint.nat i) := by rw [← Hlt, ← Hw']
        rw [this]
        simp
        rw [List.getElem!_eq_getElem?_getD] at Hvl
        omega
      rw [this]
      iapply HΦ; ipureintro; trivial
    · try wp_auto
      have : s.upToDate m (sint.nat i) = false := by
        unfold State.upToDate
        have h1 : m.lastLogTerm ≠ s.lastTerm (sint.nat i) := by
          rw [← Hlt, ← Hw']; intro h; apply Hif; word
        simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, Bool.and_eq_false_iff, beq_eq_false_iff_ne]
        exact ⟨by omega, Or.inl h1⟩
      rw [this]
      iapply HΦ; ipureintro; trivial

end proof

end AntCheck
end EtcdGrove
end Perennial
