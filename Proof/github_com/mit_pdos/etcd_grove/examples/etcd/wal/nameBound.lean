/- Lean-first (no Rocq counterpart). The proof of `nameBound`. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.nameBound
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.cutPos
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.lastIdx
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.RefLemmas

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.etcd.wal

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.wal.Assumptions]

theorem filter_range_succ_last (p : Nat → Bool) (n : Nat) :
    ((List.range (n + 1)).filter p).getLast?.getD 0 =
      if p n then n else ((List.range n).filter p).getLast?.getD 0 := by
  rw [List.range_succ, List.filter_append]
  cases hp : p n <;> simp [hp]

theorem filter_range_last_le (p : Nat → Bool) (n : Nat) :
    ((List.range n).filter p).getLast?.getD 0 ≤ n := by
  cases hg : ((List.range n).filter p).getLast? with
  | none => simp
  | some x =>
    have := List.mem_of_getLast? hg
    rw [List.mem_filter, List.mem_range] at this
    simp; omega

/-- `nameBound`'s `best` after the positions below `n`. -/
def nbBest (h : List TOp) (a : w64) (n : Nat) : w64 :=
  W64 (((List.range n).filter (fun b =>
    tCutPos h b && decide (uint.nat (tLastIdx (h.take b) + W64 1) ≤ uint.nat a))).getLast?.getD 0)

theorem nbBest_succ (h : List TOp) (a : w64) (n : Nat) :
    nbBest h a (n + 1) = if tCutPos h n && decide (uint.nat (tLastIdx (h.take n) + W64 1) ≤ uint.nat a)
      then W64 n else nbBest h a n := by
  unfold nbBest; rw [filter_range_succ_last]; split <;> rfl

theorem nameBound.wp_proof (wp_cutPos : cutPos.spec (GF := GF) (hG := hG))
    (wp_lastIdx : lastIdx.spec (GF := GF) (hG := hG)) :
    nameBound.spec (GF := GF) (hG := hG) := by
  intro s h a
  wp_start as #Hr
  ihave Hr2 := Hr
  iunfold opsRep at Hr2
  icases Hr2 with ⟨%es, #Hs, #Hel⟩
  ihave %Hlen := ownSlice_len $$ Hs
  ihave %Hwf := ownSlice_wf $$ Hs
  ihave %Hel_len := opsElems_length $$ Hel
  wp_auto
  ihave HI : (∃ (b : w64),
      "b" ∷ b_ptr ↦ b ∗
      "best" ∷ best_ptr ↦ nbBest h a (sint.nat b) ∗
      "h" ∷ h_ptr ↦ s ∗
      "%Hb" ∷ ⌜0 ≤ sint.Z b ∧ sint.Z b ≤ sint.Z s.len⌝ : IProp GF) $$ [b best h]
  · iexists W64 0
    rw [show sint.nat (W64 0) = 0 from rfl]
    iframe
    ipureintro; constructor <;> word
  wp_for HI
  have hbl : sint.nat b ≤ h.length := by
    have : sint.nat b ≤ sint.nat s.len := by word
    omega
  wp_join iprop(best_ptr ↦ nbBest h a (sint.nat b + 1) ∗ h_ptr ↦ s ∗ b_ptr ↦ b ∗ a_ptr ↦ a)
    at next with [best h b a] as ⟨best, h, b, a⟩
  · wp_apply wp_cutPos s h b Hb.1 hbl
    · iexact Hr
    cases hc : tCutPos h (sint.nat b)
    · wp_auto
      rw [nbBest_succ]
      simp only [hc, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      wp_join_done
    · wp_auto
      have hb2 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z b ∧ sint.Z b ≤ sint.Z s.cap :=
        ⟨by word, Hb.1, by omega⟩
      simp only [hb2, _root_.and_self, ↓reduceIte]
      ihave Hpre := opsRep_slice s h (W64 0) b ⟨by word, Hb.1, Hb.2⟩ $$ Hr
      have hpre : subslice (sint.nat (W64 0)) (sint.nat b) h = h.take (sint.nat b) := by
        rw [show sint.nat (W64 0) = 0 from rfl]; simp [subslice]
      rw [hpre]
      wp_apply wp_lastIdx
      · iexact Hpre
      iintro -
      wp_auto
      wp_if_destruct
      · rw [nbBest_succ]
        rw [if_pos (by simp only [hc, Bool.true_and, decide_eq_true_eq]; word)]
        rw [show (W64 (sint.nat b : Int)) = b by word]
        wp_join_done
      · rw [nbBest_succ]
        rw [if_neg (by simp only [hc, Bool.true_and, decide_eq_true_eq]; intro h'; apply Hif; word)]
        wp_join_done
  wp_if_destruct
  · wp_for_post
    have hbn : sint.nat s.len = h.length := by omega
    rw [hbn, show nbBest h a (h.length + 1) = tNameBound h a from rfl]
    iapply HΦ
    itrivial
  · wp_for_post
    iframe
    have : b ≠ s.len := Hif
    have : sint.Z b ≠ sint.Z s.len := by intro h'; apply this; word
    have hb1 : sint.nat (b + W64 1) = sint.nat b + 1 := by word
    iexists b + W64 1
    rw [hb1]
    iframe
    ipureintro
    constructor <;> word

end proof

end etcd_wal
end EtcdGrove
end Perennial
