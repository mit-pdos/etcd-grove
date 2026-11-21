/- The slice advances past exactly the complete runs at or below the apply cursor. -/
module
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.replayTerms__after

@[expose] public section
noncomputable section
namespace Perennial
namespace EtcdGrove
open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem replayTerms.after.wp_proof : replayTerms.after.spec (GF := GF) (hG := hG) := by
  intro r runs index
  wp_start as #Hr
  (try wp_auto)
  let done := fun run : replayTermRun => decide (uint.nat run.last' ≤ uint.nat index)
  ihave HI : (∃ (sl : GoSlice) (xs : List replayTermRun),
      "r" ∷ r_ptr ↦ sl ∗ "#Hruns" ∷ sl ↦*□ xs ∗ "%hrest" ∷ ⌜xs.dropWhile done = runs.dropWhile done⌝ : IProp GF) $$ [r]
  · iexists r, runs; iframe Hr; iframe; ipureintro; rfl
  wp_for HI
  ihave %hlen := ownSlice_len sl _ xs $$ Hruns
  ihave %hwf := ownSlice_wf sl _ xs $$ Hruns
  cases xs with
  | nil =>
    have hz : ¬ sint.Z (W64 0) < sint.Z sl.len := by simp only [List.length_nil] at hlen; word
    (try wp_auto)
    simp only [hz, decide_false, Bool.false_eq_true, ↓reduceIte]
    (try wp_auto)
    simp only [intoVal_eq_iff, Bool.false_eq_true, decide_false, _root_.decide_true, ↓reduceIte]
    (try wp_auto)
    iapply HΦ
    rw [← hrest, List.dropWhile_nil]; iexact Hruns
  | cons x xs =>
    have hpos : 0 < sint.Z sl.len := by simp only [List.length_cons] at hlen; word
    have hb : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z sl.len := ⟨by decide, hpos⟩
    icases ownSlice_elem_acc (sint.Z (W64 0)) x sl DFrac.discard (x :: xs) (by decide) rfl $$ Hruns with ⟨#Hx, -⟩
    iStructNamed Hx
    (try wp_auto)
    simp only [hpos, _root_.decide_true, hb, ↓reduceIte]
    (try wp_auto)
    simp only [hb, ↓reduceIte]
    (try wp_auto)
    (try wp_auto)
    by_cases he : uint.Z x.last' ≤ uint.Z index
    · simp only [he, _root_.decide_true, ↓reduceIte]
      (try wp_auto)
      have hs : 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) ≤ sint.Z sl.len ∧ sint.Z sl.len ≤ sint.Z sl.cap := by
        refine ⟨by decide, ?_, hwf.2⟩; word
      simp only [hs, ↓reduceIte]
      (try wp_auto)
      icases (ownSlice_slice (W64 1) sl.len sl DFrac.discard (x :: xs) ⟨hs.1, hs.2.1, Int.le_refl _⟩).1 $$ Hruns
        with ⟨-, #Hmid, -⟩
      wp_for_post
      iframe
      iexists _, xs
      have hsub : subslice (sint.nat (W64 1)) (sint.nat sl.len) (x :: xs) = xs := by
        unfold subslice; rw [← hlen.1, List.take_length]; rfl
      rw [hsub]
      iframe Hmid
      iframe
      ipureintro
      have hd : done x = true := by simp [done]; word
      simpa [List.dropWhile, hd] using hrest
    · simp only [decide_eq_false he, ↓reduceIte]
      (try wp_auto)
      simp only [intoVal_eq_iff, Bool.false_eq_true, decide_false, _root_.decide_true, ↓reduceIte]
      (try wp_auto)
      iapply HΦ
      have hd : done x = false := by simp [done]; word
      rw [← hrest]
      simp only [List.dropWhile, hd, Bool.false_eq_true, ↓reduceIte]; iexact Hruns

end EtcdGrove
end Perennial
