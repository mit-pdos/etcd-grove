/- Lean-first (no Rocq counterpart). Proof of `Spec/github_com/anishathalye/porcupine/byTime__Less.lean`. -/
module

public import Spec.github_com.anishathalye.porcupine.byTime__Less

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace porcupine

open Iris Iris.BI Iris.ProofMode github_com.anishathalye.porcupine

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.anishathalye.porcupine.Assumptions]

omit package_sem in
/-- An element of a slice of entries, borrowed and given back unchanged. -/
theorem entry_elem_acc (sl : GoSlice) (es : List entry) (dq : DFrac) (i : w64) (a : entry)
    (hi : 0 ≤ sint.Z i) (ha : es[sint.nat i]? = some a) :
    (sl ↦*{dq} es : IProp GF) ⊢
      typedPointsto (sliceIndexRef entry (sint.Z i) sl) a dq ∗
      (typedPointsto (sliceIndexRef entry (sint.Z i) sl) a dq -∗ sl ↦*{dq} es) := by
  have hse : es.set (sint.Z i).toNat a = es := by
    obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.1 ha
    show es.set (sint.nat i) a = es
    rw [← heq]; exact List.set_getElem_self hlt
  iintro Hs
  icases ownSlice_elem_acc (sint.Z i) a sl dq es hi ha $$ Hs with ⟨He, Hclose⟩
  iframe He
  iintro He
  ihave Hs := Hclose $$ He
  rw [hse]
  iexact Hs

omit package_sem in
/-- The `time` field of an element of a slice of entries, borrowed. -/
theorem entry_time_acc (sl : GoSlice) (es : List entry) (dq : DFrac) (i : w64) (a : entry)
    (hi : 0 ≤ sint.Z i) (ha : es[sint.nat i]? = some a) :
    (sl ↦*{dq} es : IProp GF) ⊢
      (sliceIndexRef entry (sint.Z i) sl).[entry, go!"time"] ↦{dq} a.time' ∗
      ((sliceIndexRef entry (sint.Z i) sl).[entry, go!"time"] ↦{dq} a.time' -∗
        sl ↦*{dq} es) := by
  iintro Hs
  icases entry_elem_acc sl es dq i a hi ha $$ Hs with ⟨He, Hsback⟩
  icases (AccessStrict.access_strict
      (A := (sliceIndexRef entry (sint.Z i) sl).[entry, go!"time"] ↦{dq} a.time')
      (A' := (sliceIndexRef entry (sint.Z i) sl).[entry, go!"time"] ↦{dq} a.time')
      (P := sliceIndexRef entry (sint.Z i) sl ↦{dq} a)) $$ He with ⟨He, Hclose⟩
  iframe He
  iintro He
  iapply Hsback
  iapply Hclose $$ He

omit package_sem in
/-- The `kind` field of an element of a slice of entries, borrowed. -/
theorem entry_kind_acc (sl : GoSlice) (es : List entry) (dq : DFrac) (i : w64) (a : entry)
    (hi : 0 ≤ sint.Z i) (ha : es[sint.nat i]? = some a) :
    (sl ↦*{dq} es : IProp GF) ⊢
      (sliceIndexRef entry (sint.Z i) sl).[entry, go!"kind"] ↦{dq} a.kind' ∗
      ((sliceIndexRef entry (sint.Z i) sl).[entry, go!"kind"] ↦{dq} a.kind' -∗
        sl ↦*{dq} es) := by
  iintro Hs
  icases entry_elem_acc sl es dq i a hi ha $$ Hs with ⟨He, Hsback⟩
  icases (AccessStrict.access_strict
      (A := (sliceIndexRef entry (sint.Z i) sl).[entry, go!"kind"] ↦{dq} a.kind')
      (A' := (sliceIndexRef entry (sint.Z i) sl).[entry, go!"kind"] ↦{dq} a.kind')
      (P := sliceIndexRef entry (sint.Z i) sl ↦{dq} a)) $$ He with ⟨He, Hclose⟩
  iframe He
  iintro He
  iapply Hsback
  iapply Hclose $$ He

theorem byTime.Less.wp_proof : byTime.Less.spec (GF := GF) (hG := hG) :=
  fun sl es dq i j a b => by
  wp_start as ⟨Hs, %Hij⟩
  wp_auto
  obtain ⟨hi0, hj0, ha, hb⟩ := Hij
  ihave %Hl := ownSlice_len _ _ _ $$ Hs
  have hilt : sint.nat i < es.length := (List.getElem?_eq_some_iff.1 ha).1
  have hjlt : sint.nat j < es.length := (List.getElem?_eq_some_iff.1 hb).1
  have Hbi : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z sl.len := by
    have := Hl.1; refine ⟨hi0, ?_⟩; word
  have Hbj : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sl.len := by
    have := Hl.1; refine ⟨hj0, ?_⟩; word
  simp only [Hbi, _root_.and_self, ite_true]
  wp_auto
  icases entry_time_acc sl es dq i a hi0 ha $$ Hs with ⟨He, Hs⟩
  wp_auto
  ihave Hs := Hs $$ He
  simp only [Hbj, _root_.and_self, ite_true]
  icases entry_time_acc sl es dq j b hj0 hb $$ Hs with ⟨He, Hs⟩
  wp_auto
  ihave Hs := Hs $$ He
  wp_if_destruct
  · have Ht := Hif
    simp only [Hbi, _root_.and_self, ite_true]
    icases entry_kind_acc sl es dq i a hi0 ha $$ Hs with ⟨He, Hs⟩
    wp_auto
    ihave Hs := Hs $$ He
    wp_if_destruct
    · simp only [Hbj, _root_.and_self, ite_true]
      icases entry_kind_acc sl es dq j b hj0 hb $$ Hs with ⟨He, Hs⟩
      wp_auto
      ihave Hs := Hs $$ He
      have : entryLt a b = decide (b.kind' = true) := by
        unfold entryLt; rw [Ht, Hif]; simp
      rw [← this]
      iapply HΦ $$ Hs
    · have : entryLt a b = false := by
        unfold entryLt
        cases hk : a.kind'
        · exact absurd hk Hif
        · simp [Ht]
      rw [← this]
      iapply HΦ $$ Hs
  · simp only [Hbi, _root_.and_self, ite_true]
    icases entry_time_acc sl es dq i a hi0 ha $$ Hs with ⟨He, Hs⟩
    wp_auto
    ihave Hs := Hs $$ He
    simp only [Hbj, _root_.and_self, ite_true]
    icases entry_time_acc sl es dq j b hj0 hb $$ Hs with ⟨He, Hs⟩
    wp_auto
    ihave Hs := Hs $$ He
    have : entryLt a b = decide (sint.Z a.time' < sint.Z b.time') := by
      unfold entryLt; simp only [Hif, ↓reduceIte]
    rw [← this]
    iapply HΦ $$ Hs

end proof

end porcupine
end EtcdGrove
end Perennial
