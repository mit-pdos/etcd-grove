/-
`Spec/strings/Cut.lean`'s and `Spec/strings/TrimLeft.lean`'s specs (this repository's, which Net's
net/http and net/rpc client proofs take as callee hypotheses) from Perennial's own specs of the
same functions, which Perennial proves since 52d62e83c (`Perennial.Proof.strings.Link`'s
`strings.wp_Cut`, `strings.wp_TrimLeft`): the two `cut`s agree (`strings.cut_eq`), the two
`trimLeft`s are the same definition, and Perennial's `TrimLeft` precondition is weaker.
-/
module

public import Spec.strings.Cut
public import Spec.strings.TrimLeft
public import Perennial.Spec.strings.Cut
public import Perennial.Spec.strings.TrimLeft

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

/-- This repository's `strings.cut` is Perennial's `internal.stringslite.cut`. -/
theorem strings.cut_eq (s sep : GoString) :
    strings.cut s sep = _root_.Perennial.internal.stringslite.cut s sep := by
  unfold strings.cut strings.index _root_.Perennial.internal.stringslite.cut
  rcases _root_.Perennial.internal.bytealg.index_cases s sep with ⟨i, hi, hp, hmin⟩ | ⟨hi, hn⟩
  · have hb := (_root_.Perennial.internal.bytealg.index_bounds s sep).2
    rw [hi] at hb
    have hle : i ≤ s.length := by
      have := hb (by omega)
      omega
    have hf : (List.range (s.length + 1)).find? (fun j => decide (sep <+: s.drop j)) = some i := by
      rw [List.find?_range_eq_some]
      refine ⟨by simpa using hp, by simp; omega, fun j hj => by simpa using hmin j hj⟩
    rw [hf, hi]
    simp
  · have hf : (List.range (s.length + 1)).find? (fun j => decide (sep <+: s.drop j)) = none := by
      rw [List.find?_range_eq_none]
      intro j _
      simpa using hn j
    rw [hf, hi]
    simp

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.strings.Assumptions]

/-- `Spec/strings/Cut.lean`'s spec, from Perennial's. -/
theorem strings.Cut.of_perennial
    (wp_Cut : _root_.Perennial.strings.Cut.spec (GF := GF) (hG := hG)) :
    strings.Cut.spec (GF := GF) (hG := hG) := by
  intro s sep
  simp only [strings.cut_eq]
  exact wp_Cut s sep

/-- `Spec/strings/TrimLeft.lean`'s spec, from Perennial's (whose precondition is weaker). -/
theorem strings.TrimLeft.of_perennial
    (wp_TrimLeft : _root_.Perennial.strings.TrimLeft.spec (GF := GF) (hG := hG)) :
    strings.TrimLeft.spec (GF := GF) (hG := hG) := by
  intro s cutset
  rw [show strings.trimLeft s cutset = _root_.Perennial.strings.trimLeft s cutset from rfl]
  iintro %Φ ⟨#Hpkg, %hc⟩ HΦ
  iapply wp_TrimLeft s cutset
  · ipureintro
    intro b hb
    have := hc b hb
    word
  · iexact HΦ

end proof

end EtcdGrove
end Perennial
