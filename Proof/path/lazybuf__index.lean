/-
Proof of `Spec/path/lazybuf__index.lean`. Lean-first.
-/
module

public import Spec.path.lazybuf__index

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.path.Assumptions]

theorem path.lazybuf.index.wp_proof : path.lazybuf.index.spec (GF := GF) (hG := hG) := by
  intro b p P w i Hi
  wp_start as Hb
  iunfold path.lbOwn at Hb
  icases Hb with ⟨%buf, Hs, Hbuf, Hw, %Hwb, Hcase⟩
  try wp_auto
  icases Hcase with (⟨%Hnil, %HP⟩ | ⟨⟨%Hnn, %HPl⟩, Hsl⟩)
  · subst Hnil HP
    try wp_auto
    obtain ⟨v, hv⟩ : ∃ v, P[i]? = some v := ⟨_, List.getElem?_eq_getElem Hi⟩
    have hg : P.getD i 0 = v := by simp [List.getD, hv]
    have hi1 : sint.nat (W64 (i : Int)) = i := by word
    have hi0 : 0 ≤ sint.Z (W64 (i : Int)) := by word
    simp only [hi1, hi0, ↓reduceIte, hv, hg]
    try wp_auto
    iapply HΦ
    iunfold path.lbOwn
    iexists slice.nil
    iframe
    isplitr
    · ipureintro; exact Hwb
    ileft; ipureintro; exact ⟨rfl, rfl⟩
  · ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
    simp only [Hnn, decide_false, Bool.not_false]
    try wp_auto
    have hi1 : sint.nat (W64 (i : Int)) = i := by word
    obtain ⟨v, hv⟩ : ∃ v, P[i]? = some v := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hg : P.getD i 0 = v := by simp [List.getD, hv]
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word⟩)]
    wp_apply wp_load_slice_index buf (sint.Z (W64 (i : Int))) P _ v (by word) $$ [Hsl] as Hsl
    · iframe; ipureintro
      rw [show (sint.Z (W64 (i : Int))).toNat = i by word]; exact hv
    try wp_auto
    rw [hg]
    iapply HΦ
    iunfold path.lbOwn
    iexists buf
    iframe
    isplitr
    · ipureintro; exact Hwb
    iright; iframe; ipureintro; exact ⟨Hnn, HPl⟩

end proof

end EtcdGrove
end Perennial
