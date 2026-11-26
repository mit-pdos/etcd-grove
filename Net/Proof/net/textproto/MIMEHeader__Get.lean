/-
The proof of `textproto.MIMEHeader.Get` (`Net/Spec/net/textproto/MIMEHeader__Get.lean`): the map is not
nil (`ownMap_not_nil`), the canonical key (unchanged, `CanonicalMIMEHeaderKey.spec`) looked up, then the
slice's first value, or `""`.
-/
module

public import Net.Spec.net.textproto.MIMEHeader__Get
public import Net.Spec.net.textproto.CanonicalMIMEHeaderKey

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace net.textproto

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.textproto.Assumptions]

theorem MIMEHeader.Get.wp_proof
    (wp_Canon : CanonicalMIMEHeaderKey.spec (GF := GF) (hG := hG)) :
    MIMEHeader.Get.spec (GF := GF) (hG := hG) := by
  intro h dq ms key dv vs
  unfold mimeVals
  rcases hk : ms !! key with _ | s
  · wp_start as ⟨%Hk, Hm, %Hvs⟩
    subst Hvs
    ihave %Hnn := ownMap_not_nil _ _ _ $$ Hm
    wp_auto
    try rw [decide_eq_false Hnn]
    wp_auto
    wp_apply wp_Canon key
    · ipureintro; exact Hk
    wp_apply wp_map_lookup1 $$ Hm as Hm
    rw [hk]
    wp_auto
    simp only [List.head?_nil, Option.getD_none]
    iapply HΦ
    iframe Hm
  · wp_start as ⟨%Hk, Hm, Hs⟩
    ihave %Hnn := ownMap_not_nil _ _ _ $$ Hm
    wp_auto
    try rw [decide_eq_false Hnn]
    wp_auto
    wp_apply wp_Canon key
    · ipureintro; exact Hk
    wp_apply wp_map_lookup1 $$ Hm as Hm
    rw [hk]
    ihave %Hlen := ownSlice_len _ _ _ $$ Hs
    simp only [Option.getD_some]
    rcases vs with _ | ⟨x, vs⟩
    · rw [decide_eq_true (show s.len = W64 0 by simp at Hlen; word)]
      wp_auto
      simp only [List.head?_nil, Option.getD_none]
      iapply HΦ
      iframe
    · rw [decide_eq_false (show ¬ s.len = W64 0 by simp at Hlen; word)]
      have hb : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z s.len := by simp at Hlen; word
      wp_auto
      rw [if_pos hb]
      wp_apply wp_load_slice_index s (sint.Z (W64 0)) _ _ x (by decide) $$ [Hs] as Hs
      · iframe; ipureintro; rfl
      simp only [List.head?_cons, Option.getD_some]
      iapply HΦ
      iframe

end proof

end net.textproto
end Perennial
