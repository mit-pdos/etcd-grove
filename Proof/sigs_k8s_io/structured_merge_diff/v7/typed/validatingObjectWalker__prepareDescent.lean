/-
`typed.validatingObjectWalker.prepareDescent`: not proved yet (`sorry`): the stage's Prove step, after the freeze
(notes/smd-plan.md). Draft (2026-11-19).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.validatingObjectWalker__prepareDescent

public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsA

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open sigs_k8s_io.structured_merge_diff.v7

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : typed.Assumptions]

theorem typed.validatingObjectWalker.prepareDescent.wp_proof :
    typed.validatingObjectWalker.prepareDescent.spec (GF := GF) := fun w sc S st sp a tr t' => by
  wp_start as ⟨Hcore, Hsp, #Htr⟩
  iunfold vwCore at Hcore
  icases Hcore with ⟨%tr0, Hw, #Htr0, #Hsc, %Hwf⟩
  wp_auto
  wp_join iprop(∃ (sp' : Loc) (sl : GoSlice) (ws : List Loc), ⌜sp' ≠ null⌝ ∗ ⌜sp ≠ null → sp' = sp⌝ ∗ v_ptr ↦ w ∗
      w ↦ (typed.validatingObjectWalker.mk st.value sc tr0 false sp' a) ∗ sp' ↦ sl ∗ sl ↦* ws ∗
      ownSliceCap Loc sl (DFrac.own 1) ∗
      [∗list] x ∈ ws, ∃ v : typed.validatingObjectWalker, x ↦ v)
    with [v Hw Hsp] as ⟨%sp', %sl, %ws, %Hspn, %Hspe, v, Hw, Hsp', Hsl, Hcap, Hws⟩
  · wp_apply (wp_slice_literal (V := Loc) [])
    isplitr
    · ipureintro; rfl
    iintro %slp ⟨Hsl, Hcap⟩
    wp_auto
    icases typedPointsto_not_null_dup _ _ _ $$ «$r0» with ⟨Hr0, %Hnn⟩
    isplitr
    · ipureintro; rfl
    iexists _, _, []
    iframe v Hw Hsl Hcap Hr0
    isplitr
    · ipureintro; exact Hnn
    isplitr
    · ipureintro; intro h; contradiction
    iframe
    iapply BigSepL.bigSepL_nil.2
    itrivial
  · iunfold spareWalkers at Hsp
    icases Hsp with (%h | ⟨%sl, %ws, Hsp', Hsl, Hcap, Hws⟩)
    · contradiction
    iexists sp, sl, ws
    iframe
    isplitr
    · ipureintro; assumption
    ipureintro; intro; rfl
  wp_join iprop(∃ (w2 : Loc) (sl' : GoSlice) (ws' : List Loc), v_ptr ↦ w ∗ n_ptr ↦ sl.len ∗
      w ↦ (typed.validatingObjectWalker.mk st.value sc tr0 false sp' a) ∗ v2_ptr ↦ w2 ∗
      (∃ vv : typed.validatingObjectWalker, w2 ↦ vv) ∗ sp' ↦ sl' ∗ sl' ↦* ws' ∗
      ownSliceCap Loc sl' (DFrac.own 1) ∗
      [∗list] x ∈ ws', ∃ vv : typed.validatingObjectWalker, x ↦ vv)
    with [v n Hw v2 Hsp' Hsl Hcap Hws] as ⟨%w2, %sl', %ws', v, n, Hw, v2, ⟨%vv, Hw2⟩, Hsp', Hsl, Hcap, Hws⟩
  · ihave %Hlen := ownSlice_len $$ Hsl
    have hb : 0 ≤ sint.Z (sl.len - W64 1) ∧ sint.Z (sl.len - W64 1) < sint.Z sl.len := by
      have : sint.Z (W64 0) = 0 := rfl
      constructor <;> word
    rw [ite_eq_left hb]
    obtain ⟨ws0, wl, hws⟩ : ∃ ws0 wl, ws = ws0 ++ [wl] := by
      have hne : ws ≠ [] := by
        intro h; subst h; simp at Hlen; have : sint.Z (W64 0) = 0 := rfl; word
      exact ⟨ws.dropLast, ws.getLast hne, (List.dropLast_concat_getLast hne).symm⟩
    subst hws
    have hk : (sint.Z (sl.len - W64 1)).toNat = ws0.length := by
      simp only [List.length_append, List.length_singleton] at Hlen
      have : sint.Z (W64 0) = 0 := rfl
      word
    wp_apply (wp_load_slice_index sl (sint.Z (sl.len - W64 1)) (ws0 ++ [wl]) (DFrac.own 1) wl hb.1)
      $$ [Hsl] as Hsl
    · iframe; ipureintro; rw [hk]; simp
    try wp_auto
    ihave %Hwf2 := ownSlice_wf $$ Hsl
    have hb2 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (sl.len - W64 1) ∧
        sint.Z (sl.len - W64 1) ≤ sint.Z sl.len := by
      have : sint.Z (W64 0) = 0 := rfl
      refine ⟨by word, by word, by word⟩
    rw [ite_eq_left ⟨hb2.1, hb2.2.1, by word⟩]
    wp_auto
    ihave H := ownSlice_slice_with_cap (V := Loc) (W64 0) (sl.len - W64 1) sl (ws0 ++ [wl]) hb2
      $$ [Hsl Hcap]
    · iframe
    icases H with ⟨-, Hsl', Hcap'⟩
    icases BigSepL.bigSepL_snoc.1 $$ Hws with ⟨Hws, Hwl⟩
    isplitr
    · ipureintro; rfl
    iexists wl, _, ws0
    iframe v n Hw v2 Hwl Hsp' Hcap' Hws
    iExactEq Hsl'
    congr 1
    have : sint.nat (sl.len - W64 1) = ws0.length := hk
    simp only [subslice, this, List.take_left]
    rfl
  iapply HΦ
  iexists sp'
  iunfold vwCore
  isplitl [Hw]
  · iexists tr0; iframe Hw; iframe #; ipureintro; exact Hwf
  isplitl [Hw2]
  · iexists tr; iframe Hw2; iframe #; ipureintro; exact Hwf
  iunfold spareWalkers
  isplitl
  · iright
    iexists sl', ws'
    iframe
  isplitr
  · ipureintro; exact Hspn
  ipureintro; exact Hspe

end proof

end smd
end EtcdGrove
end Perennial
