/-
`typed.reconcileWithSchemaWalker.prepareDescent`: proved (Prove phase, 2026-11-19), as the merging
walker's; the parent's path buffer given back by `wp_slice_append_undo_any` (the child may give it
back holding another representation of the same path).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.reconcileWithSchemaWalker__prepareDescent
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsBPers
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsBSlice
public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsRep

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

theorem rw_path_undo (ps ps2 : fieldpath.Path) (es : List fieldpath.PathElement) (p : Path) (pe' : PE)
    (hl : es.length = p.length) :
    isPEs (GF := GF) es p ∗
      (∀ vs2 : List fieldpath.PathElement, ps2 ↦* vs2 ∗
        ownSliceCap fieldpath.PathElement ps2 (DFrac.own 1) -∗
        ∃ vs1 : List fieldpath.PathElement, ps ↦* vs1 ∗
          ownSliceCap fieldpath.PathElement ps (DFrac.own 1) ∗
          ⌜vs1 = es ∨ vs1 = vs2.take es.length⌝) ⊢
      ((∃ es, ps2 ↦* es ∗ isPEs es (p ++ [pe'])) ∗
        ownSliceCap fieldpath.PathElement ps2 (DFrac.own 1) -∗
      (∃ es, ps ↦* es ∗ isPEs es p) ∗ ownSliceCap fieldpath.PathElement ps (DFrac.own 1)) := by
  iintro ⟨Hpes, Hundo⟩ ⟨⟨%es2, Hes2, Hpes2⟩, Hcap2⟩
  ihave %Hl2 := isPEs_length_law_holds _ _ $$ Hpes2
  icases Hundo $$ %es2 [Hes2 Hcap2] with ⟨%vs1, Hvs1, Hc1, %Hvs⟩
  · iframe Hes2 Hcap2
  iframe Hc1
  iexists vs1
  iframe Hvs1
  rcases Hvs with rfl | rfl
  · iexact Hpes
  · have hsplit : es2 = es2.take es.length ++ es2.drop es.length := (List.take_append_drop _ _).symm
    have hl2 : es2.length = p.length + 1 := by simpa using Hl2
    rw [hsplit]
    have htl : (es2.take es.length).length = p.length := by
      rw [List.length_take]; omega
    icases (isPEs_app_law_holds (es2.take es.length) (es2.drop es.length) p [pe'] htl).1 $$ Hpes2
      with ⟨H1, -⟩
    rw [List.take_append_of_le_length (by rw [List.length_take]; omega), List.take_take,
      Nat.min_self]
    iexact H1

theorem typed.reconcileWithSchemaWalker.prepareDescent.wp_proof :
    typed.reconcileWithSchemaWalker.prepareDescent.spec (GF := GF) :=
    fun w sc S st ps fs tv rem add sp pe pe' tr t' => by
  wp_start as ⟨Hcore, Hps, Hsp, #Hpe, #Htr'⟩
  unfold ownPath isPathF
  icases Hps with ⟨⟨%es, Hes, Hpes⟩, Hcap⟩
  ihave #Hpes := isPEs_persistent_law_holds _ _ $$ Hpes
  ihave %Hlen := isPEs_length_law_holds _ _ $$ Hpes
  unfold rwCore
  icases Hcore with ⟨%tr0, Hw, #Htr, #Hsc, %HWF⟩
  wp_auto
  wp_if_destruct
  · wp_apply (wp_slice_literal (V := Loc) [])
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, Hslc⟩
    wp_alloc spc as Hspc
    ihave %Hspcnn := typedPointsto_not_null _ _ _ $$ Hspc
    (try wp_auto)
    wp_apply (wp_slice_literal (V := fieldpath.PathElement) [pe])
    isplitr
    · ipureintro; rfl
    iintro %sl2 ⟨Hsl2, -⟩
    (try wp_auto)
    wp_apply (wp_slice_append_undo_any (V := fieldpath.PathElement) ps es _ [pe] (DFrac.own 1))
      $$ [$Hes $Hcap $Hsl2] as %ps2 ⟨Hps2, Hcap2, -, Hundo⟩
    (try wp_auto)
    iapply HΦ
    iexists _, ps2
    isplitl [Hw]
    · iexists tr0
      iframe
      isplitr; iexact Htr
      isplitr; iexact Hsc
      ipureintro; exact HWF
    isplitl [«$r0»]
    · iexists tr
      iframe
      isplitr; iexact Htr'
      isplitr; iexact Hsc
      ipureintro; exact HWF
    isplitl [Hps2 Hcap2]
    · iframe
      iapply (isPEs_app_law_holds es [pe] st.path [pe'] Hlen).2
      isplitr; · iexact Hpes
      iapply (isPEs_cons_law_holds pe [] pe' []).2
      isplitr; · iexact Hpe
      iapply (show iprop(True) ⊢ isPEs (GF := GF) [] [] from isPEs_nil_law_holds)
      ipureintro; trivial
    isplitl [Hundo]
    · iapply (rw_path_undo ps ps2 es st.path pe' Hlen)
      iframe Hundo
      iexact Hpes
    isplitl
    · unfold spareWalkers
      iright
      iexists _, []
      iframe
      iapply (BigSepL.bigSepL_nil_intro (P := iprop(True)))
      ipureintro; trivial
    · ipureintro; exact ⟨Hspcnn, fun h => absurd rfl h⟩
  · unfold spareWalkers
    icases Hsp with (%Hn | ⟨%sl, %ws, Hspp, Hws, Hwsc, Hwl⟩)
    · exact absurd Hn Hif
    have Hspnn : sp ≠ null := Hif
    ihave %Hwslen := ownSlice_len _ _ _ $$ Hws
    wp_auto
    wp_if_destruct
    · list_elem ws (sint.nat sl.len - 1) as wl
      have hb : 0 ≤ sint.Z (sl.len - W64 1) ∧ sint.Z (sl.len - W64 1) < sint.Z sl.len := by word
      simp only [hb, _root_.and_self, ↓reduceIte]
      wp_apply (wp_load_slice_index sl (sint.Z (sl.len - W64 1)) ws (DFrac.own 1) wl (by word))
        $$ [Hws] as Hws
      · iframe; ipureintro
        rw [show (sint.Z (sl.len - W64 1)).toNat = sint.nat sl.len - 1 by word]
        exact Hwl_lookup
      ihave %Hwf := ownSlice_wf _ _ _ $$ Hws
      have hb2 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (sl.len - W64 1) ∧
          sint.Z (sl.len - W64 1) ≤ sint.Z sl.cap := by word
      simp only [hb2, _root_.and_self, ↓reduceIte]
      have hpos : 0 < sint.nat sl.len := by word
      have hlen := Hwslen.1
      have hws : ws = ws.take (sint.nat sl.len - 1) ++ [wl] := by
        have h1 := List.take_append_drop (sint.nat sl.len - 1) ws
        have h2 : ws.drop (sint.nat sl.len - 1) = [wl] := by
          rw [List.drop_eq_getElem_cons (by omega)]
          rw [List.getElem?_eq_some_iff] at Hwl_lookup
          obtain ⟨_, h⟩ := Hwl_lookup
          rw [h, List.drop_eq_nil_of_le (by omega)]
        rw [h2] at h1; exact h1.symm
      generalize hws' : ws.take (sint.nat sl.len - 1) = ws' at hws
      rw [hws]
      icases BigSepL.bigSepL_snoc.1 $$ Hwl with ⟨Hwl, ⟨%v2, Hv2⟩⟩
      icases ownSlice_pop sl ws' wl $$ [$Hws $Hwsc] with ⟨Hws, Hwsc⟩
      wp_auto
      wp_apply (wp_slice_literal (V := fieldpath.PathElement) [pe])
      isplitr
      · ipureintro; rfl
      iintro %sl2 ⟨Hsl2, -⟩
      (try wp_auto)
      wp_apply (wp_slice_append_undo_any (V := fieldpath.PathElement) ps es _ [pe] (DFrac.own 1))
        $$ [$Hes $Hcap $Hsl2] as %ps2 ⟨Hps2, Hcap2, -, Hundo⟩
      (try wp_auto)
      iapply HΦ
      iexists sp, ps2
      isplitl [Hw]
      · iexists tr0
        iframe
        isplitr; iexact Htr
        isplitr; iexact Hsc
        ipureintro; exact HWF
      isplitl [Hv2]
      · iexists tr
        iframe
        isplitr; iexact Htr'
        isplitr; iexact Hsc
        ipureintro; exact HWF
      isplitl [Hps2 Hcap2]
      · iframe
        iapply (isPEs_app_law_holds es [pe] st.path [pe'] Hlen).2
        isplitr; · iexact Hpes
        iapply (isPEs_cons_law_holds pe [] pe' []).2
        isplitr; · iexact Hpe
        iapply (show iprop(True) ⊢ isPEs (GF := GF) [] [] from isPEs_nil_law_holds)
        ipureintro; trivial
      isplitl [Hundo]
      · iapply (rw_path_undo ps ps2 es st.path pe' Hlen)
        iframe Hundo
        iexact Hpes
      isplitl
      · iright
        iexists _, ws'
        iframe
      · ipureintro; exact ⟨Hspnn, fun _ => rfl⟩
    · have hws : ws = [] := by
        apply List.eq_nil_of_length_eq_zero
        have := Hwslen.1
        word
      subst hws
      wp_apply (wp_slice_literal (V := fieldpath.PathElement) [pe])
      isplitr
      · ipureintro; rfl
      iintro %sl2 ⟨Hsl2, -⟩
      (try wp_auto)
      wp_apply (wp_slice_append_undo_any (V := fieldpath.PathElement) ps es _ [pe] (DFrac.own 1))
        $$ [$Hes $Hcap $Hsl2] as %ps2 ⟨Hps2, Hcap2, -, Hundo⟩
      (try wp_auto)
      iapply HΦ
      iexists sp, ps2
      isplitl [Hw]
      · iexists tr0
        iframe
        isplitr; iexact Htr
        isplitr; iexact Hsc
        ipureintro; exact HWF
      isplitl [«$r0»]
      · iexists tr
        iframe
        isplitr; iexact Htr'
        isplitr; iexact Hsc
        ipureintro; exact HWF
      isplitl [Hps2 Hcap2]
      · iframe
        iapply (isPEs_app_law_holds es [pe] st.path [pe'] Hlen).2
        isplitr; · iexact Hpes
        iapply (isPEs_cons_law_holds pe [] pe' []).2
        isplitr; · iexact Hpe
        iapply (show iprop(True) ⊢ isPEs (GF := GF) [] [] from isPEs_nil_law_holds)
        ipureintro; trivial
      isplitl [Hundo]
      · iapply (rw_path_undo ps ps2 es st.path pe' Hlen)
        iframe Hundo
        iexact Hpes
      isplitl
      · iright
        iexists sl, []
        iframe
      · ipureintro; exact ⟨Hspnn, fun _ => rfl⟩

end proof

end smd
end EtcdGrove
end Perennial
