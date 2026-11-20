/-
`typed.toFieldSetWalker.prepareDescent`: proved (Prove phase, 2026-11-20): as
`mergingWalker.prepareDescent` (a spare walker or a new one, the parent copied into it, the path
element appended).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.toFieldSetWalker__prepareDescent
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsBPers
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

theorem typed.toFieldSetWalker.prepareDescent.wp_proof :
    typed.toFieldSetWalker.prepareDescent.spec (GF := GF) :=
    fun w sc S st ps s sp a pe pe' tr t' => by
  wp_start as ⟨Hcore, Hps, Hsp, #Hpe, #Htr'⟩
  unfold ownPath isPathF
  icases Hps with ⟨⟨%es, Hes, Hpes⟩, Hcap⟩
  ihave #Hpes := isPEs_persistent_law_holds _ _ $$ Hpes
  ihave %Hlen := isPEs_length_law_holds _ _ $$ Hpes
  unfold twCore
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
    wp_apply (wp_slice_append (V := fieldpath.PathElement) ps es _ [pe] (DFrac.own 1))
      $$ [$Hes $Hcap $Hsl2] as %ps2 ⟨Hps2, Hcap2, -⟩
    iapply HΦ
    iexists _, ps2
    simp only
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
    isplitl
    · unfold spareWalkers
      iright
      iexists _, []
      iframe
      iapply (BigSepL.bigSepL_nil_intro (P := iprop(True)))
      ipureintro; trivial
    · ipureintro; exact Hspcnn
  · unfold spareWalkers
    icases Hsp with (%Hn | ⟨%sl, %ws, Hspp, Hws, Hwsc, Hwl⟩)
    · exact absurd Hn Hif
    have Hspnn : sp ≠ null := Hif
    ihave %Hwslen := ownSlice_len _ _ _ $$ Hws
    wp_auto
    wp_if_destruct
    · list_elem ws (sint.nat sl.len - 1) as wl
      have hb : 0 ≤ sint.Z (sl.len - W64 1) ∧ sint.Z (sl.len - W64 1) < sint.Z sl.len := by word
      simp only [hb, and_self, ↓reduceIte]
      wp_apply (wp_load_slice_index sl (sint.Z (sl.len - W64 1)) ws (DFrac.own 1) wl (by word))
        $$ [Hws] as Hws
      · iframe; ipureintro
        rw [show (sint.Z (sl.len - W64 1)).toNat = sint.nat sl.len - 1 by word]
        exact Hwl_lookup
      ihave %Hwf := ownSlice_wf _ _ _ $$ Hws
      have hb2 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (sl.len - W64 1) ∧
          sint.Z (sl.len - W64 1) ≤ sint.Z sl.cap := by word
      simp only [hb2, and_self, ↓reduceIte]
      -- the walker taken: the last of the spare list
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
      -- the rest of the spare list, its last cell absorbed into the capacity
      icases ownSlice_pop sl ws' wl $$ [$Hws $Hwsc] with ⟨Hws, Hwsc⟩
      wp_auto
      wp_apply (wp_slice_literal (V := fieldpath.PathElement) [pe])
      isplitr
      · ipureintro; rfl
      iintro %sl2 ⟨Hsl2, -⟩
      (try wp_auto)
      wp_apply (wp_slice_append (V := fieldpath.PathElement) ps es _ [pe] (DFrac.own 1))
        $$ [$Hes $Hcap $Hsl2] as %ps2 ⟨Hps2, Hcap2, -⟩
      iapply HΦ
      iexists sp, ps2
      simp only
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
      isplitl
      · iright
        iexists _, ws'
        iframe
      · ipureintro; exact Hspnn
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
      wp_apply (wp_slice_append (V := fieldpath.PathElement) ps es _ [pe] (DFrac.own 1))
        $$ [$Hes $Hcap $Hsl2] as %ps2 ⟨Hps2, Hcap2, -⟩
      iapply HΦ
      iexists sp, ps2
      simp only
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
      isplitl
      · iright
        iexists sl, []
        iframe
      · ipureintro; exact Hspnn

end proof

end smd
end EtcdGrove
end Perennial
