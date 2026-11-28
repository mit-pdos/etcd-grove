/-
Lean-first (no Rocq counterpart).

The proof of `(*histHashes).intern`: the maps made if `canon` is nil; then `canon[k]`'s nodes (taken
out of the map, or none), each compared with `st` (`storeEqual`): an equal one holds the history, by
its `canonNode` facts; otherwise a new node, appended to `canon[k]` and recorded in `is`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.histHashes__intern
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.storeHash
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.storeEqual

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- A literal of one unkeyed element has one element. -/
theorem arrayLiteralSize1 {a} : go.arrayLiteralSize [KeyedElement none a] = 1 := rfl

theorem histHashes.intern.wp_proof (wp_storeHash : storeHash.spec (GF := GF) (hG := hG))
    (wp_storeEqual : storeEqual.spec (GF := GF) (hG := hG)) :
    histHashes.intern.spec (GF := GF) (hG := hG) := by
  intro hh prev hs st s n
  wp_start as ⟨Hinv, #Hprev, #Hst, %Hn⟩
  iunfold hhInv at Hinv
  icases Hinv with ⟨%mc, %mi, %mg, %C, %I, %G, Hc, Hi, Hg, Hci, Hgs⟩
  (try wp_auto)
  wp_join iprop(∃ (mc' mi' : GoMap) (C' : GMap ikey GoSlice) (I' : GMap Loc Bool),
      hh_ptr ↦ hh ∗ structFieldRef histHashes go!"canon" hh ↦ mc' ∗ structFieldRef histHashes go!"is" hh ↦ mi' ∗
      mc' ↦$ C' ∗ mi' ↦$ I' ∗
      [∗map] k ↦ sl ∈ C', ∃ ns : List Loc, sl ↦* ns ∗ ownSliceCap Loc sl (DFrac.own 1) ∗
        [∗list] n ∈ ns, canonNode k n) with [hh Hc Hi Hci]
      as ⟨%mc', %mi', %C', %I', hh, Hc, Hi, HC, HI, HCs⟩
  · (try wp_auto)
    wp_apply (wp_map_make1 (K := ikey) (V := GoSlice) _ _) as %m1 Hm1
    (try wp_auto)
    wp_apply (wp_map_make1 (K := Loc) (V := Bool) _ _) as %m2 Hm2
    (try wp_auto)
    isplitr
    · ipureintro; rfl
    iexists m1, m2, ∅, ∅
    iframe
    iapply BigSepM.bigSepM_empty.2
    itrivial
  · icases Hci with (%Hnil | ⟨HC, HI, HCs⟩)
    · exact absurd Hnil.1 (by assumption)
    · iexists mc, mi, C, I
      iframe
  wp_apply wp_storeHash st s $$ [$Hst] as %hv -
  (try wp_auto)
  wp_apply (wp_map_lookup1 _ _ mc' C' (ikey.mk prev n hv) (DFrac.own 1)) $$ [$HC] as HC
  ihave Hsl : (∃ ns : List Loc,
      ((C' !! ikey.mk prev n hv).getD (zero_val GoSlice)) ↦* ns ∗
      ownSliceCap Loc ((C' !! ikey.mk prev n hv).getD (zero_val GoSlice)) (DFrac.own 1) ∗
      ([∗list] c ∈ ns, canonNode (ikey.mk prev n hv) c) ∗
      ((∀ sl' : GoSlice, (∃ ns' : List Loc, sl' ↦* ns' ∗ ownSliceCap Loc sl' (DFrac.own 1) ∗
          [∗list] c ∈ ns', canonNode (ikey.mk prev n hv) c) -∗
        [∗map] k ↦ sl ∈ <[ikey.mk prev n hv := sl']> C', ∃ ns : List Loc, sl ↦* ns ∗
          ownSliceCap Loc sl (DFrac.own 1) ∗ [∗list] n ∈ ns, canonNode k n) ∧
       ((∃ ns' : List Loc, ((C' !! ikey.mk prev n hv).getD (zero_val GoSlice)) ↦* ns' ∗
          ownSliceCap Loc ((C' !! ikey.mk prev n hv).getD (zero_val GoSlice)) (DFrac.own 1) ∗
          [∗list] c ∈ ns', canonNode (ikey.mk prev n hv) c) -∗
        [∗map] k ↦ sl ∈ C', ∃ ns : List Loc, sl ↦* ns ∗
          ownSliceCap Loc sl (DFrac.own 1) ∗ [∗list] n ∈ ns, canonNode k n)) : IProp GF) $$ [HCs]
  · cases hC : C' !! ikey.mk prev n hv with
    | none =>
      iexists []
      rw [Option.getD_none]
      isplitr
      · iapply (show ⊢ (zero_val GoSlice ↦* ([] : List Loc) : IProp GF) from ownSlice_nil _)
      isplitr
      · iapply (show ⊢ (ownSliceCap Loc (zero_val GoSlice) (DFrac.own 1) : IProp GF) from ownSliceCap_nil)
      isplitr
      · iapply BigSepL.bigSepL_nil.2; itrivial
      isplit
      · iintro %sl' Hsl'
        iapply (BigSepM.bigSepM_insert hC).2
        iframe
      · iintro -
        iexact HCs
    | some sl0 =>
      simp only [Option.getD_some]
      icases (BigSepM.bigSepM_delete hC).1 $$ HCs with ⟨⟨%ns, Hns, Hcap, #Hcn⟩, Hrest⟩
      iexists ns
      iframe
      iframe #
      isplit
      · iintro %sl' Hsl'
        iapply BigSepM.bigSepM_insert_delete.2
        iframe
      · iintro Hsl'
        iapply (BigSepM.bigSepM_delete hC).2
        iframe
  icases Hsl with ⟨%ns, Hns, Hcap, #Hcn, Hback⟩
  ihave %Hlns := ownSlice_len $$ Hns
  (try wp_auto)
  ihave HJ : (∃ (j : w64) (cv : Loc), "i" ∷ i_ptr ↦ j ∗ "c" ∷ c_ptr ↦ cv ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j⌝ : IProp GF) $$ [i c]
  · iexists W64 0, _
    iframe
    ipureintro; word
  wp_for HJ
  wp_if_destruct
  · have Hb' := And.intro Hj Hif
    list_elem ns (sint.nat j) as v
    simp only [Hb', _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index _ (sint.Z j) ns _ v Hj $$ [Hns] as Hns
    · isplit
      · iexact Hns
      · ipureintro; exact Hv_lookup
    ihave #Hcv := BigSepL.bigSepL_lookup Hv_lookup $$ Hcn
    iunfold canonNode at Hcv
    icases Hcv with ⟨%hn, #Hvp, %Hk, %s', #Hs'⟩
    iStructNamed Hvp
    (try wp_auto)
    wp_apply wp_storeEqual hn.st' st s' s $$ [$Hs' $Hst]
    wp_if_destruct
    · (try wp_auto)
      wp_for_post
      (try wp_auto)
      iapply HΦ
      isplitl [Hc Hi HC HI Hg Hgs Hns Hcap Hback]
      · iunfold hhInv
        iexists mc', mi', mg, C', I', G
        iframe
        iright
        iframe
        icases Hback with ⟨-, Hb2⟩
        iapply Hb2
        iexists ns
        iframe
        iframe #
      · subst Hif
        simp only at Hk
        iapply (histOwn_snoc v hs s').2
        iexists hn
        isplitr
        · iexact Hvp
        isplitr
        · iexact Hs'
        isplitr
        · ipureintro; rw [Hk.2]; word
        rw [Hk.1]; iexact Hprev
    · wp_for_post
      iframe
      iexists j + W64 1, _
      iframe
      ipureintro; word
  · (try wp_auto)
    wp_apply (wp_map_lookup1 _ _ mc' C' (ikey.mk prev n hv) (DFrac.own 1)) $$ [$HC] as HC
    (try wp_auto)
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %lsl ⟨Hl, -⟩
    simp only [arrayLiteralSize1]
    wp_apply (wp_slice_append _ ns _ _ (DFrac.own 1)) $$ [$Hns $Hcap $Hl] as %sl' ⟨Hns', Hcap', -⟩
    (try wp_auto)
    wp_apply (wp_mapInsert _ mc' C' _ sl') $$ [$HC] as HC
    (try wp_auto)
    wp_apply (wp_mapInsert _ mi' I' _ true) $$ [$HI] as HI
    (try wp_auto)
    ipersist «$r0»
    iapply HΦ
    isplitl [Hc Hi HC HI Hg Hgs Hns' Hcap' Hback]
    · iunfold hhInv
      iexists mc', mi', mg, _, _, G
      iframe
      iright
      iframe
      icases Hback with ⟨Hb1, -⟩
      iapply Hb1
      iexists ns ++ [«$r0_ptr»]
      iframe
      iapply BigSepL.bigSepL_snoc.2
      iframe #
      iunfold canonNode
      iexists _
      isplitr
      · iexact «$r0»
      isplitr
      · ipureintro; exact ⟨rfl, rfl⟩
      iexists s
      iexact Hst
    · iapply (histOwn_snoc «$r0_ptr» hs s).2
      iexists _
      isplitr
      · iexact «$r0»
      isplitr
      · iexact Hst
      isplitr
      · ipureintro; show n = _; word
      iexact Hprev

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
