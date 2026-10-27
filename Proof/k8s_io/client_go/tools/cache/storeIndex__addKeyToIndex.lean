/-
Proof of `Spec/k8s_io/client_go/tools/cache/storeIndex__addKeyToIndex.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.cache.storeIndex__addKeyToIndex
public import Spec.k8s_io.apimachinery.pkg.util.sets.Set__Insert
public import Proof.k8s_io.apimachinery.pkg.util.sets.PtrMethods

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.tools.cache

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

theorem storeIndex.addKeyToIndex.wp_proof
    (wp_Insert : sets.Set.Insert.spec (GF := GF) (hG := hG)) :
    storeIndex.addKeyToIndex.spec (GF := GF) (hG := hG) := by
  intro i l X key v
  wp_start as Hown
  iunfold ownIxN at Hown
  icases Hown with ⟨Hl, HX⟩
  ihave #Hsets : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.sets $$ []
  · iPkgInit
  wp_auto
  wp_apply (wp_map_lookup1 go.string (k8s_io.apimachinery.pkg.util.sets.Set'.ty go.string) l _ v)
    $$ [$Hl] as Hl
  cases hv : X !! v with
  | none =>
    simp only [Option.map_none, Option.getD_none]
    (try wp_auto)
    wp_apply (wp_map_make1 (K := GoString) (V := sets.Elem) go.string
      k8s_io.apimachinery.pkg.util.sets.Empty.ty) as %m Hm
    (try wp_auto)
    wp_apply (wp_mapInsert go.string l _ v m) $$ [$Hl] as Hl
    (try wp_auto)
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %l1 ⟨Hl1, -⟩
    simp only [go.arrayLiteralSize, List.foldl]
    (try wp_auto)
    wp_apply (sets.Set.wp_ptr_Insert_of wp_Insert) $$ [$set $Hm $Hl1] as ⟨-, Hm, -⟩
    (try wp_auto)
    iapply HΦ
    iexists <[v := (m, sets.insertAll ∅ [key])]> X
    isplitl [Hl HX Hm]
    · iunfold ownIxN
      rw [GMap.fmap_insert]
      iframe Hl
      iapply (BigSepM.bigSepM_insert hv).2
      iframe
    · ipureintro
      funext w
      unfold viewN
      by_cases hw : w = v
      · subst hw; simp [hv]
      · simp [hw, Ne.symm hw]
  | some e =>
    obtain ⟨s, S⟩ := e
    simp only [Option.map_some, Option.getD_some]
    icases (BigSepM.bigSepM_insert_acc hv) $$ HX with ⟨Hs, HXc⟩
    ihave %hnn := ownMap_not_nil $$ Hs
    simp only [decide_eq_false hnn]
    (try wp_auto)
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %l1 ⟨Hl1, -⟩
    simp only [go.arrayLiteralSize, List.foldl]
    (try wp_auto)
    wp_apply (sets.Set.wp_ptr_Insert_of wp_Insert) $$ [$set $Hs $Hl1] as ⟨-, Hs, -⟩
    (try wp_auto)
    iapply HΦ
    iexists <[v := (s, sets.insertAll S [key])]> X
    isplitl [Hl HXc Hs]
    · iunfold ownIxN
      have hf : GMap.fmap Prod.fst (<[v := (s, sets.insertAll S [key])]> X) =
          GMap.fmap Prod.fst X := by
        ext w
        simp only [GMap.lookup_fmap, GMap.lookup_insert_eq_iff]
        split
        · subst_vars; simp [hv]
        · rfl
      rw [hf]
      iframe Hl
      ispecialize HXc $$ %((s, sets.insertAll S [key]) : Loc × KSet) Hs
      iexact HXc
    · ipureintro
      funext w
      unfold viewN
      by_cases hw : w = v
      · subst hw; simp [hv]
      · simp [hw, Ne.symm hw]

end proof

end cache
end EtcdGrove
end Perennial
