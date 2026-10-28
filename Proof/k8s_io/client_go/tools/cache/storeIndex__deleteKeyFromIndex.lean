/-
Proof of `Spec/k8s_io/client_go/tools/cache/storeIndex__deleteKeyFromIndex.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.cache.storeIndex__deleteKeyFromIndex
public import Spec.k8s_io.apimachinery.pkg.util.sets.Set__Delete
public import Proof.k8s_io.apimachinery.pkg.util.sets.PtrMethods
public import Proof.k8s_io.apimachinery.pkg.util.sets.DeleteNamed

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.tools.cache

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

theorem storeIndex.deleteKeyFromIndex.wp_proof
    (wp_Delete : sets.Set.Delete.spec (GF := GF) (hG := hG)) :
    storeIndex.deleteKeyFromIndex.spec (GF := GF) (hG := hG) := by
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
    iapply HΦ
    iexists X
    iunfold ownIxN
    iframe
    ipureintro
    funext w
    unfold viewN
    by_cases hw : w = v
    · subst hw; simp only [hv, ↓reduceIte, Option.map_none, Option.getD_none]
      ext k; simp
    · simp [hw]
  | some e =>
    obtain ⟨s, S⟩ := e
    simp only [Option.map_some, Option.getD_some]
    icases (BigSepM.bigSepM_delete hv) $$ HX with ⟨Hs, HXd⟩
    ihave %hnn := ownMap_not_nil $$ Hs
    simp only [decide_eq_false hnn]
    (try wp_auto)
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %l1 ⟨Hl1, -⟩
    simp only [go.arrayLiteralSize, List.foldl]
    (try wp_auto)
    wp_apply (sets.Set.wp_ptr_Delete_of wp_Delete) $$ [$set $Hs $Hl1] as ⟨Hset, Hs, -⟩
    (try wp_auto)
    wp_apply (wp_map_len_lt (t := k8s_io.apimachinery.pkg.util.sets.Set'.ty go.string)
      s (sets.deleteAll S [key]) _) $$ [$Hs] as ⟨Hs, %hlt⟩
    simp only [sets.deleteAll_cons, sets.deleteAll_nil]
    have hview : ∀ (X' : IxN), (X' !! v).map Prod.snd = some (GMap.delete key S) ∨
        (X' !! v = none ∧ GMap.delete key S = ∅) →
        (∀ w, w ≠ v → X' !! w = X !! w) →
        viewN X' = fun w => if w = v then GMap.delete key (viewN X w) else viewN X w := by
      intro X' h1 h2
      funext w
      unfold viewN
      by_cases hw : w = v
      · subst hw
        simp only [hv, ↓reduceIte, Option.map_some, Option.getD_some]
        rcases h1 with h1 | ⟨h1, h1'⟩
        · rw [h1]; rfl
        · rw [h1, h1']; rfl
      · simp only [hw, ↓reduceIte, h2 w hw]
    by_cases hz : GMap.size (GMap.delete key S) = 0
    · have hz' : W64 (GMap.size (GMap.delete key S)) = W64 0 := by rw [hz]; rfl
      simp only [hz', _root_.decide_true]
      (try wp_auto)
      wp_apply (EtcdGrove.wp_mapDelete_underlying (t := index.ty) l _ v) $$ [$Hl] as Hl
      (try wp_auto)
      iapply HΦ
      iexists GMap.delete v X
      iunfold ownIxN
      isplitl [Hl HXd]
      · have hf : GMap.delete v (GMap.fmap Prod.fst X) = GMap.fmap Prod.fst (GMap.delete v X) := by
          ext w; simp only [GMap.lookup_fmap, GMap.lookup_delete_iff]; split <;> rfl
        rw [hf]; iframe
      · ipureintro
        apply hview
        · right; exact ⟨GMap.lookup_delete _ _, GMap.map_size_empty_inv _ hz⟩
        · intro w hw; exact GMap.lookup_delete_ne _ (Ne.symm hw)
    · have hz' : W64 (GMap.size (GMap.delete key S)) ≠ W64 0 := by
        intro h; apply hz
        simp only [sets.deleteAll_cons, sets.deleteAll_nil] at hlt
        word
      simp only [hz', decide_false]
      (try wp_auto)
      iapply HΦ
      iexists <[v := (s, GMap.delete key S)]> X
      iunfold ownIxN
      isplitl [Hl HXd Hs]
      · have hf : GMap.fmap Prod.fst (<[v := (s, GMap.delete key S)]> X) =
            GMap.fmap Prod.fst X := by
          ext w
          simp only [GMap.lookup_fmap, GMap.lookup_insert_eq_iff]
          split
          · subst_vars; simp [hv]
          · rfl
        rw [hf]
        iframe Hl
        iapply BigSepM.bigSepM_insert_delete.2
        iframe
      · ipureintro
        apply hview
        · left; simp
        · intro w hw; simp [Ne.symm hw]

end proof

end cache
end EtcdGrove
end Perennial
