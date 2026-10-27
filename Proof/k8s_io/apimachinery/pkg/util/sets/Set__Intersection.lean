/-
Proof of `Spec/k8s_io/apimachinery/pkg/util/sets/Set__Intersection.lean`. Lean-first.
-/
module

public import Spec.k8s_io.apimachinery.pkg.util.sets.Set__Intersection
public import Spec.k8s_io.apimachinery.pkg.util.sets.New
public import Proof.k8s_io.apimachinery.pkg.util.sets.PtrMethods

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace sets

open Iris Iris.BI Iris.ProofMode k8s_io.apimachinery.pkg.util.sets

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.util.sets.Assumptions]

theorem Set.Intersection.wp_proof (wp_New : New.spec (GF := GF) (hG := hG))
    (wp_Len : Set.Len.spec (GF := GF) (hG := hG)) (wp_Has : Set.Has.spec (GF := GF) (hG := hG))
    (wp_Insert : Set.Insert.spec (GF := GF) (hG := hG)) :
    Set.Intersection.spec (GF := GF) (hG := hG) := by
  intro K _ _ _ _ T _ _ m1 m2 d1 d2 s1 s2
  wp_start as ⟨Hm1, Hm2⟩
  (try wp_auto)
  ihave Hnil := ownSlice_nil (V := K) (DFrac.own 1)
  wp_apply (wp_New (T := T)) $$ [$Hnil] as %r ⟨Hr, -⟩
  (try wp_auto)
  wp_apply (Set.wp_ptr_Len_of (T := T) wp_Len) $$ [$s1 $Hm1] as ⟨s1, Hm1⟩
  wp_apply (Set.wp_ptr_Len_of (T := T) wp_Len) $$ [$s2 $Hm2] as ⟨s2, Hm2⟩
  (try wp_auto)
  -- the two branches only choose which set to walk; the loop is the same with the roles swapped
  wp_bind (If _ _ _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ ∃ (w o : Loc) (dw do' : DFrac)
      (sw so : GMap K Elem), s1_ptr ↦ m1 ∗ s2_ptr ↦ m2 ∗ walk_ptr ↦ w ∗ other_ptr ↦ o ∗ w ↦${dw} sw ∗ o ↦${do'} so ∗
      ((w ↦${dw} sw ∗ o ↦${do'} so) -∗ (m1 ↦${d1} s1 ∗ m2 ↦${d2} s2)))))
    $$ [walk other Hm1 Hm2 s1 s2]
  · wp_if_destruct
    · (try wp_auto)
      isplitr
      · ipureintro; trivial
      iexists m1, m2, d1, d2, s1, s2
      iframe
      iintro ⟨H1, H2⟩; iframe
    · (try wp_auto)
      isplitr
      · ipureintro; trivial
      iexists m2, m1, d2, d1, s2, s1
      iframe
      iintro ⟨H1, H2⟩; iframe
  iintro %v ⟨%hv, %w, %o, %dw, %do', %sw, %so, s1, s2, walk, other, Hw, Ho, Hback⟩
  subst hv
  (try wp_auto)
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (fun (keys : List K) (p : Int) => iprop(∃ (x : K) (rs : GMap K Elem),
      "key" ∷ key_ptr ↦ x ∗ "result" ∷ result_ptr ↦ r ∗ "Hr" ∷ r ↦$ rs ∗
      "other" ∷ other_ptr ↦ o ∗ "Ho" ∷ o ↦${do'} so)) $$ Hw
  iintro %keys -
  isplitl [key result Hr other Ho]
  · iexists _, _
    simp only [named]
    iframe
  isplitr
  · imodintro
    iintro %p %k %e - HP
    iNamed HP
    (try wp_auto)
    wp_apply (Set.wp_ptr_Has_of (T := T) wp_Has) $$ [$other $Ho] as ⟨other, Ho⟩
    cases hk : (so !! k).isSome with
    | true =>
      simp only [_root_.decide_true]
      (try wp_auto)
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %l1 ⟨Hl1, -⟩
      simp only [go.arrayLiteralSize, List.foldl]
      (try wp_auto)
      wp_apply (Set.wp_ptr_Insert_of wp_Insert) $$ [$result $Hr $Hl1] as ⟨result, Hr, -⟩
      (try wp_auto)
      unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists k, _
      simp only [named]
      iframe
    | false =>
      simp only [Bool.false_eq_true, _root_.decide_false]
      (try wp_auto)
      unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists k, _
      simp only [named]
      iframe
  · iintro HP Hw
    iNamed HP
    (try wp_auto)
    iapply HΦ
    iframe
    ispecialize Hback $$ [Hw Ho]
    · iframe
    icases Hback with ⟨H1, H2⟩
    iframe

end proof

end sets
end EtcdGrove
end Perennial
