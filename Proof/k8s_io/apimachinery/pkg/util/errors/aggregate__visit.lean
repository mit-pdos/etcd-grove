/-
The proof of `aggregate.visit`'s spec (`Spec/.../util/errors/aggregate__visit.lean`), by induction
on the tree's depth (a nested `aggregate` is visited by the recursive call). Lean-first.
-/
module

public import Spec.k8s_io.apimachinery.pkg.util.errors.aggregate__visit

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace utilerrors

open Iris Iris.BI Iris.ProofMode k8s_io.apimachinery.pkg.util.errors

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.util.errors.Assumptions]

/-- A leaf is no `aggregate` (its method set has no `Errors`, `aggregate`'s has). -/
theorem leaf_ty_ne (ii : GoInterfaceOk) (h : methodSet ii.ty !! go!"Errors" = none) :
    ii.ty ≠ aggregate.ty := by
  intro he
  have h1 := (go.MethodSetIs.method_set_is (t := aggregate.ty) go!"Errors")
  simp only [go.methodSetLookup] at h1
  rw [he] at h
  rw [h] at h1
  simp at h1

/-- A leaf is no `Aggregate` (no `Errors` method). -/
theorem leaf_not_Aggregate (ii : GoInterfaceOk) (h : methodSet ii.ty !! go!"Errors" = none) :
    go.typeSetContains ii.ty Aggregate.ty = false := by
  rw [go.typeSetContains_underlying]
  simp [go.typeSetElemsContains_cons, go.typeSetElemContains, h]

theorem aggregate.visit.wp_at (n : Nat)
    (IHn : ∀ m, m < n → ∀ (sl : GoSlice) (ys : List GoInterface) (f : GoFunc) (I : IProp GF),
      {{ sl ↦*□ ys ∗ ([∗list] y ∈ ys, errTreeN m y) ∗ visitFnOk f I ∗ I }}
        (App (Val #(methods aggregate.ty go!"visit" #sl)) (Val #f))
      {{ RET #false; I }}) :
    ∀ (sl : GoSlice) (ys : List GoInterface) (f : GoFunc) (I : IProp GF),
      {{ sl ↦*□ ys ∗ ([∗list] y ∈ ys, errTreeN n y) ∗ visitFnOk f I ∗ I }}
        (App (Val #(methods aggregate.ty go!"visit" #sl)) (Val #f))
      {{ RET #false; I }} := by
  intro sl ys f I
  wp_start as ⟨#Hs, #Hys, #Hf, HI⟩
  wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  ihave IH : iprop(∃ (k : w64) (ev : GoInterface),
      "i" ∷ i_ptr ↦ k ∗
      "err" ∷ err_ptr ↦ ev ∗
      "HI" ∷ I ∗
      "%Hb" ∷ ⌜0 ≤ sint.Z k ∧ sint.nat k ≤ ys.length⌝) $$ [i err HI]
  · iexists W64 0, _
    iframe
    ipureintro
    refine ⟨by word, by word⟩
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat k < ys.length := by word
    obtain ⟨y, Hy⟩ : ∃ y, ys[(sint.Z k).toNat]? = some y := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hbnd : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z sl.len := ⟨Hb.1, Hif⟩
    simp only [Hbnd, and_self, ↓reduceIte]
    wp_apply wp_load_slice_index sl (sint.Z k) ys DFrac.discard y Hb.1 as -
    · iframe #; ipureintro; exact Hy
    ihave #Hy := BigSepL.bigSepL_lookup Hy $$ Hys
    ihave Hcase : iprop(errLeafOk y ∨ ∃ (m : Nat) (sl' : GoSlice) (ys' : List GoInterface),
        ⌜m < n ∧ y = interface.mkOk aggregate.ty #sl'⌝ ∗ sl' ↦*□ ys' ∗
          [∗list] z ∈ ys', errTreeN m z) $$ [Hy]
    · cases n with
      | zero => simp only [errTreeN]; ileft; iexact Hy
      | succ m =>
        rw [errTreeN]
        icases Hy with (Hl | ⟨%sl', %ys', %he, #Hs', #Hys'⟩)
        · ileft; iexact Hl
        · iright
          iexists m, sl', ys'
          isplitr; · ipureintro; exact ⟨by omega, he⟩
          isplitr; · iexact Hs'
          iexact Hys'
    icases Hcase with (#Hl | ⟨%m, %sl', %ys', %Hm, #Hs', #Hys'⟩)
    · cases y with
      | nil => simp only [errLeafOk]; iexfalso; iexact Hl
      | ok ii =>
        simp only [errLeafOk]
        icases Hl with ⟨#Hok, %hE⟩
        have hne := leaf_ty_ne ii hE
        simp only [hne, ↓reduceIte, decide_false]
        wp_auto
        simp only [leaf_not_Aggregate ii hE]
        wp_auto
        iunfold visitFnOk at Hf
        ihave #Hfe := Hf $$ %(GoInterface.ok ii) []
        · simp only [errLeafOk]
          isplitr
          · iexact Hok
          · ipureintro; exact hE
        wp_apply Hfe $$ [$HI] as HI
        wp_for_post
        iframe
        iexists k + W64 1, _
        iframe
        ipureintro
        refine ⟨by word, by word⟩
    · obtain ⟨Hm, rfl⟩ := Hm
      simp only [interface.mkOk, ↓reduceIte, _root_.decide_true]
      wp_auto
      simp only [method_unfold]
      wp_auto
      have hrec := IHn m Hm sl' ys' f I
      wp_bind (App (Val #(methods aggregate.ty go!"visit" #sl')) (Val #f))
      iapply hrec $$ [HI]
      · iframe #
        iexact HI
      inext
      iintro HI
      wp_auto
      wp_for_post
      iframe
      iexists k + W64 1, GoInterface.ok { ty := aggregate.ty, v := #sl' }
      iframe
      ipureintro
      refine ⟨by word, by word⟩
  · iapply HΦ
    iexact HI

theorem aggregate.visit.wp_proof : aggregate.visit.spec (GF := GF) (hG := hG) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih => exact aggregate.visit.wp_at n (fun m hm => ih m hm)

end proof

end utilerrors
end EtcdGrove
end Perennial
