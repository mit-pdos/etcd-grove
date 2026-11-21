/-
The proof of `aggregate.Error`'s spec (`Spec/.../util/errors/aggregate__Error.lean`), by induction
on the tree's depth (an `aggregate` of one element returns that element's `Error()`, which for a
nested `aggregate` is the recursive call); for several elements, `visit` with a closure that reads
each leaf's `Error()` into a `sets.String` and the result. Lean-first.
-/
module

public import Spec.k8s_io.apimachinery.pkg.util.errors.aggregate__Error
public import Spec.k8s_io.apimachinery.pkg.util.errors.aggregate__visit
public import Spec.k8s_io.apimachinery.pkg.util.sets.New
public import Spec.k8s_io.apimachinery.pkg.util.sets.Set__Has
public import Spec.k8s_io.apimachinery.pkg.util.sets.Set__Insert
public import Proof.k8s_io.apimachinery.pkg.util.sets.StringMethods

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

theorem aggregate.Error.wp_at
    (wp_visit : aggregate.visit.spec (GF := GF) (hG := hG))
    (wp_New : EtcdGrove.sets.New.spec (GF := GF) (hG := hG))
    (wp_Has : EtcdGrove.sets.Set.Has.spec (GF := GF) (hG := hG))
    (wp_Insert : EtcdGrove.sets.Set.Insert.spec (GF := GF) (hG := hG))
    (n : Nat)
    (IHn : ∀ m, m < n → ∀ (sl : GoSlice) (ys : List GoInterface),
      {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.errors ∗
          sl ↦*□ ys ∗ [∗list] y ∈ ys, errTreeN m y }}
        (App (Val #(methods aggregate.ty go!"Error" #sl)) (Val #()))
      {{ (s : GoString), RET #s; True }}) :
    ∀ (sl : GoSlice) (ys : List GoInterface),
      {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.errors ∗
          sl ↦*□ ys ∗ [∗list] y ∈ ys, errTreeN n y }}
        (App (Val #(methods aggregate.ty go!"Error" #sl)) (Val #()))
      {{ (s : GoString), RET #s; True }} := by
  intro sl ys
  wp_start as ⟨#Hs, #Hys⟩
  -- an element's `Error()` returns some string
  ihave #Hel : iprop(□ ∀ y : GoInterface, errTreeN n y -∗ ∃ ii : GoInterfaceOk, ⌜y = .ok ii⌝ ∗
      □ ∀ Φ : val → IProp GF, ▷ (∀ str : GoString, Φ #str) -∗
        WP (App (Val #(methods ii.ty go!"Error" ii.v)) (Val #())) {{ Φ }}) $$ []
  · iintro !> %y #Hy
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
        icases Hl with ⟨#Hok, -⟩
        iexists ii
        isplitr; · ipureintro; rfl
        iapply errOk_wp
        iexact Hok
    · obtain ⟨Hm, rfl⟩ := Hm
      iexists ⟨aggregate.ty, #sl'⟩
      isplitr; · ipureintro; rfl
      iintro !> %Φ HΦ
      have hrec := IHn m Hm sl' ys'
      iapply hrec
      · iframe #
      · inext; iintro %str -; iapply HΦ
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  wp_auto
  wp_if_destruct
  · iapply HΦ; itrivial
  wp_if_destruct
  · obtain ⟨y, Hy⟩ : ∃ y, ys[(sint.Z (W64 0)).toNat]? = some y :=
      ⟨_, List.getElem?_eq_getElem (show (sint.Z (W64 0)).toNat < ys.length by word)⟩
    simp only [show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z sl.len from ⟨by word, by word⟩,
      and_self, ↓reduceIte]
    wp_apply wp_load_slice_index sl (sint.Z (W64 0)) ys DFrac.discard y (by word) as -
    · iframe #; ipureintro; exact Hy
    ihave #Hy := BigSepL.bigSepL_lookup Hy $$ Hys
    ihave ⟨%ii, %hii, #Hw⟩ := Hel $$ %y Hy
    subst hii
    wp_auto
    wp_bind (App (Val #(methods ii.ty go!"Error" ii.v)) (Val #()))
    iapply Hw
    inext
    iintro %str
    wp_auto
    iapply HΦ; itrivial
  wp_apply (sets.wp_NewString_nil_of wp_New) as %m Hm
  rw [method_unfold]
  wp_auto
  wp_apply (wp_visit n sl ys _ iprop(∃ (S : GMap GoString sets.Elem) (r : GoString),
    seenerrs_ptr ↦ (m : k8s_io.apimachinery.pkg.util.sets.String) ∗ m ↦$ S ∗ result_ptr ↦ r))
    $$ [seenerrs Hm result] as ⟨%S, %r, seenerrs, Hm, result⟩
  · isplitr; · iexact Hs
    isplitr; · iexact Hys
    isplitr
    · iunfold visitFnOk
      iintro !> %e #Hl
      iintro !> %Φ' HI HΦ'
      icases HI with ⟨%S, %r, seenerrs, Hm, result⟩
      cases e with
      | nil => simp only [errLeafOk]; iexfalso; iexact Hl
      | ok ii =>
        simp only [errLeafOk]
        icases Hl with ⟨#Hok, -⟩
        ihave #Hw := errOk_wp ii $$ Hok
        wp_auto
        wp_bind (App (Val #(methods ii.ty go!"Error" ii.v)) (Val #()))
        iapply Hw
        inext
        iintro %msg
        wp_auto
        wp_apply (sets.String.wp_ptr_Has_of wp_Has seenerrs_ptr (DFrac.own 1) m (DFrac.own 1) S msg)
          $$ [$seenerrs $Hm] as ⟨seenerrs, Hm⟩
        wp_if_destruct
        · iapply HΦ'
          iexists S, r
          iframe
        · wp_apply wp_slice_literal
          isplitr
          · ipureintro; rfl
          iintro %msl ⟨Hmsl, -⟩
          wp_apply (sets.String.wp_ptr_Insert_of wp_Insert seenerrs_ptr (DFrac.own 1) m S _ (DFrac.own 1) [msg])
            $$ [$seenerrs $Hm $Hmsl] as ⟨seenerrs, Hm, -⟩
          wp_apply wp_map_len (V := sets.Elem) m _ (DFrac.own 1) $$ Hm as Hm
          wp_if_destruct
          · iapply HΦ'
            iexists _, _
            iframe
          · iapply HΦ'
            iexists _, _
            iframe
    · iexists ∅, _
      iframe
  wp_apply wp_map_len (V := sets.Elem) m S (DFrac.own 1) $$ Hm as Hm
  wp_if_destruct
  · iapply HΦ; itrivial
  · iapply HΦ; itrivial

theorem aggregate.Error.wp_proof
    (wp_visit : aggregate.visit.spec (GF := GF) (hG := hG))
    (wp_New : EtcdGrove.sets.New.spec (GF := GF) (hG := hG))
    (wp_Has : EtcdGrove.sets.Set.Has.spec (GF := GF) (hG := hG))
    (wp_Insert : EtcdGrove.sets.Set.Insert.spec (GF := GF) (hG := hG)) :
    aggregate.Error.spec (GF := GF) (hG := hG) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih => exact aggregate.Error.wp_at wp_visit wp_New wp_Has wp_Insert n (fun m hm => ih m hm)

end proof

end utilerrors
end EtcdGrove
end Perennial
