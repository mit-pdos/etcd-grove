module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.ObjList__DeepCopyObject

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode k8sDeep

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- A slice holding a non-empty list is not the nil slice. -/
theorem ownSlice_ne_nil_of_ne (s : GoSlice) (dq : DFrac)
    (vs : List github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj) (hne : vs ≠ []) : (s ↦*{dq} vs : IProp GF) ⊢ ⌜s ≠ slice.nil⌝ := by
  cases vs with
  | nil => exact absurd rfl hne
  | cons v vs =>
    iintro Hs
    icases ownSlice_elem_acc 0 v s dq (v :: vs) (by omega) rfl $$ Hs with ⟨Hv, -⟩
    icases typedPointsto_not_null _ _ _ $$ Hv with %Hn
    ipureintro
    intro h
    subst h
    exact Hn (go.arrayIndexRef_0 _ _)

/-- `Items` as a slice holding its items (none: the nil slice, empty), with the way back. -/
theorem itemsRep_getD (sl : GoSlice) (dq : DFrac)
    (items : Option (List github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj)) :
    itemsRep (GF := GF) dq sl items ⊢ sl ↦*{dq} items.getD [] ∗
      (sl ↦*{dq} items.getD [] -∗ itemsRep dq sl items) := by
  cases items with
  | none =>
    unfold itemsRep
    rw [show (none : Option (List github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj)).getD [] = [] from rfl]
    iintro %h
    subst h
    isplitl []
    · iapply ownSlice_nil
    · iintro -; ipureintro; rfl
  | some xs =>
    unfold itemsRep
    rw [show (some xs).getD [] = xs from rfl]
    iintro ⟨%h, H⟩
    iframe H
    iintro H
    simp only
    iframe H
    ipureintro; exact h

/-- `append([]Obj{}, items...)`: a non-nil slice holding the items (Go's empty literal is not
nil, and a non-empty result holds elements). -/
theorem wp_append_lit (slp : Loc) (hslp : slp ≠ null) (sl : GoSlice) (dq : DFrac)
    (L : List github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj) :
    {{ (slice.mk slp (W64 (go.arrayLiteralSize [])) (W64 (go.arrayLiteralSize [])) ↦*
          ([] : List github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj) ∗
        ownSliceCap github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj
          (slice.mk slp (W64 (go.arrayLiteralSize [])) (W64 (go.arrayLiteralSize []))) (DFrac.own 1) ∗
        sl ↦*{dq} L : IProp GF) }}
      (App (App (Val #(functions go.append [go.GoType.SliceType github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.ty]))
        (Val #(slice.mk slp (W64 (go.arrayLiteralSize [])) (W64 (go.arrayLiteralSize []))))) (Val #sl))
    {{ (s' : GoSlice), RET #s'; ⌜s' ≠ slice.nil⌝ ∗ s' ↦* L ∗ sl ↦*{dq} L }} := by
  wp_start_folded as ⟨Hsl, Hcap, Hs2⟩
  by_cases hL : L = []
  · subst hL
    ihave %Hl2 := ownSlice_len _ _ _ $$ Hs2
    have h0 : go.arrayLiteralSize ([] : List keyed_element) = 0 := rfl
    have hz : sint.Z sl.len = 0 := by
      have h1 := Hl2.1; have h2 := Hl2.2
      simp only [List.length_nil] at h1
      word
    have hz' : sl.len = W64 0 := by word
    iapply wp_slice_append_fits (slice.mk slp (W64 (go.arrayLiteralSize [])) (W64 (go.arrayLiteralSize []))) sl _
      ⟨by simp [h0], Hl2.2⟩ (by simp [h0, hz])
    wp_apply wp_slice_copy_of_len_zero (V := github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj) _ sl
      (by word)
    isplitl []
    · ipureintro; exact isPanic_intoVal _
    imodintro
    iapply HΦ
    have hs : slice.slice (slice.mk slp (W64 (go.arrayLiteralSize [])) (W64 (go.arrayLiteralSize [])))
        github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj (W64 0)
        ((slice.mk slp (W64 (go.arrayLiteralSize [])) (W64 (go.arrayLiteralSize []))).len + sl.len) =
        slice.mk slp (W64 (go.arrayLiteralSize [])) (W64 (go.arrayLiteralSize [])) := by
      simp only [slice.slice, sliceIndexRef, hz', h0]
      rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0]
      congr 1
    rw [hs]
    iframe Hsl Hs2
    ipureintro
    intro h; injection h with h1; exact hslp h1
  · wp_apply wp_slice_append (V := github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj) _ []
      sl L dq $$ [Hsl Hcap Hs2] as %s' ⟨Hs', -, Hs2⟩
    · iframe Hsl Hcap Hs2
    rw [List.nil_append]
    ihave %hne := ownSlice_ne_nil_of_ne _ _ _ hL $$ Hs'
    iapply HΦ
    iframe Hs' Hs2
    ipureintro; exact hne

theorem ObjList.DeepCopyObject.wp_proof :
    ObjList.DeepCopyObject.spec (GF := GF) (hG := hG) := by
  intro p dq sl rv cont rp items rem
  wp_start as ⟨Hp, Hit, Hrem⟩
  icases (typedPointsto_not_null_dup _ _ _) $$ Hp with ⟨Hp, %Hpn⟩
  ihave ⟨Hs2, Hback⟩ := itemsRep_getD sl dq items $$ Hit
  wp_auto
  icases (typedPointsto_not_null_dup _ _ _) $$ c with ⟨c, %Hcn⟩
  iStructNamed c
  irename Items => cI
  irename ResourceVersion => cRV
  irename Continue => cC
  irename RemainingItemCount => cR
  iStructNamed Hp
  wp_bind (App (Val (GoInstruction (CompositeLiteral _))) (Val (LiteralValueV _)))
  iapply wp_slice_literal_nonnull (V := github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj)
    (t := github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.ty) []
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %slp %hslp ⟨Hsl, Hcap⟩
  wp_auto
  wp_apply wp_append_lit slp hslp sl dq (items.getD []) $$ [Hsl Hcap Hs2] as %sl' ⟨%hsl', Hs', Hs2⟩
  · iframe Hsl Hcap Hs2
  ihave Hit := Hback $$ Hs2
  cases rem with
  | none =>
    unfold remRep
    icases Hrem with %hrp
    subst hrp
    rw [decide_eq_true rfl]
    wp_auto
    iapply HΦ
    isplitl [Items ResourceVersion Continue RemainingItemCount]
    · iapply typedPointsto_combine p _ dq Hpn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    iframe Hit
    simp only
    isplitl []
    · ipureintro; trivial
    iexists sl', null
    isplitl [cI cRV cC cR]
    · iapply typedPointsto_combine c_ptr _ _ Hcn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    unfold itemsRep
    simp only
    iframe Hs'
    ipureintro; exact hsl'
  | some n =>
    unfold remRep
    icases (typedPointsto_not_null_dup _ _ _) $$ Hrem with ⟨Hrem, %Hrpn⟩
    rw [decide_eq_false Hrpn]
    wp_auto
    iapply HΦ
    isplitl [Items ResourceVersion Continue RemainingItemCount]
    · iapply typedPointsto_combine p _ dq Hpn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    iframe Hit
    simp only
    isplitl [Hrem]
    · iexact Hrem
    iexists sl', n_ptr
    isplitl [cI cRV cC cR]
    · iapply typedPointsto_combine c_ptr _ _ Hcn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    unfold itemsRep
    simp only
    iframe Hs' n
    ipureintro; exact hsl'

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
