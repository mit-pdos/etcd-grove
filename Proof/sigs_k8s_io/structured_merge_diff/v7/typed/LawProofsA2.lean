/-
**Helpers of the validating, field-set and removing walkers' loop proofs** (part A2): appending
two empty error lists (`errs = append(errs, v2.validate(...)...)`).

Prove phase, round 2 (2026-11-20, notes/smd-plan.md).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.Walkers
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.Base
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.listUnstructured__Length
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.listUnstructured__Length_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.listUnstructured__AtUsing
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.listUnstructured__AtUsing_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.listUnstructured__At
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.listUnstructured__At_ptr
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.LawProofs
public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofs
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Vocab

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI Iris.ProgramLogic Iris.ProofMode
open sigs_k8s_io.structured_merge_diff.v7

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : typed.Assumptions]

namespace LawA2

/-- A found entry is an entry. -/
theorem lookupKV_mem {α : Type} (k : GoString) (v : α) :
    ∀ (l : List (GoString × α)), lookupKV k l = some v → (k, v) ∈ l
  | [], h => by simp [lookupKV] at h
  | (k', v') :: rest, h => by
    simp only [lookupKV] at h
    split at h
    · cases h; subst_vars; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (lookupKV_mem k v rest h)

/-- `append(errs, more...)` of two empty error lists is an empty error list. -/
theorem wp_append_noErrs (a b : GoSlice) :
    {{ noErrs (GF := GF) a ∗ noErrs b }}
      (App (App (Val #(functions go.append [typed.ValidationErrors.ty])) (Val #a)) (Val #b))
    {{ (r : GoSlice), RET #r; noErrs r }} := by
  iintro %Φ ⟨Ha, Hb⟩ HΦ
  iunfold noErrs at Ha
  iunfold ownErrs at Ha
  iunfold noErrs at Hb
  iunfold ownErrs at Hb
  icases Ha with ⟨Ha, Hac⟩
  icases Hb with ⟨Hb, -⟩
  wp_apply (wp_slice_append (V := typed.ValidationError) a [] b [] (DFrac.own 1))
    $$ [Ha Hac Hb] as %r ⟨Hr, Hrc, -⟩
  · iframe
  iapply HΦ
  unfold noErrs ownErrs
  iframe

/-- An owned local `PathElementSet` lent at half to `Has` (`isPESet` at a half: the other half,
kept, makes the returned set the same value). -/
theorem ownPESet_lend (l : Loc) (v : fieldpath.PathElementSet) (S : FSet PE) :
    l ↦ v ∗ ownPESetV (GF := GF) v S ⊢
      isPESet l (DFrac.own (1 : Qp).half) S ∗
      (isPESet l (DFrac.own (1 : Qp).half) S -∗ ∃ v', l ↦ v' ∗ ownPESetV v' S) := by
  unfold ownPESetV isPESet isPESetV
  iintro ⟨Hl, %es, %xs, Hs, Hcap, Hel, %h⟩
  icases (typedPointsto_half_split l v 1).1 $$ Hl with ⟨Hl1, Hl2⟩
  have hs := (ownSlice_fractional (GF := GF) (V := fieldpath.PathElement) v.members' es).fractional
    (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at hs
  icases hs.1 $$ Hs with ⟨Hs1, Hs2⟩
  isplitl [Hl1 Hs1 Hel]
  · iexists v; iframe; ipureintro; exact h
  · iintro ⟨%v', Hl', %es', %xs', Hs', Hel', %h'⟩
    icombine Hl2 Hl' gives %hv
    subst hv
    icombine Hs2 Hs' gives %he
    subst he
    iexists v
    isplitl [Hl' Hl2]
    · iapply (typedPointsto_half_split l v 1).2; iframe
    iexists es, xs'
    iframe
    isplitl [Hs' Hs2]
    · iapply hs.2; iframe
    ipureintro; exact h'

/-- An item's key is not among the keys before it (the keys of a conforming list are distinct). -/
theorem keyOf_fresh (ks : List GoString) (vs : List UVal) (i : Nat) (x : UVal) (k : PE)
    (hnd : (keysOf ks vs).Nodup) (hx : vs[i]? = some x) (hk : keyOf ks x = some k) :
    k ∉ keysOf ks (vs.take i) := by
  have hsplit : vs = vs.take i ++ x :: vs.drop (i + 1) := by
    have h1 := List.take_append_drop i vs
    have hlt : i < vs.length := by
      rcases Nat.lt_or_ge i vs.length with h | h
      · exact h
      · rw [List.getElem?_eq_none h] at hx; cases hx
    have h2 : vs.drop i = x :: vs.drop (i + 1) := by
      rw [List.drop_eq_getElem_cons hlt]
      rw [List.getElem?_eq_getElem hlt] at hx
      cases hx; rfl
    rw [h2] at h1; exact h1.symm
  rw [hsplit] at hnd
  unfold keysOf at hnd ⊢
  rw [List.filterMap_append, List.filterMap_cons, hk] at hnd
  intro hm
  exact (List.nodup_append.1 hnd).2.2 k hm k List.mem_cons_self rfl

/-- The keys of the first `i + 1` items. -/
theorem keysOf_take_succ (ks : List GoString) (vs : List UVal) (i : Nat) (x : UVal)
    (hx : vs[i]? = some x) :
    keysOf ks (vs.take (i + 1)) = keysOf ks (vs.take i) ++ (keyOf ks x).toList := by
  unfold keysOf
  rw [List.take_add_one, hx, List.filterMap_append]
  cases h : keyOf ks x <;> simp [h]

theorem dedupL_length_le {α : Type} [DecidableEq α] : ∀ l : List α, (FSet.dedupL l).length ≤ l.length
  | [] => by simp [FSet.dedupL]
  | x :: xs => by
    unfold FSet.dedupL
    have := dedupL_length_le xs
    split <;> simp <;> omega

/-- A set whose members are in a list shorter than `n` counts less than `n`. -/
theorem cardLt_of_sub {α : Type} [DecidableEq α] (O : FSet α) (l : List α) (n : Nat)
    (h : ∀ p, p ∈ O → p ∈ l) (hl : l.length < n) : O.CardLt n := by
  unfold FSet.CardLt
  have h1 := FSet.card_le_of_subset O (FSet.ofList l) (fun x hx => (FSet.mem_ofList' _ _).2 (h x hx))
  rw [FSet.card_ofList] at h1
  have := dedupL_length_le l
  omega

theorem keysOf_take_length (ks : List GoString) (vs : List UVal) (j : Nat) :
    (keysOf ks (vs.take j)).length ≤ j := by
  unfold keysOf
  have := List.length_filterMap_le (keyOf ks) (vs.take j)
  have := List.length_take_le j vs
  omega

/-- A list view's `Length`, `AtUsing` and `At`, from the concrete specs of its two dynamic types. -/
theorem isListV_dispatchA
    (hL : value.listUnstructured.Length.spec (GF := GF))
    (hLP : value.listUnstructured.Length_ptr.spec (GF := GF))
    (hA : value.listUnstructured.AtUsing.spec (GF := GF))
    (hAP : value.listUnstructured.AtUsing_ptr.spec (GF := GF))
    (hT : value.listUnstructured.At.spec (GF := GF))
    (hTP : value.listUnstructured.At_ptr.spec (GF := GF))
    (l : value.List') (vs : List UVal) :
    isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.value ∗ isListV l vs ⊢
      ∃ i, ⌜l = .ok i⌝ ∗
        □ ({{ True }} (App (Val #(methods i.ty go!"Length" i.v)) (Val #()))
            {{ (r : w64), RET #r; ⌜r.toInt = vs.length⌝ }}) ∗
        □ (∀ (a : value.Allocator) (n : w64) (x : UVal),
            {{ isAlloc a ∗ ⌜0 ≤ n.toInt ∧ vs[n.toInt.toNat]? = some x⌝ }}
            (App (App (Val #(methods i.ty go!"AtUsing" i.v)) (Val #a)) (Val #n))
            {{ (v : value.Value), RET #v; isAlloc a ∗ isValF v (DFrac.own 1) x }}) ∗
        □ (∀ (n : w64) (x : UVal),
            {{ ⌜0 ≤ n.toInt ∧ vs[n.toInt.toNat]? = some x⌝ }}
            (App (Val #(methods i.ty go!"At" i.v)) (Val #n))
            {{ (v : value.Value), RET #v; isValF v (DFrac.own 1) x }}) := by
  iintro ⟨#Hpkg, Hl⟩
  ihave #Hl := isListV_persistent_law_holds l vs $$ Hl
  ihave %Hc := isListV_concrete_law_holds l vs $$ Hl
  rcases Hc with ⟨sl, rfl⟩ | ⟨p, rfl⟩
  · iexists _
    isplitr
    · ipureintro; rfl
    isplitr
    · imodintro
      iintro %Φ !> - HΦ
      iapply hL sl vs $$ [] [HΦ]
      · iframe #
      · iexact HΦ
    isplitr
    · imodintro
      iintro %a %n %x %Φ !> ⟨Ha, %h⟩ HΦ
      iapply hA sl vs a n x $$ [Ha] [HΦ]
      · iframe; iframe #; ipureintro; exact h
      · iexact HΦ
    · imodintro
      iintro %n %x %Φ !> %h HΦ
      iapply hT sl vs n x $$ [] [HΦ]
      · iframe #; ipureintro; exact h
      · iexact HΦ
  · iexists _
    isplitr
    · ipureintro; rfl
    isplitr
    · imodintro
      iintro %Φ !> - HΦ
      iapply hLP p vs $$ [] [HΦ]
      · iframe #
      · iexact HΦ
    isplitr
    · imodintro
      iintro %a %n %x %Φ !> ⟨Ha, %h⟩ HΦ
      iapply hAP p vs a n x $$ [Ha] [HΦ]
      · iframe; iframe #; ipureintro; exact h
      · iexact HΦ
    · imodintro
      iintro %n %x %Φ !> %h HΦ
      iapply hTP p vs n x $$ [] [HΦ]
      · iframe #; ipureintro; exact h
      · iexact HΦ

end LawA2

end proof

end smd
end EtcdGrove
end Perennial
