/-
**Helpers of `mergingWalker.visitListItems`'s proof** (`mergingWalker__visitListItemsBody.lean`):
a list view's `Length` and `AtUsing` (without `At`), path elements by position, the items of a
keyed list by position, the fuel of an item's merge.

Prove phase, round 2 (2026-11-21, notes/smd-plan.md).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsBList2
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsA2
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsB
public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsRep
public import Proof.sigs_k8s_io.structured_merge_diff.v7.LawProofs.Persist

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSimpArgs false

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

namespace LawBL2

/-- The keys of the shared-order pointers (positions in the right side's keys). -/
def shKeys (R : List PE) (idxs : List Nat) : List PE := idxs.filterMap (fun i => R[i]?)

/-- A list view's `Length` and `AtUsing`, from the concrete specs of its two dynamic types. -/
theorem isListV_dispatchU
    (hL : value.listUnstructured.Length.spec (GF := GF))
    (hLP : value.listUnstructured.Length_ptr.spec (GF := GF))
    (hA : value.listUnstructured.AtUsing.spec (GF := GF))
    (hAP : value.listUnstructured.AtUsing_ptr.spec (GF := GF))
    (l : value.List') (vs : List UVal) :
    isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.value ∗ isListV l vs ⊢
      ∃ i, ⌜l = .ok i⌝ ∗
        □ ({{ True }} (App (Val #(methods i.ty go!"Length" i.v)) (Val #()))
            {{ (r : w64), RET #r; ⌜r.toInt = vs.length⌝ }}) ∗
        □ (∀ (a : value.Allocator) (n : w64) (x : UVal),
            {{ isAlloc a ∗ ⌜0 ≤ n.toInt ∧ vs[n.toInt.toNat]? = some x⌝ }}
            (App (App (Val #(methods i.ty go!"AtUsing" i.v)) (Val #a)) (Val #n))
            {{ (v : value.Value), RET #v; isAlloc a ∗ isValF v (DFrac.own 1) x }}) := by
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
    · imodintro
      iintro %a %n %x %Φ !> ⟨Ha, %h⟩ HΦ
      iapply hA sl vs a n x $$ [Ha] [HΦ]
      · iframe; iframe #; ipureintro; exact h
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
    · imodintro
      iintro %a %n %x %Φ !> ⟨Ha, %h⟩ HΦ
      iapply hAP p vs a n x $$ [Ha] [HΦ]
      · iframe; iframe #; ipureintro; exact h
      · iexact HΦ

/-- `indexListPathElements`' map of items is persistent. -/
theorem itemMap_box (f : PE → Option UVal) (M : PEMap value.Value) :
    (∀ k, match f k, M k with
      | none, none => iprop(True)
      | some x, some v => isVal (GF := GF) v x
      | _, _ => iprop(False)) ⊢
    □ (∀ k, match f k, M k with
      | none, none => iprop(True)
      | some x, some v => isVal (GF := GF) v x
      | _, _ => iprop(False)) := by
  haveI hp : ∀ k, Persistent (match f k, M k with
      | none, none => iprop(True)
      | some x, some v => isVal (GF := GF) v x
      | _, _ => iprop(False)) := by
    intro k; cases f k <;> cases M k <;> infer_instance
  refine (forall_mono fun k => (hp k).persistent).trans ?_
  refine persistently_forall.mpr.trans ?_
  exact intuitionistically_iff_persistently.mpr

/-- A key has an entry in the map exactly when it has an item. -/
theorem itemMap_isSome (f : PE → Option UVal) (M : PEMap value.Value) (k : PE) :
    (∀ k, match f k, M k with
      | none, none => iprop(True)
      | some x, some v => isVal (GF := GF) v x
      | _, _ => iprop(False)) ⊢ ⌜(M k).isSome = (f k).isSome⌝ := by
  iintro H
  ispecialize H $$ %k
  cases f k <;> cases M k <;> simp only
  all_goals first | (ipureintro; rfl) | (iexfalso; iexact H)

/-- The entry of a key with an item holds it. -/
theorem itemMap_some (f : PE → Option UVal) (M : PEMap value.Value) (k : PE) (x : UVal)
    (h : f k = some x) :
    (∀ k, match f k, M k with
      | none, none => iprop(True)
      | some x, some v => isVal (GF := GF) v x
      | _, _ => iprop(False)) ⊢ ∃ v, ⌜M k = some v⌝ ∗ isVal v x := by
  iintro H
  ispecialize H $$ %k
  rw [h]
  cases M k <;> simp only
  · iexfalso; iexact H
  · iexists _; iframe; ipureintro; rfl

/-- A persistent slice of pointers without its first element (`s[1:]`). -/
theorem ownSlice_tail_pers (so : GoSlice) (x : Loc) (xs : List Loc) :
    (so ↦*□ (x :: xs) : IProp GF) ⊢ slice.slice so Loc (W64 1) so.len ↦*□ xs := by
  iintro #H
  ihave %Hl := ownSlice_len _ _ _ $$ H
  have h1 : 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) ≤ sint.Z so.len ∧ sint.Z so.len ≤ sint.Z so.len := by
    simp at Hl; refine ⟨by decide, ?_, Int.le_refl _⟩
    have := Hl.1; have := Hl.2; word
  icases (ownSlice_slice (W64 1) so.len so DFrac.discard (x :: xs) h1).1 $$ H with ⟨-, Hm, -⟩
  have hs : subslice (sint.nat (W64 1)) (sint.nat so.len) (x :: xs) = xs := by
    simp at Hl
    have h2 : sint.nat so.len = xs.length + 1 := by have := Hl.1; have := Hl.2; word
    rw [h2, show sint.nat (W64 1) = 1 from rfl]
    simp [subslice]
  rw [hs]
  iexact Hm

/-- A list side is persistent. -/
theorem isListO_box (l : value.List') (o : Option (List UVal)) :
    isListO (GF := GF) l o ⊢ □ isListO l o := by
  rcases o with _ | vs
  · unfold isListO; iintro %h; imodintro; ipureintro; exact h
  · unfold isListO; iintro H
    ihave #H := isListV_persistent_law_holds l vs $$ H
    imodintro; iexact H

/-- A path element of a list of path elements, by position. -/
theorem isPEs_at : ∀ (es : List fieldpath.PathElement) (p : Path),
    isPEs (GF := GF) es p ⊢ □ ∀ (i : Nat) e k, ⌜es[i]? = some e ∧ p[i]? = some k⌝ -∗ isPE e k
  | [], p => by
    iintro -; imodintro; iintro %i %e %k %h; simp at h
  | e0 :: es, [] => by
    iintro H
    ihave %hl := isPEs_length_law_holds _ _ $$ H
    simp at hl
  | e0 :: es, k0 :: p => by
    iintro H
    icases (isPEs_cons_law_holds e0 es k0 p).1 $$ H with ⟨H0, Hs⟩
    ihave #H0 := isPE_persistent_law_holds _ _ $$ H0
    ihave #Hs := isPEs_at es p $$ Hs
    imodintro
    iintro %i %e %k %h
    rcases i with _ | i
    · simp at h; obtain ⟨rfl, rfl⟩ := h; iexact H0
    · simp at h; iapply Hs; ipureintro; exact h

end LawBL2

namespace LawBL2

/-! ## Keyed lists by position -/

theorem keysOf_get (ks : List GoString) : ∀ (vs : List UVal), (∀ v ∈ vs, (keyOf ks v).isSome) →
    (keysOf ks vs).length = vs.length ∧ ∀ (i : Nat) x, vs[i]? = some x → (keysOf ks vs)[i]? = keyOf ks x
  | [], _ => by simp [keysOf]
  | v :: vs, h => by
    obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 (h v List.mem_cons_self)
    obtain ⟨ih1, ih2⟩ := keysOf_get ks vs (fun w hw => h w (List.mem_cons_of_mem _ hw))
    have hc : keysOf ks (v :: vs) = k :: keysOf ks vs := by
      simp [keysOf, List.filterMap_cons, hk]
    rw [hc]
    refine ⟨by simp [ih1], ?_⟩
    intro i x hx
    rcases i with _ | i
    · simp at hx; subst hx; simp [hk]
    · simp at hx ⊢; exact ih2 i x hx

theorem itemOf_at (ks : List GoString) : ∀ (vs : List UVal), (∀ v ∈ vs, (keyOf ks v).isSome) →
    (keysOf ks vs).Nodup → ∀ (i : Nat) x k, vs[i]? = some x → keyOf ks x = some k →
    itemOf ks vs k = some x
  | [], _, _, i, x, k, hx, _ => by simp at hx
  | v :: vs, h, hnd, i, x, k, hx, hk => by
    obtain ⟨k0, hk0⟩ := Option.isSome_iff_exists.1 (h v List.mem_cons_self)
    have hall : ∀ w ∈ vs, (keyOf ks w).isSome := fun w hw => h w (List.mem_cons_of_mem _ hw)
    have hc : keysOf ks (v :: vs) = k0 :: keysOf ks vs := by
      simp [keysOf, List.filterMap_cons, hk0]
    rw [hc] at hnd
    rcases i with _ | i
    · simp at hx; subst hx
      simp [itemOf, List.find?_cons, hk]
    · simp at hx
      have hki : (keysOf ks vs)[i]? = some k := by rw [(keysOf_get ks vs hall).2 i x hx, hk]
      have hne : k0 ≠ k := by
        intro he; subst he
        exact (List.nodup_cons.1 hnd).1 (List.mem_of_getElem? hki)
      have ih := itemOf_at ks vs hall (List.nodup_cons.1 hnd).2 i x k hx hk
      unfold itemOf at ih ⊢
      simp [List.find?_cons, hk0, hne, ih]

theorem itemOf_mem {ks : List GoString} {vs : List UVal} {k : PE} {x : UVal}
    (h : itemOf ks vs k = some x) : x ∈ vs := List.mem_of_find?_eq_some h

theorem sizeO_itemOf (ks : List GoString) (vs : List UVal) (k : PE) :
    sizeO (itemOf ks vs k) ≤ UVal.sizeL vs := by
  cases h : itemOf ks vs k with
  | none => simp [sizeO]
  | some x => simp only [sizeO]; exact LawB.mem_sizeL (itemOf_mem h)

/-- An item's merge is `mergeO` (enough fuel). -/
theorem mergeF_item (S : Schema) (e : TypeRef) (ks : List GoString) (ls rs : List UVal) (k : PE) :
    mergeF (fuelL ls rs) S e (itemOf ks ls k) (itemOf ks rs k) =
      mergeO S e (itemOf ks ls k) (itemOf ks rs k) := by
  apply mergeF_fuel_law_holds
  have h1 := sizeO_itemOf ks ls k
  have h2 := sizeO_itemOf ks rs k
  unfold fuelO fuelL; omega

end LawBL2

namespace LawBL2

/-- An item's merge (`mergeListItem`'s result). -/
def mItem (S : Schema) (e : TypeRef) (ks : List GoString) (ls rs : List UVal) (pe : PE) : Option UVal :=
  mergeO S e (itemOf ks ls pe) (itemOf ks rs pe)

/-- The merged list from the merged order. -/
theorem mergeListOut_eq (S : Schema) (e : TypeRef) (ks : List GoString) (ls rs : List UVal) :
    mergeListOut (fuelL ls rs) S e ks ls rs =
      (let out := (mergeKeys (keysOf ks ls) (keysOf ks rs)).filterMap (mItem S e ks ls rs)
       if out.isEmpty then none else some (.list out)) := by
  unfold mergeListOut
  simp only
  rw [LawB.filterMap_congr_mem _ (fun pe _ => mergeF_item S e ks ls rs pe)]
  rfl

theorem drop_cons {α : Type} (l : List α) (i : Nat) (x : α) (h : l[i]? = some x) :
    l.drop i = x :: l.drop (i + 1) := by
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.1 h
  exact List.drop_eq_getElem_cons hi

theorem drop_nil {α : Type} (l : List α) (i : Nat) (h : l.length ≤ i) : l.drop i = [] :=
  List.drop_eq_nil_of_le h

/-- The done keys' merges, one more. -/
theorem fm_snoc {α β : Type} (f : α → Option β) (d : List α) (a : α) :
    (d ++ [a]).filterMap f = d.filterMap f ++ (f a).toList := by
  cases h : f a <;> simp [List.filterMap_append, h]

end LawBL2

end proof

section pure
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]

namespace LawBL2

/-- The shared-order state: `nextShared` and the rest of `sharedOrder` point at the right side's
path elements at the positions `idxs` (all in range), whose keys are `sh`. -/
def shRep (R : List PE) (base : GoSlice) (nsp : Loc) (sps : List Loc) (sh : List PE) : Prop :=
  ∃ idxs : List Nat, (∀ i ∈ idxs, i < R.length) ∧ shKeys R idxs = sh ∧
    match idxs with
    | [] => nsp = null ∧ sps = []
    | i :: is => nsp = sliceIndexRef fieldpath.PathElement (i : Int) base ∧
        sps = is.map (fun x : Nat => sliceIndexRef fieldpath.PathElement (x : Int) base)

end LawBL2

end pure

end smd
end EtcdGrove
end Perennial
