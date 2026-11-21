/-
**Helpers of `compareWalker.visitListItems`'s proof** (`compareWalker__visitListItemsBody.lean`):
the comparisons of a list of keys one at a time (`LawBMZ`'s, for path elements), the keys of a
prefix, an item's comparison, and the maps of `[]value.Value` the walker indexes the items by.

Prove phase, round 2 (2026-11-21, notes/smd-plan.md).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsBList2M
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsBMapZip

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI Iris.ProgramLogic Iris.ProofMode
open sigs_k8s_io.structured_merge_diff.v7

namespace LawBL2C

/-! ## The comparisons of a list of keys -/

theorem mem_unionAll_map (f : PE → Cmp) (l : List PE) (x : Path) :
    (x ∈ (Cmp.unionAll (l.map f)).removed ↔ ∃ k ∈ l, x ∈ (f k).removed) ∧
    (x ∈ (Cmp.unionAll (l.map f)).modified ↔ ∃ k ∈ l, x ∈ (f k).modified) ∧
    (x ∈ (Cmp.unionAll (l.map f)).added ↔ ∃ k ∈ l, x ∈ (f k).added) := by
  obtain ⟨h1, h2, h3⟩ := LawB.mem_unionAll x (l.map f)
  have conv : ∀ (P : Cmp → Prop), (∃ c, c ∈ l.map f ∧ P c) ↔ ∃ k ∈ l, P (f k) := by
    intro P; constructor
    · rintro ⟨c, hc, hp⟩
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hc
      exact ⟨a, ha, hp⟩
    · rintro ⟨a, ha, hp⟩; exact ⟨_, List.mem_map.2 ⟨a, ha, rfl⟩, hp⟩
  exact ⟨h1.trans (conv _), h2.trans (conv _), h3.trans (conv _)⟩

theorem cmp_union_nil (C : Cmp) (f : PE → Cmp) :
    C.union (Cmp.unionAll (([] : List PE).map f)) = C := by
  obtain ⟨r, m, a⟩ := C
  simp only [List.map_nil, Cmp.unionAll, List.foldr_nil, Cmp.none, Cmp.union, LawB.ps_union_empty]

/-- One more key's comparison. -/
theorem unionAll_snoc (C : Cmp) (f : PE → Cmp) (done : List PE) (k : PE) :
    (C.union (Cmp.unionAll (done.map f))).union (f k) =
      C.union (Cmp.unionAll ((done ++ [k]).map f)) := by
  apply LawBMZ.cmp_ext
  intro x
  obtain ⟨a1, a2, a3⟩ := LawBMZ.mem_cmp_union (C.union (Cmp.unionAll (done.map f))) (f k) x
  obtain ⟨b1, b2, b3⟩ := LawBMZ.mem_cmp_union C (Cmp.unionAll (done.map f)) x
  obtain ⟨c1, c2, c3⟩ := LawBMZ.mem_cmp_union C (Cmp.unionAll ((done ++ [k]).map f)) x
  obtain ⟨d1, d2, d3⟩ := mem_unionAll_map f done x
  obtain ⟨e1, e2, e3⟩ := mem_unionAll_map f (done ++ [k]) x
  rw [a1, a2, a3, b1, b2, b3, c1, c2, c3, d1, d2, d3, e1, e2, e3]
  simp only [List.mem_append, List.mem_singleton, _root_.or_and_right, exists_or,
    exists_eq_left, _root_.or_assoc, iff_self, and_self]

/-- The comparisons of fewer keys have no more paths. -/
theorem cardLt_keys (C : Cmp) (f : PE → Cmp) (l1 l2 : List PE)
    (hsub : ∀ k ∈ l1, k ∈ l2) (n : Nat)
    (h : (C.union (Cmp.unionAll (l2.map f))).removed.CardLt n ∧
      (C.union (Cmp.unionAll (l2.map f))).modified.CardLt n ∧
      (C.union (Cmp.unionAll (l2.map f))).added.CardLt n) :
    (C.union (Cmp.unionAll (l1.map f))).removed.CardLt n ∧
      (C.union (Cmp.unionAll (l1.map f))).modified.CardLt n ∧
      (C.union (Cmp.unionAll (l1.map f))).added.CardLt n := by
  refine ⟨LawA3.cardLt_sub _ _ _ (fun x hx => ?_) h.1, LawA3.cardLt_sub _ _ _ (fun x hx => ?_) h.2.1,
    LawA3.cardLt_sub _ _ _ (fun x hx => ?_) h.2.2⟩
  · rw [(LawBMZ.mem_cmp_union _ _ x).1, (mem_unionAll_map f _ x).1] at hx ⊢
    rcases hx with hx | ⟨k, hk, hx⟩
    · exact Or.inl hx
    · exact Or.inr ⟨k, hsub k hk, hx⟩
  · rw [(LawBMZ.mem_cmp_union _ _ x).2.1, (mem_unionAll_map f _ x).2.1] at hx ⊢
    rcases hx with hx | ⟨k, hk, hx⟩
    · exact Or.inl hx
    · exact Or.inr ⟨k, hsub k hk, hx⟩
  · rw [(LawBMZ.mem_cmp_union _ _ x).2.2, (mem_unionAll_map f _ x).2.2] at hx ⊢
    rcases hx with hx | ⟨k, hk, hx⟩
    · exact Or.inl hx
    · exact Or.inr ⟨k, hsub k hk, hx⟩

/-! ## Keys and items -/

/-- The keys of a prefix (every item keyed). -/
theorem keysOf_take (ks : List GoString) : ∀ (vs : List UVal), (∀ v ∈ vs, (keyOf ks v).isSome) →
    ∀ j, keysOf ks (vs.take j) = (keysOf ks vs).take j
  | [], _, j => by simp [keysOf]
  | v :: vs, h, j => by
    obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 (h v List.mem_cons_self)
    have ih := keysOf_take ks vs (fun w hw => h w (List.mem_cons_of_mem _ hw))
    rcases j with _ | j
    · simp [keysOf]
    · have e1 : keysOf ks (v :: vs) = k :: keysOf ks vs := by simp [keysOf, List.filterMap_cons, hk]
      have e2 : keysOf ks ((v :: vs).take (j + 1)) = k :: keysOf ks (vs.take j) := by
        simp [keysOf, List.filterMap_cons, hk]
      rw [e1, e2, ih j]; rfl

end LawBL2C

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

namespace LawBL2C

/-- An item's comparison is `cmpO` (enough fuel). -/
theorem cmpF_item (S : Schema) (e : TypeRef) (ks : List GoString) (ls rs : List UVal) (p : Path)
    (k : PE) :
    cmpF (fuelL ls rs) S e p (itemOf ks ls k) (itemOf ks rs k) =
      cmpO S e p (itemOf ks ls k) (itemOf ks rs k) := by
  apply cmpF_fuel_law_holds
  have h1 := LawBL2.sizeO_itemOf ks ls k
  have h2 := LawBL2.sizeO_itemOf ks rs k
  unfold fuelO fuelL; omega

/-- **`slMapRep f M`**: a `PathElementMap` of `[]value.Value` (the compare walker's `lValues`,
`rValues`) holds, for each key with an item `x` (`f`), a one-element slice of a value of `x`. -/
def slMapRep (f : PE → Option UVal) (M : PEMap GoInterface) : IProp GF :=
  iprop(∀ k, match f k, M k with
    | none, none => iprop(True)
    | some x, some i => iprop(∃ (sl : GoSlice) (v : value.Value),
        ⌜i = interface.mkOk (go.GoType.SliceType value.Value.ty) #sl⌝ ∗ sl ↦*□ [v] ∗ isVal v x)
    | _, _ => iprop(False))

theorem slMapRep_box (f : PE → Option UVal) (M : PEMap GoInterface) :
    slMapRep (GF := GF) f M ⊢ □ slMapRep f M := by
  unfold slMapRep
  haveI hp : ∀ k, Persistent (match f k, M k with
      | none, none => iprop(True)
      | some x, some i => iprop(∃ (sl : GoSlice) (v : value.Value),
          ⌜i = interface.mkOk (go.GoType.SliceType value.Value.ty) #sl⌝ ∗ sl ↦*□ [v] ∗ isVal (GF := GF) v x)
      | _, _ => iprop(False)) := by
    intro k; cases f k <;> cases M k <;> infer_instance
  refine (forall_mono fun k => (hp k).persistent).trans ?_
  refine persistently_forall.mpr.trans ?_
  exact intuitionistically_iff_persistently.mpr

theorem slMapRep_empty : ⊢ slMapRep (GF := GF) (fun _ => none) PEMap.empty := by
  unfold slMapRep
  iintro %k
  simp only [PEMap.empty]
  ipureintro; trivial

theorem slMapRep_isSome (f : PE → Option UVal) (M : PEMap GoInterface) (k : PE) :
    slMapRep (GF := GF) f M ⊢ ⌜(M k).isSome = (f k).isSome⌝ := by
  unfold slMapRep
  iintro H
  ispecialize H $$ %k
  cases f k <;> cases M k <;> simp only
  all_goals first | (ipureintro; rfl) | (iexfalso; iexact H)

theorem slMapRep_some (f : PE → Option UVal) (M : PEMap GoInterface) (k : PE) (x : UVal)
    (h : f k = some x) :
    slMapRep (GF := GF) f M ⊢ ∃ (sl : GoSlice) (v : value.Value),
      ⌜M k = some (interface.mkOk (go.GoType.SliceType value.Value.ty) #sl)⌝ ∗ sl ↦*□ [v] ∗ isVal v x := by
  unfold slMapRep
  iintro H
  ispecialize H $$ %k
  rw [h]
  cases M k <;> simp only
  · iexfalso; iexact H
  · icases H with ⟨%sl, %v, %hi, Hs, Hv⟩
    iexists sl, v
    subst hi
    iframe
    ipureintro; rfl

/-- A new key's slice. -/
theorem slMapRep_insert (f f' : PE → Option UVal) (M : PEMap GoInterface) (k : PE) (x : UVal)
    (sl : GoSlice) (v : value.Value) (hk : f' k = some x) (hne : ∀ k', k' ≠ k → f' k' = f k') :
    slMapRep (GF := GF) f M ∗ sl ↦*□ [v] ∗ isVal v x ⊢
      slMapRep f' (M.insert k (interface.mkOk (go.GoType.SliceType value.Value.ty) #sl)) := by
  unfold slMapRep
  iintro ⟨H, #Hs, #Hv⟩
  iintro %k'
  by_cases h : k' = k
  · subst h
    simp only [PEMap.insert, if_pos, hk]
    iexists sl, v
    iframe #
    ipureintro; rfl
  · simp only [PEMap.insert, if_neg h, hne k' h]
    iapply H

/-- **`slotRep sl o`**: a `[]value.Value` the walker took from its map for one key: empty when
the side lacks the key (`o = none`), else one value of the item. -/
def slotRep (sl : GoSlice) : Option UVal → IProp GF
  | none => iprop(⌜sint.Z sl.len = 0⌝)
  | some x => iprop(∃ v : value.Value, sl ↦*□ [v] ∗ isVal v x)

instance slotRep_persistent (sl : GoSlice) (o : Option UVal) : Persistent (slotRep (GF := GF) sl o) := by
  cases o <;> unfold slotRep <;> infer_instance

theorem slotRep_len (sl : GoSlice) (o : Option UVal) :
    slotRep (GF := GF) sl o ⊢ ⌜sint.Z sl.len ≤ 1 ∧ (sint.Z sl.len = 0 ↔ o = none)⌝ := by
  cases o with
  | none =>
    unfold slotRep; iintro %h; ipureintro; simp [h]
  | some x =>
    unfold slotRep
    iintro ⟨%v, #Hs, -⟩
    ihave %hl := ownSlice_len _ _ _ $$ Hs
    ipureintro
    simp at hl
    have h1 := hl.1; have h2 := hl.2
    constructor
    · word
    · constructor
      · intro h; word
      · intro h; cases h

/-- One more path element. -/
theorem isPEs_snoc (es : List fieldpath.PathElement) (p : Path) (e : fieldpath.PathElement) (k : PE) :
    isPEs (GF := GF) es p ∗ isPE e k ⊢ isPEs (es ++ [e]) (p ++ [k]) := by
  iintro ⟨Hs, He⟩
  ihave %hl := isPEs_length_law_holds _ _ $$ Hs
  iapply (isPEs_app_law_holds es [e] p [k] hl).2
  iframe
  iapply (isPEs_cons_law_holds e [] k []).2
  iframe
  iapply (show iprop(True) ⊢ isPEs (GF := GF) [] [] from isPEs_nil_law_holds)
  ipureintro; trivial

end LawBL2C

end iris

end smd
end EtcdGrove
end Perennial
