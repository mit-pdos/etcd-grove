/-
Pure helpers of the reconcile walker's proofs (`reconcileWithSchemaWalker`): `optU` with itself and
with nil, the empty child set's `reconOut`.
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsB
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsB2
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Defs

@[expose] public section

noncomputable section

set_option linter.unusedSimpArgs false

namespace Perennial
namespace EtcdGrove
namespace smd

open sigs_k8s_io.structured_merge_diff.v7

namespace LawB

theorem optU_none_r (x : Option PathSet) : optU x none = x := by cases x <;> rfl

/-- An accumulator unioned with itself is unchanged (as `optU x none`). -/
theorem optU_self (x : Option PathSet) : optU x x = optU x none := by
  have h := optU_idem_law_holds x none
  rw [optU_none_r] at h
  rw [h, optU_none_r]

theorem atomicNodes_empty (S : Schema) (t : TypeRef) :
    (atomicNodes S t PathSet.empty).isEmpty = true := rfl

/-- No child set (nil `fieldSet`) and not touched: nothing to add. -/
theorem reconOut_empty (S : Schema) (t : TypeRef) (p : Path) (b : Bool)
    (h : reconTouch S t b PathSet.empty = false) : reconOut S t p b PathSet.empty = none := by
  rw [reconOut_granular_law_holds S t p b _ h]
  simp [reconBelow, atomicNodes_empty]

/-- A schema in scope never names the reserved `__untyped_deduced_` (a map's element type resolves). -/
theorem find_not_untyped (S : Schema) (hS : S.WF) (n : GoString) (a : Atom) (h : S.find n = some a) :
    n ≠ go!"__untyped_deduced_" := by
  intro hn
  subst hn
  have hm := lkv_mem h
  have hmem : go!"__untyped_deduced_" ∈ S.types.map (·.1) := List.mem_map.2 ⟨_, hm, rfl⟩
  unfold Schema.WF at hS
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hS
  have h2 := hS.1.2
  rw [List.contains_iff_mem.2 hmem] at h2
  exact absurd h2 (by decide)

/-- A map type's element type is never the reserved `__untyped_deduced_` in a schema in scope:
`isUntypedDeducedMap` is false. -/
theorem map_elem_not_untyped (S : Schema) (hS : S.WF) (n : GoString) (fs : List (GoString × TypeRef))
    (e : Option TypeRef) (rel : ElemRel) (h : S.find n = some (.map fs e rel)) :
    e.map (·.name) ≠ some go!"__untyped_deduced_" := by
  rcases e with _ | t
  · simp
  · have hw := find_wf S hS _ _ h
    have hres : S.resolves t = true := by
      simp only [Atom.wf, Bool.and_eq_true] at hw; exact hw.2
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 hres
    simp only [Option.map_some, ne_eq, Option.some.injEq]
    exact find_not_untyped S hS _ _ ha

/-! ## The compare walker's node change (`compare`'s tail) -/

theorem cmp_node_added (C B : Cmp) (p : Path) (r : Option UVal) :
    C.union (B.union (nodeC p none r)) =
      ⟨(C.union B).removed, (C.union B).modified, ((C.union B).added).union (ins p)⟩ := by
  simp only [Cmp.union, nodeC, Cmp.none, PathSet.union, PathSet.empty, fset_union_assoc, fset_union_empty]

theorem cmp_node_removed (C B : Cmp) (p : Path) (x : UVal) :
    C.union (B.union (nodeC p (some x) none)) =
      ⟨((C.union B).removed).union (ins p), (C.union B).modified, (C.union B).added⟩ := by
  simp only [Cmp.union, nodeC, Cmp.none, PathSet.union, PathSet.empty, fset_union_assoc, fset_union_empty]

theorem cmp_node_none (C B : Cmp) (p : Path) (x y : UVal) :
    C.union (B.union (nodeC p (some x) (some y))) = C.union B := by
  simp only [Cmp.union, nodeC, Cmp.none, PathSet.union, PathSet.empty, fset_union_assoc, fset_union_empty]

/-! ## An atomic node's own `reconOut` (`doList`/`doMap`'s granular-to-atomic branch) -/

/-- Nothing below a non-granular node is reached by the walker: no atomic nodes below it. -/
theorem atomicNodes_notGranular (S : Schema) (t : TypeRef) (F : PathSet)
    (h : isGranularT S t = false) : (atomicNodes S t F).isEmpty = true := by
  unfold atomicNodes
  apply fset_filter_false
  intro p
  cases p with
  | nil => rfl
  | cons pe q => simp [reconAt, h]

theorem fset_map_empty {α β : Type} (f : α → β) : FSet.map f FSet.empty = FSet.empty := rfl

/-- An atomic node touched: itself only. -/
theorem reconOut_atomic (S : Schema) (t : TypeRef) (p : Path) (b : Bool) (F : PathSet)
    (h : isGranularT S t = false) (hT : reconTouch S t b F = true) :
    reconOut S t p b F = some (ins p) := by
  unfold reconOut
  rw [fset_isEmpty_eq _ (atomicNodes_notGranular S t F h), hT]
  simp only [Bool.true_or, ↓reduceIte, fset_map_empty]
  exact congrArg some (fset_union_empty _)

/-- An atomic node not touched: nothing. -/
theorem reconOut_atomic_none (S : Schema) (t : TypeRef) (p : Path) (b : Bool) (F : PathSet)
    (h : isGranularT S t = false) (hT : reconTouch S t b F = false) :
    reconOut S t p b F = none := by
  unfold reconOut
  dsimp only
  rw [atomicNodes_notGranular S t F h, hT]
  rfl

theorem dedupL_ne {α : Type} [DecidableEq α] : ∀ (l : List α), l ≠ [] → FSet.dedupL l ≠ []
  | [], h => absurd rfl h
  | x :: xs, _ => by
    unfold FSet.dedupL
    split
    · rename_i hx; exact dedupL_ne xs (List.ne_nil_of_mem hx)
    · simp

/-- A set is non-empty iff it counts at least one. -/
theorem isEmpty_false_iff {α : Type} [DecidableEq α] (s : FSet α) :
    s.isEmpty = false ↔ 0 < s.card := by
  induction s using Quotient.inductionOn with | h l =>
  show (!l.any (fun _ => true)) = false ↔ 0 < (FSet.dedupL l).length
  cases l with
  | nil => simp [FSet.dedupL]
  | cons x xs =>
    simp only [List.any_cons, Bool.true_or, Bool.not_true, true_iff]
    exact List.length_pos_iff.2 (dedupL_ne _ (by simp))

/-! ## `ReconcileFieldSetWithSchema`'s tail: `RecursiveDifference` is `reconcile`'s filter -/

theorem nePrefixes_any (q : Path) (N : PathSet) (hN : [] ∉ N) :
    q.nePrefixes.any (fun r => FSet.mem N r) = N.any (fun p => p.isPrefixOf q) := by
  apply Bool.eq_iff_iff.2
  rw [List.any_eq_true]
  induction N using Quotient.inductionOn with | h ln =>
  change (∃ r, r ∈ q.nePrefixes ∧ r ∈ FSet.ofList ln) ↔ ln.any _ = true
  rw [List.any_eq_true]
  simp only [FSet.mem_ofList']
  have hN' : [] ∉ ln := fun h => hN ((FSet.mem_ofList' ln []).2 h)
  constructor
  · rintro ⟨r, hr, hrN⟩
    refine ⟨r, hrN, ?_⟩
    simp only [Path.nePrefixes, List.mem_map, List.mem_range] at hr
    obtain ⟨k, hk, rfl⟩ := hr
    exact List.isPrefixOf_iff_prefix.2 (List.take_prefix _ _)
  · rintro ⟨p, hpN, hp⟩
    refine ⟨p, ?_, hpN⟩
    have hpp := List.isPrefixOf_iff_prefix.1 hp
    have hne : p ≠ [] := fun h => hN' (h ▸ hpN)
    have hpos : 0 < p.length := List.length_pos_iff.2 hne
    simp only [Path.nePrefixes, List.mem_map, List.mem_range]
    refine ⟨p.length - 1, ?_, ?_⟩
    · have := hpp.length_le; omega
    · rw [Nat.sub_add_cancel hpos]; exact (List.prefix_iff_eq_take.1 hpp).symm

theorem rdiff_eq_filter (s N : PathSet) (hN : [] ∉ N) :
    PathSet.rdiff s N = s.filter (fun q => !N.any (fun p => p.isPrefixOf q)) := by
  unfold PathSet.rdiff
  congr 1
  funext q
  rw [nePrefixes_any q N hN]

/-- The root's accumulators never hold the empty path. -/
theorem reconOut_root_ne (S : Schema) (t : TypeRef) (s N : PathSet)
    (h : reconOut S t [] false s = some N) : [] ∉ N := by
  unfold reconOut at h
  dsimp only at h
  split at h
  · cases h
    intro hm
    rcases (FSet.mem_union' _ _ _).1 hm with hm | hm
    · split at hm
      · rw [ins_nil] at hm; exact absurd hm (by decide)
      · exact absurd hm (by decide)
    · rw [fset_map_append_nil, atomicNodes, FSet.mem_filter'] at hm
      simp at hm
  · cases h

/-- A map type's declared field names are distinct (`Map.FindField`'s premise). -/
theorem map_fields_nodup (S : Schema) (hS : S.WF) (n : GoString) (fs : List (GoString × TypeRef))
    (e : Option TypeRef) (rel : ElemRel) (h : S.find n = some (.map fs e rel)) :
    (fs.map (·.1)).Nodup := by
  have hw := find_wf S hS _ _ h
  simp only [Atom.wf, Bool.and_eq_true, decide_eq_true_eq] at hw
  exact hw.1.1

/-- A length read back as a `w64`: zero iff the list is empty. -/
theorem w64_len_zero {α : Type} (n : w64) (vs : List α) (h : n.toInt = vs.length) :
    n = W64 0 ↔ vs = [] := by
  constructor
  · rintro rfl
    have : vs.length = 0 := by simp at h; omega
    exact List.eq_nil_of_length_eq_zero this
  · rintro rfl
    simp at h
    apply BitVec.eq_of_toInt_eq
    simp [h]

/-- The element relationship's Go name decides atomicity. -/
theorem goName_atomic (rel : ElemRel) : ElemRel.goName rel = go!"atomic" ↔ rel = ElemRel.atomic := by
  cases rel <;> decide


/-- A granular list's compare below the node is its items' (`visitListItems`). -/
theorem cmpBelow_list (S : Schema) (t e : TypeRef) (rel : ElemRel) (ks : List GoString) (p : Path)
    (l r : Option UVal) (hf : S.find t.name = some (.list e rel ks)) (hleaf : leafAt S t l r = false) :
    cmpBelow S t p l r = cmpListOut (fuelL (listItems l) (listItems r)) S e ks p (listItems l) (listItems r) := by
  have hl2 := hleaf
  simp only [leafAt, hf, Bool.or_eq_false_iff, decide_eq_false_iff_not, Bool.and_eq_false_iff] at hl2
  obtain ⟨-, hemp⟩ := hl2
  have hne : ¬((listItems l).isEmpty = true ∧ (listItems r).isEmpty = true) := by
    rintro ⟨h1, h2⟩; rcases hemp with h | h <;> simp_all
  unfold cmpBelow
  rw [hleaf]
  simp only [Bool.false_eq_true, ↓reduceIte, hf, cmpListOut]
  refine map_congr' Cmp.unionAll ?_
  intro pe _
  have := list_child_fuel ks l r pe hne
  exact cmpF_stable _ _ S e _ _ _ (by unfold fuelO at *; omega) this.2

/-- A granular map's compare below the node is its entries' (`visitMapItems`). -/
theorem cmpBelow_map (S : Schema) (t : TypeRef) (fs : List (GoString × TypeRef)) (e : Option TypeRef)
    (rel : ElemRel) (p : Path) (l r : Option UVal) (hf : S.find t.name = some (.map fs e rel))
    (hleaf : leafAt S t l r = false) :
    cmpBelow S t p l r = cmpMapOut (fuelM (mapItems l) (mapItems r)) S fs e p (mapItems l) (mapItems r) := by
  have hl2 := hleaf
  simp only [leafAt, hf, Bool.or_eq_false_iff, decide_eq_false_iff_not, Bool.and_eq_false_iff] at hl2
  obtain ⟨-, hemp⟩ := hl2
  have hne : ¬((mapItems l).isEmpty = true ∧ (mapItems r).isEmpty = true) := by
    rintro ⟨h1, h2⟩; rcases hemp with h | h <;> simp_all
  unfold cmpBelow
  rw [hleaf]
  simp only [Bool.false_eq_true, ↓reduceIte, hf, cmpMapOut]
  refine map_congr' Cmp.unionAll ?_
  rintro ⟨k, a, b⟩ hmem
  have := map_child_fuel l r _ hmem hne
  simp only at this ⊢
  split
  · exact cmpF_stable _ _ S _ _ a b (by unfold fuelO at *; omega) this.2
  · rfl

/-- A count bound on `X ∪ (Y ∪ Z)` bounds `X ∪ Y`. -/
theorem cardLt_union_mid (X Y Z : PathSet) (n : Nat)
    (h : (PathSet.union X (PathSet.union Y Z)).CardLt n) : (PathSet.union X Y).CardLt n := by
  refine FSet_cardLt_mono_law_holds _ _ n n (fun x hx => ?_) (Nat.le_refl n) h
  rcases (FSet.mem_union' _ _ x).1 hx with h1 | h1
  · exact (FSet.mem_union' _ _ x).2 (Or.inl h1)
  · exact (FSet.mem_union' _ _ x).2 (Or.inr ((FSet.mem_union' _ _ x).2 (Or.inl h1)))

/-- The compare bounds at a granular node give the bounds below it. -/
theorem cmp_cardLt_below (C B N : Cmp) (n : Nat) (h1 : (C.union (B.union N)).removed.CardLt n)
    (h2 : (C.union (B.union N)).modified.CardLt n) (h3 : (C.union (B.union N)).added.CardLt n) :
    (C.union B).removed.CardLt n ∧ (C.union B).modified.CardLt n ∧ (C.union B).added.CardLt n :=
  ⟨cardLt_union_mid _ _ _ n h1, cardLt_union_mid _ _ _ n h2, cardLt_union_mid _ _ _ n h3⟩

section wst
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]

/-- A walker state updated with its own `inLeaf`. -/
theorem MWSt.with_inLeaf (st : MWSt) (x : Option UVal) (b : Bool) (h : st.inLeaf = b) :
    { st with out := x, inLeaf := b } = { st with out := x } := by
  cases st; simp only at h; subst h; rfl

theorem CWSt.with_inLeaf (st : CWSt) (b : Bool) (h : st.inLeaf = b) :
    { st with inLeaf := b } = st := by
  cases st; simp only at h; subst h; rfl

end wst

end LawB

end smd
end EtcdGrove
end Perennial
