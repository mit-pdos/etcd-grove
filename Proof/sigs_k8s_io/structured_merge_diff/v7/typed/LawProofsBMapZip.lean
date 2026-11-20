/-
**Helpers of the merge and compare walkers' `visitMapItems`** (part B, map zip): the walkers
visit the union of two maps' keys in any order (`MapZipUsing(Unordered)`), while `mergeMapOut` and
`cmpMapOut` are written over `zipLexical`'s sorted entries. On sorted sides each entry of the zip
is its key's two lookups (`zipLexical_exact`), so both outputs are functions of the keys alone
(`mergeMapOut_eq`, `cmpMapOut_eq`); the merged map is the per-key results over the keys
(`entriesOf`, its lookups `lkv_entriesOf`, sorted), built from a Go map filled in any order
(`isIface_entries`); the comparison's union does not depend on the order (`unionAll_perm`).

Prove phase, round 2 (2026-11-20, notes/smd-plan.md).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsBRecon
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsA3
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.LawProofs
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.LawProofsPure
public import Proof.sigs_k8s_io.structured_merge_diff.v7.LawProofs.Maps

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI Iris.ProgramLogic Iris.ProofMode
open sigs_k8s_io.structured_merge_diff.v7

namespace LawBMZ

/-! ## Lookups in sorted maps and their lexical zip -/

theorem lkv_of_mem_nodup {α : Type} (k : GoString) (v : α) :
    ∀ l : List (GoString × α), (l.map (·.1)).Nodup → (k, v) ∈ l → lookupKV k l = some v
  | [], _, h => by simp at h
  | (k', v') :: rest, hnd, h => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.1 h with he | h
    · cases he; simp [lookupKV]
    · have hk : k' ≠ k := by
        rintro rfl; exact hnd.1 (List.mem_map.2 ⟨_, h, rfl⟩)
      simp [lookupKV, hk, lkv_of_mem_nodup k v rest hnd.2 h]

theorem lkv_sorted_cons_ne {k j : GoString} {a : UVal} {xs : List (GoString × UVal)}
    (hj : gsLt k j = true) : lookupKV j ((k, a) :: xs) = lookupKV j xs := by
  have : k ≠ j := by rintro rfl; rw [LawProofs.gsLt_irrefl] at hj; cases hj
  simp [lookupKV, this]

/-- On sorted sides, each entry of the lexical zip is its key's two lookups. -/
theorem zipLexical_exact : ∀ (n : Nat) (xs ys : List (GoString × UVal)),
    xs.length + ys.length < n → keysSorted xs = true → keysSorted ys = true →
    ∀ e ∈ zipLexical n xs ys, e.2.1 = lookupKV e.1 xs ∧ e.2.2 = lookupKV e.1 ys
  | 0, _, _, h, _, _ => by omega
  | n + 1, [], [], _, _, _ => by simp [zipLexical]
  | n + 1, (k1, a) :: xs, [], _, hx, _ => by
    intro e he
    simp only [zipLexical, List.mem_cons, List.mem_map] at he
    have hnd : (((k1, a) :: xs).map (·.1)).Nodup := ValuePure.keysSorted_nodup _ hx
    rcases he with rfl | ⟨⟨k', a'⟩, hm, rfl⟩
    · simp [lookupKV]
    · exact ⟨(lkv_of_mem_nodup _ _ _ hnd (List.mem_cons_of_mem _ hm)).symm, rfl⟩
  | n + 1, [], (k2, b) :: ys, _, _, hy => by
    intro e he
    simp only [zipLexical, List.mem_cons, List.mem_map] at he
    have hnd : (((k2, b) :: ys).map (·.1)).Nodup := ValuePure.keysSorted_nodup _ hy
    rcases he with rfl | ⟨⟨k', b'⟩, hm, rfl⟩
    · simp [lookupKV]
    · exact ⟨rfl, (lkv_of_mem_nodup _ _ _ hnd (List.mem_cons_of_mem _ hm)).symm⟩
  | n + 1, (k1, a) :: xs, (k2, b) :: ys, h, hx, hy => by
    intro e he
    simp only [List.length_cons] at h
    simp only [zipLexical] at he
    by_cases e12 : k1 = k2
    · subst e12
      simp only [↓reduceIte, List.mem_cons] at he
      rcases he with rfl | he
      · simp [lookupKV]
      · obtain ⟨h1, h2⟩ := zipLexical_exact n xs ys (by omega) (LawProofs.keysSorted_tail hx)
          (LawProofs.keysSorted_tail hy) e he
        have hk : e.1 ∈ kvKeys xs ∨ e.1 ∈ kvKeys ys :=
          (ValuePure.zipLexical_mem e.1 n xs ys (by omega)).1 (List.mem_map.2 ⟨e, he, rfl⟩)
        have hlt : gsLt k1 e.1 = true := by
          rcases hk with hk | hk
          · exact ValuePure.keysSorted_lt_all hx _ hk
          · exact ValuePure.keysSorted_lt_all hy _ hk
        rw [lkv_sorted_cons_ne hlt, lkv_sorted_cons_ne hlt]; exact ⟨h1, h2⟩
    · by_cases hl : gsLt k1 k2 = true
      · simp only [e12, hl, ↓reduceIte, List.mem_cons] at he
        rcases he with rfl | he
        · exact ⟨by simp [lookupKV], (LawProofs.lookupKV_below hy hl).symm⟩
        · obtain ⟨h1, h2⟩ := zipLexical_exact n xs ((k2, b) :: ys) (by simp; omega)
            (LawProofs.keysSorted_tail hx) hy e he
          have hk := (ValuePure.zipLexical_mem e.1 n xs ((k2, b) :: ys) (by simp; omega)).1
            (List.mem_map.2 ⟨e, he, rfl⟩)
          have hlt : gsLt k1 e.1 = true := by
            rcases hk with hk | hk
            · exact ValuePure.keysSorted_lt_all hx _ hk
            · simp only [kvKeys, List.map_cons, List.mem_cons] at hk
              rcases hk with hk | hk
              · rw [hk]; exact hl
              · exact LawProofs.gsLt_trans hl (ValuePure.keysSorted_lt_all hy _ hk)
          rw [lkv_sorted_cons_ne hlt]; exact ⟨h1, h2⟩
      · have hl2 : gsLt k2 k1 = true := by
          cases h2 : gsLt k2 k1
          · exact absurd (LawProofs.gsLt_total (by simpa using hl) h2) e12
          · rfl
        simp only [e12, hl, ↓reduceIte, List.mem_cons, Bool.false_eq_true] at he
        rcases he with rfl | he
        · exact ⟨(LawProofs.lookupKV_below hx hl2).symm, by simp [lookupKV]⟩
        · obtain ⟨h1, h2⟩ := zipLexical_exact n ((k1, a) :: xs) ys (by simp; omega)
            hx (LawProofs.keysSorted_tail hy) e he
          have hk := (ValuePure.zipLexical_mem e.1 n ((k1, a) :: xs) ys (by simp; omega)).1
            (List.mem_map.2 ⟨e, he, rfl⟩)
          have hlt : gsLt k2 e.1 = true := by
            rcases hk with hk | hk
            · simp only [kvKeys, List.map_cons, List.mem_cons] at hk
              rcases hk with hk | hk
              · rw [hk]; exact hl2
              · exact LawProofs.gsLt_trans hl2 (ValuePure.keysSorted_lt_all hx _ hk)
            · exact ValuePure.keysSorted_lt_all hy _ hk
          rw [lkv_sorted_cons_ne hlt]; exact ⟨h1, h2⟩

/-- The keys a zip visits, on the entries' lists. -/
def zkeys (L R : List (GoString × UVal)) : List GoString :=
  (zipLexical (L.length + R.length + 1) L R).map (·.1)

theorem zipKeys_eq (ol or_ : Option (List (GoString × UVal))) :
    zipKeys ol or_ = zkeys (kvsOrEmpty ol) (kvsOrEmpty or_) := rfl

theorem zkeys_sorted (L R : List (GoString × UVal)) (hL : keysSorted L = true)
    (hR : keysSorted R = true) : (zkeys L R).Pairwise (fun a b => gsLt a b = true) :=
  ValuePure.zipLexical_sorted _ L R (by omega) hL hR

/-! ## The merged map, key by key -/

/-- The merged entry of key `k` (the merging walker's `visitMapItem` on its two sides); `none`
if dropped. -/
def resM (S : Schema) (fs : List (GoString × TypeRef)) (e : Option TypeRef)
    (L R : List (GoString × UVal)) (k : GoString) : Option UVal :=
  match fieldType fs e k with
  | some t' => mergeO S t' (lookupKV k L) (lookupKV k R)
  | none => none

/-- The entries `(k, v)` for the keys `ks` with `f k = some v`, in order. -/
def entriesOf (f : GoString → Option UVal) (ks : List GoString) : List (GoString × UVal) :=
  ks.filterMap (fun k => (f k).map (fun v => (k, v)))

theorem lkv_entriesOf (f : GoString → Option UVal) (k : GoString) :
    ∀ ks : List GoString, lookupKV k (entriesOf f ks) = if k ∈ ks then f k else none
  | [] => by simp [entriesOf, lookupKV]
  | k' :: ks => by
    have ih := lkv_entriesOf f k ks
    unfold entriesOf at ih ⊢
    rw [List.filterMap_cons]
    by_cases hk : k' = k
    · subst hk
      cases hf : f k' with
      | none => simp only [Option.map_none, ih, hf, List.mem_cons, true_or, ↓reduceIte, ite_self]
      | some v => simp [lookupKV]
    · have hk' : ¬ k = k' := fun h => hk h.symm
      cases hf : f k' with
      | none => simp only [Option.map_none, ih, List.mem_cons, hk', false_or]
      | some v => simp only [Option.map_some, lookupKV, hk, ↓reduceIte, ih, List.mem_cons, hk',
          false_or]

theorem entriesOf_keys (f : GoString → Option UVal) :
    ∀ ks : List GoString, ((entriesOf f ks).map (·.1)).Sublist ks
  | [] => by simp [entriesOf]
  | k :: ks => by
    have ih := entriesOf_keys f ks
    unfold entriesOf at ih ⊢
    rw [List.filterMap_cons]
    cases f k with
    | none => exact ih.cons k
    | some v => exact ih.cons_cons k

theorem entriesOf_sorted (f : GoString → Option UVal) (ks : List GoString)
    (h : ks.Pairwise (fun a b => gsLt a b = true)) : keysSorted (entriesOf f ks) = true :=
  (LawProofs.keysSorted_iff_pairwise _).2 (List.pairwise_map.1 (h.sublist (entriesOf_keys f ks)))

theorem kvsOf_sorted (kvs : List (GoString × UVal)) (hs : keysSorted kvs = true) :
    kvsOf kvs = kvs := by
  obtain ⟨h1, h2, h3⟩ := LawProofs.kvsOf_facts kvs
  have hnd : (kvs.map (·.1)).Nodup := ValuePure.keysSorted_nodup kvs hs
  apply LawProofs.sorted_ext _ _ h1 hs
  intro j
  cases hl : lookupKV j (kvsOf kvs) with
  | some v => exact (lkv_of_mem_nodup j v kvs hnd (h3 _ (LawProofs.lookupKV_mem' hl))).symm
  | none =>
    have := h2 j
    rw [hl] at this
    cases h' : lookupKV j kvs with
    | none => rfl
    | some _ => rw [h'] at this; cases this

/-- **The merged map is the per-key results over the zip's keys.** -/
theorem mergeMapOut_eq (S : Schema) (fs : List (GoString × TypeRef)) (e : Option TypeRef)
    (L R : List (GoString × UVal)) (hL : keysSorted L = true) (hR : keysSorted R = true) :
    mergeMapOut (fuelM L R) S fs e L R =
      (if (entriesOf (resM S fs e L R) (zkeys L R)).isEmpty then none
       else some (.map (entriesOf (resM S fs e L R) (zkeys L R)))) := by
  unfold mergeMapOut entriesOf zkeys
  simp only [List.filterMap_map]
  rw [LawB.filterMap_congr_mem _ (fun z hz => ?_)]
  obtain ⟨k, a, b⟩ := z
  obtain ⟨ha, hb⟩ := zipLexical_exact _ L R (by omega) hL hR _ hz
  simp only at ha hb
  subst ha hb
  have hs := LawB.zipOk_size (LawB.zipLexical_mem _ _ _ _ hz)
  simp only [Function.comp_apply, resM]
  cases fieldType fs e k with
  | none => rfl
  | some t' =>
    simp only
    rw [mergeF_fuel_law_holds _ S t' _ _ (by unfold fuelO fuelM; simp only at hs; omega)]

/-- The merged entry of a key the zip visits, from `visitMapItem`'s result. -/
theorem resM_eq (S : Schema) (fs : List (GoString × TypeRef)) (e : Option TypeRef)
    (L R : List (GoString × UVal)) (k : GoString) (t' : TypeRef) (ht : fieldType fs e k = some t') :
    resM S fs e L R k = mergeO S t' (lookupKV k L) (lookupKV k R) := by
  simp only [resM, ht]

/-! ## The comparison, key by key -/

/-- The comparison of key `k` (the compare walker's `visitMapItem`). -/
def resC (S : Schema) (fs : List (GoString × TypeRef)) (e : Option TypeRef) (p : Path)
    (L R : List (GoString × UVal)) (k : GoString) : Cmp :=
  match fieldType fs e k with
  | some t' => cmpO S t' (p ++ [.field k]) (lookupKV k L) (lookupKV k R)
  | none => Cmp.none

theorem cmpMapOut_eq (S : Schema) (fs : List (GoString × TypeRef)) (e : Option TypeRef) (p : Path)
    (L R : List (GoString × UVal)) (hL : keysSorted L = true) (hR : keysSorted R = true) :
    cmpMapOut (fuelM L R) S fs e p L R = Cmp.unionAll ((zkeys L R).map (resC S fs e p L R)) := by
  unfold cmpMapOut zkeys
  simp only [List.map_map]
  congr 1
  apply List.map_congr_left
  intro z hz
  obtain ⟨k, a, b⟩ := z
  obtain ⟨ha, hb⟩ := zipLexical_exact _ L R (by omega) hL hR _ hz
  simp only at ha hb
  subst ha hb
  have hs := LawB.zipOk_size (LawB.zipLexical_mem _ _ _ _ hz)
  simp only [Function.comp_apply, resC]
  cases fieldType fs e k with
  | none => rfl
  | some t' =>
    simp only
    rw [cmpF_fuel_law_holds _ S t' _ _ _ (by unfold fuelO fuelM; simp only at hs; omega)]

theorem cmp_ext {a b : Cmp} (h : ∀ x, (x ∈ a.removed ↔ x ∈ b.removed) ∧
    (x ∈ a.modified ↔ x ∈ b.modified) ∧ (x ∈ a.added ↔ x ∈ b.added)) : a = b := by
  obtain ⟨r1, m1, a1⟩ := a
  obtain ⟨r2, m2, a2⟩ := b
  have e1 : r1 = r2 := FSet.ext' (fun x => (h x).1)
  have e2 : m1 = m2 := FSet.ext' (fun x => (h x).2.1)
  have e3 : a1 = a2 := FSet.ext' (fun x => (h x).2.2)
  subst e1 e2 e3; rfl

theorem mem_cmp_union (a b : Cmp) (x : Path) :
    (x ∈ (a.union b).removed ↔ x ∈ a.removed ∨ x ∈ b.removed) ∧
    (x ∈ (a.union b).modified ↔ x ∈ a.modified ∨ x ∈ b.modified) ∧
    (x ∈ (a.union b).added ↔ x ∈ a.added ∨ x ∈ b.added) :=
  ⟨FSet.mem_union' _ _ x, FSet.mem_union' _ _ x, FSet.mem_union' _ _ x⟩

/-- What is in the union of the comparisons of some keys. -/
theorem mem_unionAll_map (f : GoString → Cmp) (l : List GoString) (x : Path) :
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

theorem unionAll_perm (f : GoString → Cmp) {l l' : List GoString} (h : l.Perm l') :
    Cmp.unionAll (l.map f) = Cmp.unionAll (l'.map f) := by
  apply cmp_ext
  intro x
  obtain ⟨a1, a2, a3⟩ := mem_unionAll_map f l x
  obtain ⟨b1, b2, b3⟩ := mem_unionAll_map f l' x
  rw [a1, a2, a3, b1, b2, b3]
  simp only [h.mem_iff, iff_self, and_self]

theorem cmp_union_nil (C : Cmp) (f : GoString → Cmp) :
    C.union (Cmp.unionAll (([] : List GoString).map f)) = C := by
  obtain ⟨r, m, a⟩ := C
  simp only [List.map_nil, Cmp.unionAll, List.foldr_nil, Cmp.none, Cmp.union, LawB.ps_union_empty]

/-- One more key's comparison. -/
theorem unionAll_snoc (C : Cmp) (f : GoString → Cmp) (done : List GoString) (k : GoString) :
    (C.union (Cmp.unionAll (done.map f))).union (f k) =
      C.union (Cmp.unionAll ((done ++ [k]).map f)) := by
  apply cmp_ext
  intro x
  obtain ⟨a1, a2, a3⟩ := mem_cmp_union (C.union (Cmp.unionAll (done.map f))) (f k) x
  obtain ⟨b1, b2, b3⟩ := mem_cmp_union C (Cmp.unionAll (done.map f)) x
  obtain ⟨c1, c2, c3⟩ := mem_cmp_union C (Cmp.unionAll ((done ++ [k]).map f)) x
  obtain ⟨d1, d2, d3⟩ := mem_unionAll_map f done x
  obtain ⟨e1, e2, e3⟩ := mem_unionAll_map f (done ++ [k]) x
  rw [a1, a2, a3, b1, b2, b3, c1, c2, c3, d1, d2, d3, e1, e2, e3]
  simp only [List.mem_append, List.mem_singleton, _root_.or_and_right, exists_or,
    exists_eq_left, _root_.or_assoc, iff_self, and_self]

/-- The comparisons of fewer keys have no more paths. -/
theorem cardLt_keys (C : Cmp) (f : GoString → Cmp) (l1 l2 : List GoString)
    (hsub : ∀ k ∈ l1, k ∈ l2) (n : Nat)
    (h : (C.union (Cmp.unionAll (l2.map f))).removed.CardLt n ∧
      (C.union (Cmp.unionAll (l2.map f))).modified.CardLt n ∧
      (C.union (Cmp.unionAll (l2.map f))).added.CardLt n) :
    (C.union (Cmp.unionAll (l1.map f))).removed.CardLt n ∧
      (C.union (Cmp.unionAll (l1.map f))).modified.CardLt n ∧
      (C.union (Cmp.unionAll (l1.map f))).added.CardLt n := by
  refine ⟨LawA3.cardLt_sub _ _ _ (fun x hx => ?_) h.1, LawA3.cardLt_sub _ _ _ (fun x hx => ?_) h.2.1,
    LawA3.cardLt_sub _ _ _ (fun x hx => ?_) h.2.2⟩
  · rw [(mem_cmp_union _ _ x).1, (mem_unionAll_map f _ x).1] at hx ⊢
    rcases hx with hx | ⟨k, hk, hx⟩
    · exact Or.inl hx
    · exact Or.inr ⟨k, hsub k hk, hx⟩
  · rw [(mem_cmp_union _ _ x).2.1, (mem_unionAll_map f _ x).2.1] at hx ⊢
    rcases hx with hx | ⟨k, hk, hx⟩
    · exact Or.inl hx
    · exact Or.inr ⟨k, hsub k hk, hx⟩
  · rw [(mem_cmp_union _ _ x).2.2, (mem_unionAll_map f _ x).2.2] at hx ⊢
    rcases hx with hx | ⟨k, hk, hx⟩
    · exact Or.inl hx
    · exact Or.inr ⟨k, hsub k hk, hx⟩

/-! ## A key of the zip of two conforming maps -/

theorem mapItems_kvs (o : Option (List (GoString × UVal))) :
    mapItems (o.map UVal.map) = kvsOrEmpty o := by cases o <;> rfl

theorem confO_lookup (S : Schema) (fs : List (GoString × TypeRef)) (em : Option TypeRef)
    (L : List (GoString × UVal))
    (cL : ∀ k v, (k, v) ∈ L → ∃ t', fieldType fs em k = some t' ∧ conforms S t' v)
    (k : GoString) (t' : TypeRef) (ht : fieldType fs em k = some t') :
    confO S t' (lookupKV k L) := by
  cases h : lookupKV k L with
  | none => trivial
  | some v =>
    obtain ⟨t'', h1, h2⟩ := cL k v (LawProofs.lookupKV_mem' h)
    rw [ht] at h1; cases h1
    exact h2

/-- A key of the zip of two maps conforming to a map type: its field type, a side holding it,
both sides conforming to the field type. -/
theorem key_conf (S : Schema) (t : TypeRef) (fs : List (GoString × TypeRef)) (em : Option TypeRef)
    (rel : ElemRel) (hf : S.find t.name = some (.map fs em rel))
    (ol or_ : Option (List (GoString × UVal)))
    (hl : confO S t (ol.map UVal.map)) (hr : confO S t (or_.map UVal.map))
    (k : GoString) (hk : k ∈ zipKeys ol or_) :
    ∃ t', fieldType fs em k = some t' ∧
      ((lookupKV k (kvsOrEmpty ol)).isSome ∨ (lookupKV k (kvsOrEmpty or_)).isSome) ∧
      confO S t' (lookupKV k (kvsOrEmpty ol)) ∧ confO S t' (lookupKV k (kvsOrEmpty or_)) := by
  have hs := (zipKeys_mem_law_holds ol or_ k).1 hk
  have cL := LawB.confO_map S t fs em rel _ hf hl
  have cR := LawB.confO_map S t fs em rel _ hf hr
  rw [mapItems_kvs] at cL cR
  have ht : ∃ t', fieldType fs em k = some t' := by
    rcases hs with h | h
    · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 h
      obtain ⟨t', h1, -⟩ := cL k v (LawProofs.lookupKV_mem' hv)
      exact ⟨t', h1⟩
    · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 h
      obtain ⟨t', h1, -⟩ := cR k v (LawProofs.lookupKV_mem' hv)
      exact ⟨t', h1⟩
  obtain ⟨t', ht⟩ := ht
  exact ⟨t', ht, hs, confO_lookup S fs em _ cL k t' ht, confO_lookup S fs em _ cR k t' ht⟩

end LawBMZ

/-! ## The merged map's interface -/

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

namespace LawBMZ

/-! ## The Go map the merging walker fills, key by key -/

/-- The Go map holds exactly the visited keys with a merged entry. -/
def MInv (M : GMap GoString GoInterface) (done : List GoString) (g : GoString → Option UVal) :
    Prop :=
  ∀ k, (M !! k).isSome = decide (k ∈ done ∧ (g k).isSome)

theorem minv_nil (g : GoString → Option UVal) : MInv ∅ [] g := by
  intro k; simp

theorem minv_none {M : GMap GoString GoInterface} {done : List GoString}
    {g : GoString → Option UVal} {k : GoString} (h : MInv M done g) (hg : g k = none) :
    MInv M (done ++ [k]) g := by
  intro k'
  rw [h k']
  by_cases hk : k' = k
  · subst hk; simp [hg]
  · simp [hk]

theorem minv_some {M : GMap GoString GoInterface} {done : List GoString}
    {g : GoString → Option UVal} {k : GoString} {x : UVal} (i : GoInterface) (h : MInv M done g)
    (hg : g k = some x) : MInv (<[k := i]> M) (done ++ [k]) g := by
  intro k'
  rw [GMap.lookup_insert_eq_iff]
  by_cases hk : k = k'
  · subst hk; simp [hg]
  · have hk' : ¬ k' = k := fun e => hk e.symm
    simp only [hk, ↓reduceIte, h k', List.mem_append, List.mem_singleton, hk', or_false]

theorem minv_final {M : GMap GoString GoInterface} {done ks : List GoString}
    {g : GoString → Option UVal} (h : MInv M done g) (hp : done.Perm ks) (k : GoString) :
    (M !! k).isSome = (lookupKV k (entriesOf g ks)).isSome := by
  rw [h k, lkv_entriesOf]
  simp only [← hp.mem_iff]
  by_cases hk : k ∈ done <;> simp [hk]

theorem minv_empty {M : GMap GoString GoInterface} {done ks : List GoString}
    {g : GoString → Option UVal} (h : MInv M done g) (hp : done.Perm ks) :
    GMap.size M = 0 ↔ (entriesOf g ks).isEmpty := by
  rw [GMap.map_size_empty_iff, ← GMap.lookup_empty_iff]
  constructor
  · intro he
    cases hE : entriesOf g ks with
    | nil => rfl
    | cons kv rest =>
      have h1 : (lookupKV kv.1 (entriesOf g ks)).isSome := by rw [hE]; simp [lookupKV]
      rw [← minv_final h hp, he] at h1
      cases h1
  · intro he k
    have := minv_final h hp k
    have h2 : entriesOf g ks = [] := List.isEmpty_iff.1 he
    rw [h2] at this
    simp only [lookupKV, Option.isSome_none] at this
    exact Option.isSome_eq_false_iff.1 this |> Option.isNone_iff_eq_none.1

/-- A Go map whose keys are those of the sorted entries `kvs`, each holding an interface of its
value (filled in any order), read-only, is an interface holding `.map kvs`. -/
theorem isIface_entries (m : GoMap) (M : GMap GoString GoInterface)
    (kvs : List (GoString × UVal)) (hs : keysSorted kvs = true)
    (hk : ∀ k, (M !! k).isSome = (lookupKV k kvs).isSome) :
    ownMap m DFrac.discard M -∗
    (□ ∀ (k : GoString) (x : UVal), ⌜lookupKV k kvs = some x⌝ -∗
      ∃ i, ⌜M !! k = some i⌝ ∗ isIface (GF := GF) i x) -∗
    isIface (interface.mkOk mapStrIfaceTy #m) (.map kvs) := by
  have hnd : (kvs.map (·.1)).Nodup := ValuePure.keysSorted_nodup kvs hs
  iintro #Hm #H
  rw [show UVal.map kvs = UVal.ofMap kvs by rw [UVal.ofMap, kvsOf_sorted kvs hs]]
  iapply isIface_ofMap_law_holds m M kvs hnd hk $$ Hm
  iapply LawA3.sepL_of_forall
  imodintro
  iintro %kv %hkv
  iapply H $$ %kv.1 %kv.2
  ipureintro; exact lkv_of_mem_nodup _ _ _ hnd hkv

theorem isMapO_sorted (m : value.Map) (o : Option (List (GoString × UVal))) :
    isMapO (GF := GF) m o ⊢ ⌜keysSorted (kvsOrEmpty o) = true⌝ := by
  cases o with
  | none => iintro -; ipureintro; rfl
  | some kvs => exact isMapV_sorted_law_holds m kvs

theorem optValF_isValO (v : value.Value) (o : Option UVal) :
    optValF (GF := GF) v o = isValO v (DFrac.own 1) o := by cases o <;> rfl

end LawBMZ

end iris

end smd
end EtcdGrove
end Perennial
