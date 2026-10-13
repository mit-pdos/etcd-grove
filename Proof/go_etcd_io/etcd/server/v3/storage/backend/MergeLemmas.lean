/-
Lemmas for the proofs of the bucket buffer's writers (`bucketBuffer.{add,merge,dedupe}`):
`dedupe`'s loop on the pure model (`dedupLast` of a prefix one entry longer), and the slots of a
buffer (`entsIn`, `slotsRO`) under a store into a slot, a drop and the growth of the slice.
Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBuffer

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace backend

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend

/-! ## `dedupLast` of a prefix -/

theorem dedupLast_cons_facts (a : Ent) (l : List Ent) :
    dedupLast (a :: l) ≠ [] ∧ (dedupLast (a :: l)).getLast? = (a :: l).getLast? ∧
      (dedupLast (a :: l)).length ≤ (a :: l).length := by
  induction l generalizing a with
  | nil => simp [dedupLast]
  | cons b rest ih =>
    obtain ⟨h1, h2, h3⟩ := ih b
    rw [dedupLast]
    split
    · refine ⟨h1, ?_, ?_⟩
      · rw [h2, List.getLast?_cons_cons]
      · simp only [List.length_cons] at h3 ⊢; omega
    · refine ⟨by simp, ?_, ?_⟩
      · rw [List.getLast?_cons_cons, ← h2]
        obtain ⟨y, ys, hy⟩ := List.exists_cons_of_ne_nil h1
        rw [hy, List.getLast?_cons_cons]
      · simp only [List.length_cons] at h3 ⊢; omega

/-- `dedupe`'s step: one more entry, compared with the last of the prefix. -/
theorem dedupLast_snoc (a : Ent) (l : List Ent) (e : Ent) :
    dedupLast ((a :: l) ++ [e]) =
      if ((a :: l).getLast (by simp)).1 = e.1 then (dedupLast (a :: l)).dropLast ++ [e]
      else dedupLast (a :: l) ++ [e] := by
  induction l generalizing a with
  | nil =>
    simp only [List.cons_append, List.nil_append, List.getLast_singleton]
    by_cases h : a.1 = e.1 <;> simp [dedupLast, h]
  | cons b rest ih =>
    have ih' := ih b
    obtain ⟨h1, -, -⟩ := dedupLast_cons_facts b rest
    simp only [List.cons_append] at ih' ⊢
    rw [dedupLast, ih', List.getLast_cons_cons]
    conv => rhs; rw [dedupLast]
    by_cases hab : a.1 = b.1
    · simp only [hab, ↓reduceIte]
    · simp only [hab, ↓reduceIte]
      obtain ⟨y, ys, hy⟩ := List.exists_cons_of_ne_nil h1
      split <;> simp [hy, List.dropLast_cons_of_ne_nil]

/-- The loop's state after the prefix of length `r`: some entries, the last being the prefix's
last, at most `r` of them. -/
theorem dedupLast_take_facts (L : List Ent) (r : Nat) (a : Ent) (hr : 0 < r)
    (ha : L[r - 1]? = some a) :
    let D := dedupLast (L.take r)
    1 ≤ D.length ∧ D.length ≤ r ∧ D[D.length - 1]? = some a := by
  intro D
  have hlt : r - 1 < L.length := (List.getElem?_eq_some_iff.1 ha).1
  obtain ⟨y, ys, hy⟩ : ∃ y ys, L.take r = y :: ys := by
    apply List.exists_cons_of_ne_nil
    intro h; rw [List.take_eq_nil_iff] at h
    rcases h with h | h
    · omega
    · subst h; simp at hlt
  have hlen : (L.take r).length = r := by rw [List.length_take]; omega
  obtain ⟨h1, h2, h3⟩ := dedupLast_cons_facts y ys
  simp only [D, hy]
  rw [hy] at hlen
  refine ⟨?_, by omega, ?_⟩
  · cases h : dedupLast (y :: ys) with
    | nil => exact absurd h h1
    | cons _ _ => simp
  · rw [← List.getLast?_eq_getElem?, h2, ← hy, List.getLast?_eq_getElem?, List.getElem?_take]
    rw [List.length_take, ite_eq_left (by omega)]
    rw [show min r L.length - 1 = r - 1 by omega]; exact ha

/-- One more step of `dedupe`'s loop: the entry `b` at `r` replaces the last kept one (`a`, at
`r - 1`) if it has its key, or is kept after it. -/
theorem dedupLast_take_succ (L : List Ent) (r : Nat) (a b : Ent) (hr : 0 < r)
    (ha : L[r - 1]? = some a) (hb : L[r]? = some b) :
    dedupLast (L.take (r + 1)) =
      (dedupLast (L.take r)).take
        (if a.1 = b.1 then (dedupLast (L.take r)).length - 1 else (dedupLast (L.take r)).length)
        ++ [b] := by
  have hlt : r < L.length := (List.getElem?_eq_some_iff.1 hb).1
  rw [List.take_add_one, hb]
  obtain ⟨y, ys, hy⟩ : ∃ y ys, L.take r = y :: ys := by
    apply List.exists_cons_of_ne_nil
    intro h; rw [List.take_eq_nil_iff] at h
    rcases h with h | h
    · omega
    · subst h; simp at hlt
  have hlast : (y :: ys).getLast (by simp) = a := by
    have : (y :: ys).getLast? = some a := by
      rw [← hy, List.getLast?_eq_getElem?, List.getElem?_take, List.length_take, ite_eq_left (by omega),
        show min r L.length - 1 = r - 1 by omega]; exact ha
    rw [List.getLast?_eq_some_getLast (by simp)] at this
    exact Option.some.inj this
  simp only [Option.toList_some, hy]
  rw [dedupLast_snoc, hlast]
  split
  · rw [List.dropLast_eq_take]
  · rw [List.take_length]

theorem dedupLast_take_one (L : List Ent) : dedupLast (L.take 1) = L.take 1 := by
  cases L with
  | nil => rfl
  | cons x _ => simp [dedupLast]

/-! ## Sorted lists -/

/-- `bytes.Compare(a, b) < 0` is `a < b`. -/
theorem compare_neg (a b : GoString) :
    decide (sint.Z (bytes.compareResult a b) < sint.Z (W64 0)) = decide (strLt a b) := by
  apply decide_eq_decide.2
  unfold bytes.compareResult
  by_cases h : go.GoStringLt a b
  · simp only [h, ↓reduceIte, iff_true]; decide
  · simp only [h, ↓reduceIte, iff_false]
    split <;> decide

/-- In a sorted list, an entry is at most a later one. -/
theorem entsSorted_le_of_idx {l : List Ent} (hs : entsSorted l) {i j : Nat} {x y : Ent}
    (hx : l[i]? = some x) (hy : l[j]? = some y) (hij : i ≤ j) : x = y ∨ strLt x.1 y.1 := by
  rcases Nat.eq_or_lt_of_le hij with h | h
  · subst h; rw [hx] at hy; exact Or.inl (Option.some.inj hy)
  · right
    obtain ⟨hi, hx'⟩ := List.getElem?_eq_some_iff.1 hx
    obtain ⟨hj, hy'⟩ := List.getElem?_eq_some_iff.1 hy
    have := List.pairwise_iff_getElem.1 hs i j hi hj h
    rw [hx', hy'] at this
    exact this

/-- Sorted lists, the last of the first below the first of the second: their concatenation is
sorted. -/
theorem entsSorted_append_of_last_lt {es es2 : List Ent} (hs : entsSorted es)
    (hs2 : entsSorted es2) (a b : Ent) (ha : es[es.length - 1]? = some a)
    (hb : es2[0]? = some b) (hlt : strLt a.1 b.1) : entsSorted (es ++ es2) := by
  unfold entsSorted
  rw [List.pairwise_append]
  refine ⟨hs, hs2, ?_⟩
  intro x hx y hy
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hx
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hy
  have hil : i < es.length := (List.getElem?_eq_some_iff.1 hi).1
  have h1 := entsSorted_le_of_idx hs hi ha (by omega)
  have h2 := entsSorted_le_of_idx hs2 hb hj (by omega)
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · subst h1; subst h2; exact hlt
  · subst h1; exact strLt_trans hlt h2
  · subst h2; exact strLt_trans h1 hlt
  · exact strLt_trans (strLt_trans h1 hlt) h2

/-! ## Lists with one slot set -/

theorem take_snoc_getElem? {α : Type} (D : List α) (w k : Nat) (e : α) (hw : w ≤ D.length) :
    (D.take w ++ [e])[k]? = if k < w then D[k]? else if k = w then some e else none := by
  by_cases hk : k < w
  · rw [List.getElem?_append_left (by rw [List.length_take]; omega), List.getElem?_take,
      ite_eq_left hk, ite_eq_left hk]
  · rw [List.getElem?_append_right (by rw [List.length_take]; omega), ite_eq_right hk,
      List.length_take, show min w D.length = w by omega]
    by_cases hkw : k = w
    · subst hkw; simp
    · rw [ite_eq_right hkw, List.getElem?_eq_none (by simp; omega)]

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-! ## The slots of a buffer -/

/-- The slot of the `n`-th entry holds its key and value. -/
theorem entsIn_slot (kvs : List kv) (es : List Ent) (n : Nat) (x : kv) (e : Ent)
    (hx : kvs[n]? = some x) (he : es[n]? = some e) :
    entsIn (GF := GF) kvs es ⊢ x.key' ↦*□ e.1 ∗ x.val' ↦*□ e.2 := by
  unfold entsIn
  iintro ⟨_, H⟩
  have hz : (kvs.zip es)[n]? = some (x, e) := List.getElem?_zip_eq_some.2 ⟨hx, he⟩
  iapply (BigSepL.bigSepL_lookup (Φ := fun _ (y : kv × Ent) =>
    iprop(y.1.key' ↦*□ y.2.1 ∗ y.1.val' ↦*□ y.2.2)) hz) $$ H

/-- Every slot's key and value slices are read-only. -/
theorem slotsRO_slot (kvs : List kv) (n : Nat) (x : kv) (hx : kvs[n]? = some x) :
    slotsRO (GF := GF) kvs ⊢ ∃ (b1 b2 : GoString), x.key' ↦*□ b1 ∗ x.val' ↦*□ b2 := by
  unfold slotsRO
  iintro H
  iapply (BigSepL.bigSepL_lookup (Φ := fun _ (y : kv) =>
    iprop(∃ (b1 b2 : GoString), y.key' ↦*□ b1 ∗ y.val' ↦*□ b2)) hx) $$ H

/-- A big separating conjunction of a persistent predicate holds of a list whose elements are
all elements of the first. -/
theorem bigSepL_of_lookups' {A : Type} (Φ : A → IProp GF) [∀ x, Persistent (Φ x)]
    (l l' : List A) (hl : ∀ (k : Nat) (x : A), l'[k]? = some x → ∃ k' : Nat, l[k']? = some x) :
    ([∗list] x ∈ l, Φ x) ⊢ [∗list] x ∈ l', Φ x := by
  refine (BigSepL.bigSepL_forall_eqv (Φ := fun _ x => Φ x)).1.trans ?_
  refine BIBase.Entails.trans ?_ (BigSepL.bigSepL_forall_eqv (Φ := fun _ x => Φ x)).2
  iintro #H %k %x %hk
  obtain ⟨k', hk'⟩ := hl k x hk
  iapply H $$ %k' %x %hk'

/-- The slots from `n` on hold the entries from `n` on. -/
theorem entsIn_drop (kvs : List kv) (es : List Ent) (n : Nat) :
    entsIn (GF := GF) kvs es ⊢ entsIn (kvs.drop n) (es.drop n) := by
  unfold entsIn
  iintro ⟨%Hle, H⟩
  isplitr
  · ipureintro; simp only [List.length_drop]; omega
  iapply (bigSepL_of_lookups' (fun (z : kv × Ent) =>
    iprop(z.1.key' ↦*□ z.2.1 ∗ z.1.val' ↦*□ z.2.2)) _ _ ?_) $$ H
  intro k z hk
  refine ⟨n + k, ?_⟩
  rw [List.getElem?_zip_eq_some] at hk ⊢
  rw [List.getElem?_drop, List.getElem?_drop] at hk
  exact hk

/-- The slots hold any prefix of their entries. -/
theorem entsIn_take_es (kvs : List kv) (es : List Ent) (n : Nat) :
    entsIn (GF := GF) kvs es ⊢ entsIn kvs (es.take n) := by
  unfold entsIn
  iintro ⟨%Hle, H⟩
  isplitr
  · ipureintro; simp only [List.length_take]; omega
  iapply (bigSepL_of_lookups' (fun (z : kv × Ent) =>
    iprop(z.1.key' ↦*□ z.2.1 ∗ z.1.val' ↦*□ z.2.2)) _ _ ?_) $$ H
  intro k z hk
  refine ⟨k, ?_⟩
  rw [List.getElem?_zip_eq_some] at hk ⊢
  rw [List.getElem?_take] at hk
  split at hk
  · exact hk
  · exact absurd hk.2 (by simp)

/-- More slots after the entries' do not matter. -/
theorem entsIn_append_slots (kvs more : List kv) (es : List Ent) :
    entsIn (GF := GF) kvs es ⊢ entsIn (kvs ++ more) es := by
  unfold entsIn
  iintro ⟨%Hle, H⟩
  isplitr
  · ipureintro; simp only [List.length_append]; omega
  iapply (bigSepL_of_lookups' (fun (z : kv × Ent) =>
    iprop(z.1.key' ↦*□ z.2.1 ∗ z.1.val' ↦*□ z.2.2)) _ _ ?_) $$ H
  intro k z hk
  refine ⟨k, ?_⟩
  rw [List.getElem?_zip_eq_some] at hk ⊢
  have hk2 : k < es.length := (List.getElem?_eq_some_iff.1 hk.2).1
  rw [List.getElem?_append_left (by omega)] at hk
  exact hk

/-- The slot `w` set to one holding `e`: the entries before `w`, then `e`. -/
theorem entsIn_set_snoc (kvs : List kv) (D : List Ent) (w : Nat) (x : kv) (e : Ent)
    (hw : w ≤ D.length) (hwk : w < kvs.length) :
    entsIn (GF := GF) kvs D ∗ (x.key' ↦*□ e.1 ∗ x.val' ↦*□ e.2) ⊢
      entsIn (kvs.set w x) (D.take w ++ [e]) := by
  unfold entsIn
  iintro ⟨⟨%Hle, #H⟩, #Hx⟩
  isplitr
  · ipureintro; simp only [List.length_set, List.length_append, List.length_take,
      List.length_singleton]; omega
  iapply (BigSepL.bigSepL_forall_eqv (Φ := fun _ (z : kv × Ent) =>
    iprop(z.1.key' ↦*□ z.2.1 ∗ z.1.val' ↦*□ z.2.2))).2
  iintro %k %z %hk
  obtain ⟨z1, z2⟩ := z
  rw [List.getElem?_zip_eq_some, take_snoc_getElem? D w k e hw, List.getElem?_set] at hk
  obtain ⟨hk1, hk2⟩ := hk
  by_cases hkw : k < w
  · rw [ite_eq_right (by omega)] at hk1
    rw [ite_eq_left hkw] at hk2
    iapply (BigSepL.bigSepL_lookup (Φ := fun _ (y : kv × Ent) =>
      iprop(y.1.key' ↦*□ y.2.1 ∗ y.1.val' ↦*□ y.2.2))
      (List.getElem?_zip_eq_some.2 ⟨hk1, hk2⟩)) $$ H
  · rw [ite_eq_right hkw] at hk2
    by_cases hkw' : k = w
    · subst hkw'
      rw [ite_eq_left rfl, ite_eq_left hwk] at hk1
      rw [ite_eq_left rfl] at hk2
      cases hk1; cases hk2
      iexact Hx
    · rw [ite_eq_right hkw'] at hk2; cases hk2

/-- The slot `w` set to a read-only one. -/
theorem slotsRO_set (kvs : List kv) (w : Nat) (x : kv) :
    slotsRO (GF := GF) kvs ∗ (∃ (b1 b2 : GoString), x.key' ↦*□ b1 ∗ x.val' ↦*□ b2) ⊢
      slotsRO (kvs.set w x) := by
  unfold slotsRO
  iintro ⟨#H, #Hx⟩
  iapply (BigSepL.bigSepL_forall_eqv (Φ := fun _ (y : kv) =>
    iprop(∃ (b1 b2 : GoString), y.key' ↦*□ b1 ∗ y.val' ↦*□ b2))).2
  iintro %k %y %hk
  rw [List.getElem?_set] at hk
  by_cases hkw : w = k
  · rw [ite_eq_left hkw] at hk
    split at hk
    · cases hk; iexact Hx
    · cases hk
  · rw [ite_eq_right hkw] at hk
    iapply (BigSepL.bigSepL_lookup (Φ := fun _ (y : kv) =>
      iprop(∃ (b1 b2 : GoString), y.key' ↦*□ b1 ∗ y.val' ↦*□ b2)) hk) $$ H

/-- Fresh (zero) slots are read-only: their slices are `nil`. -/
theorem slotsRO_append_zero (kvs : List kv) (n : Nat) :
    slotsRO (GF := GF) kvs ⊢ slotsRO (kvs ++ List.replicate n (zero_val kv)) := by
  unfold slotsRO
  iintro #H
  ihave #Hnil := ownSlice_nil (V := w8) (GF := GF) DFrac.discard
  iapply (BigSepL.bigSepL_append).2
  isplitl
  · iexact H
  iapply (BigSepL.bigSepL_forall_eqv (Φ := fun _ (y : kv) =>
    iprop(∃ (b1 b2 : GoString), y.key' ↦*□ b1 ∗ y.val' ↦*□ b2))).2
  iintro %k %y %hk
  rw [List.getElem?_replicate] at hk
  split at hk
  · cases hk
    iexists [], []
    isplitl
    · iexact Hnil
    · iexact Hnil
  · cases hk

end defs

end backend
end EtcdGrove
end Perennial
