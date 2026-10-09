/-
etcd's `cache.ringBuffer[T]` (`cache/ringbuffer.go`): the shared vocabulary of
`Spec/newRingBuffer.lean` and `Spec/ringBuffer__*.lean`. Lean-first (no Rocq
counterpart).

The model of a ring buffer is a list `items : List V` of abstract values, oldest first,
for any `V` and any relation `isItem : T' → V → IProp GF` between a Go item (Lean
representation `T'` of the Go type argument `T`) and its model, which must be
persistent where an item is added (`Append`); `revOf : V → w64` is the revision of a
model value. `ownRingBuffer r cap isItem revOf items` (below) says that `r` is a ring of
capacity `cap` holding `items`, with strictly increasing revisions.

The pure part: the slot arithmetic (`ringSlot`), the binary searches' answers
(`ltCount`, `leCount`), and the lemmas the proofs share.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.cache.v3

/-! ## Pure definitions -/

/-- The slot of logical index `i` in a ring of `cap` slots whose oldest item is at
`tail`. -/
abbrev ringSlot (tail : w64) (cap i : Nat) : Nat := (sint.nat tail + i) % cap

/-- The revisions of `items` are strictly increasing (as signed 64-bit integers, which
is how Go compares `int64`s). -/
def RevSorted {V : Type} (revOf : V → w64) (items : List V) : Prop :=
  items.Pairwise (fun a b => sint.Z (revOf a) < sint.Z (revOf b))

/-- The number of items with revision `< pivot`: for sorted revisions, the index of
the first item with revision `≥ pivot` (`items.length` if none), which is what
`findFirstIndexGreaterOrEqual(pivot)` returns. -/
def ltCount {V : Type} (revOf : V → w64) (pivot : w64) (items : List V) : Nat :=
  items.countP (fun v => decide (sint.Z (revOf v) < sint.Z pivot))

/-- The number of items with revision `≤ pivot`: for sorted revisions, one more than
the index of the last item with revision `≤ pivot`, which is what
`findLastIndexLessOrEqual(pivot)` returns (`-1` if none). -/
def leCount {V : Type} (revOf : V → w64) (pivot : w64) (items : List V) : Nat :=
  items.countP (fun v => decide (sint.Z (revOf v) ≤ sint.Z pivot))

/-- The revision of the newest item, `0` if there is none (`PeekLatest`). -/
def latestRev {V : Type} (revOf : V → w64) (items : List V) : w64 :=
  match items.getLast? with
  | some v => revOf v
  | none => W64 0

/-- The revision of the oldest item, `0` if there is none (`PeekOldest`). -/
def oldestRev {V : Type} (revOf : V → w64) (items : List V) : w64 :=
  match items.head? with
  | some v => revOf v
  | none => W64 0

/-- The items `AscendGreaterOrEqual(pivot, _)` visits, in its order: from the first with
revision `≥ pivot` on, ascending. -/
abbrev ascendGeVisited {V : Type} (revOf : V → w64) (pivot : w64) (items : List V) : List V :=
  items.drop (ltCount revOf pivot items)

/-- The items `AscendLessThan(pivot, _)` visits, in its order: those with revision
`< pivot`, ascending. -/
abbrev ascendLtVisited {V : Type} (revOf : V → w64) (pivot : w64) (items : List V) : List V :=
  items.take (ltCount revOf pivot items)

/-- The items `DescendGreaterThan(pivot, _)` visits, in its order: those with revision
`> pivot`, descending. -/
abbrev descendGtVisited {V : Type} (revOf : V → w64) (pivot : w64) (items : List V) :
    List V :=
  (items.drop (leCount revOf pivot items)).reverse

/-- The items `DescendLessOrEqual(pivot, _)` visits, in its order: those with revision
`≤ pivot`, descending. -/
abbrev descendLeVisited {V : Type} (revOf : V → w64) (pivot : w64) (items : List V) :
    List V :=
  (items.take (leCount revOf pivot items)).reverse

/-- What `Append` leaves: the new item at the end, and the oldest one dropped if the
ring was full. -/
def ringAppend {V : Type} (cap : Nat) (items : List V) (v : V) : List V :=
  if items.length < cap then items ++ [v] else items.tail ++ [v]

/-- `Append`'s precondition on the new item: its revision is above the newest one's. -/
def RevAbove {V : Type} (revOf : V → w64) (items : List V) (v : V) : Prop :=
  ∀ last, items.getLast? = some last → sint.Z (revOf last) < sint.Z (revOf v)

/-! ## Sortedness and the searches -/

theorem RevSorted.lt {V : Type} {revOf : V → w64} {items : List V} (h : RevSorted revOf items)
    {i j : Nat} {a b : V} (ha : items[i]? = some a) (hb : items[j]? = some b) (hij : i < j) :
    sint.Z (revOf a) < sint.Z (revOf b) := by
  unfold RevSorted at h
  rw [List.pairwise_iff_getElem] at h
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.1 ha
  obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.1 hb
  exact h i j hi hj hij

/-- A predicate true exactly on the first `k` items holds of `k` of them. -/
theorem countP_eq_of {V : Type} (p : V → Bool) (items : List V) (k : Nat)
    (hk : k ≤ items.length)
    (hlt : ∀ j v, j < k → items[j]? = some v → p v = true)
    (hge : ∀ j v, k ≤ j → items[j]? = some v → p v = false) :
    items.countP p = k := by
  rw [← List.take_append_drop k items, List.countP_append]
  rw [List.countP_eq_length.2, List.countP_eq_zero.2, List.length_take]
  · omega
  · intro a ha
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 ha
    rw [List.getElem?_drop] at hj
    simp [hge _ _ (by omega) hj]
  · intro a ha
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 ha
    rw [List.getElem?_take] at hj
    split at hj
    · exact hlt _ _ (by omega) hj
    · simp at hj

/-- What `findFirstIndexGreaterOrEqual`'s binary search ends with: the items before `k`
are below `pivot`, the others are not. -/
theorem ltCount_eq_of {V : Type} (revOf : V → w64) (pivot : w64) (items : List V) (k : Nat)
    (hk : k ≤ items.length)
    (hlt : ∀ j v, j < k → items[j]? = some v → sint.Z (revOf v) < sint.Z pivot)
    (hge : ∀ j v, k ≤ j → items[j]? = some v → sint.Z pivot ≤ sint.Z (revOf v)) :
    ltCount revOf pivot items = k :=
  countP_eq_of _ items k hk (fun j v h1 h2 => by simp [hlt j v h1 h2])
    (fun j v h1 h2 => by have := hge j v h1 h2; simp; omega)

/-- What `findLastIndexLessOrEqual`'s binary search ends with: the items before `k`
are at most `pivot`, the others are above it. -/
theorem leCount_eq_of {V : Type} (revOf : V → w64) (pivot : w64) (items : List V) (k : Nat)
    (hk : k ≤ items.length)
    (hle : ∀ j v, j < k → items[j]? = some v → sint.Z (revOf v) ≤ sint.Z pivot)
    (hgt : ∀ j v, k ≤ j → items[j]? = some v → sint.Z pivot < sint.Z (revOf v)) :
    leCount revOf pivot items = k :=
  countP_eq_of _ items k hk (fun j v h1 h2 => by simp [hle j v h1 h2])
    (fun j v h1 h2 => by have := hgt j v h1 h2; simp; omega)

theorem ltCount_le {V : Type} (revOf : V → w64) (pivot : w64) (items : List V) :
    ltCount revOf pivot items ≤ items.length := List.countP_le_length

theorem leCount_le {V : Type} (revOf : V → w64) (pivot : w64) (items : List V) :
    leCount revOf pivot items ≤ items.length := List.countP_le_length

/-- `Append` keeps the revisions sorted. -/
theorem RevSorted.ringAppend_of {V : Type} {revOf : V → w64} {items : List V} {v : V}
    (h : RevSorted revOf items) (hv : RevAbove revOf items v) (cap : Nat) :
    RevSorted revOf (ringAppend cap items v) := by
  have hle : ∀ a ∈ items, sint.Z (revOf a) < sint.Z (revOf v) := by
    intro a ha
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 ha
    have hjl : j < items.length := (List.getElem?_eq_some_iff.1 hj).1
    obtain ⟨last, hlast⟩ : ∃ last, items[items.length - 1]? = some last :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hl := hv last (by rw [List.getLast?_eq_getElem?]; exact hlast)
    rcases Nat.lt_or_ge j (items.length - 1) with h1 | h1
    · have := h.lt hj hlast h1; omega
    · have : j = items.length - 1 := by omega
      subst this; rw [hj] at hlast; cases hlast; exact hl
  unfold ringAppend RevSorted at *
  split
  · rw [List.pairwise_append]
    refine ⟨h, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
    rw [List.mem_singleton] at hb; subst hb; exact hle a ha
  · rw [List.pairwise_append]
    refine ⟨h.sublist (List.tail_sublist _), List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
    rw [List.mem_singleton] at hb; subst hb; exact hle a (List.mem_of_mem_tail ha)

/-! ## `Append`'s slots -/

/-- Distinct logical indices below `c` have distinct slots. -/
theorem mod_inj_of_lt (t c i j : Nat) (hi : i < c) (hj : j < c)
    (h : (t + i) % c = (t + j) % c) : i = j := by
  have hc : 0 < c := by omega
  rw [Nat.add_mod t i, Nat.add_mod t j, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at h
  have ha := Nat.mod_lt t hc
  generalize t % c = a at h ha
  have key : ∀ x, x < 2 * c → x % c = if x < c then x else x - c := by
    intro x hx; split
    · exact Nat.mod_eq_of_lt ‹_›
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [key _ (by omega), key _ (by omega)] at h
  split at h <;> split at h <;> omega

/-- Where `Append` leaves each item: the new tail `t'` is `t` unless the ring was full,
then `t + 1`; the new item `v` is in slot `t + n` (the old `head`), every other item in
the slot it had, which is not that one. -/
theorem ringAppend_lookup {V : Type} (t t' cap : Nat) (items : List V) (v : V)
    (hc : 0 < cap) (hn : items.length ≤ cap)
    (ht' : t' = if items.length < cap then t else (t + 1) % cap)
    (i : Nat) (w : V) (hw : (ringAppend cap items v)[i]? = some w) :
    ((t' + i) % cap = (t + items.length) % cap ∧ w = v) ∨
    (∃ j, items[j]? = some w ∧ (t' + i) % cap = (t + j) % cap ∧
      (t + j) % cap ≠ (t + items.length) % cap) := by
  unfold ringAppend at hw
  by_cases hlt : items.length < cap
  · rw [ite_eq_left hlt] at hw ht'
    rw [ht']
    rcases Nat.lt_or_ge i items.length with hi | hi
    · right
      rw [List.getElem?_append_left hi] at hw
      refine ⟨i, hw, rfl, fun h => ?_⟩
      have := mod_inj_of_lt t cap i items.length (by omega) hlt h
      omega
    · left
      rw [List.getElem?_append_right hi, List.getElem?_singleton] at hw
      by_cases h0 : i - items.length = 0
      · rw [ite_eq_left h0] at hw
        refine ⟨by congr 1; omega, by simpa using hw.symm⟩
      · rw [ite_eq_right h0] at hw; simp at hw
  · rw [ite_eq_right hlt] at hw ht'
    rw [ht']
    have hn' : items.length = cap := by omega
    rcases Nat.lt_or_ge i items.tail.length with hi | hi
    · right
      rw [List.getElem?_append_left hi, List.getElem?_tail] at hw
      simp only [List.length_tail] at hi
      refine ⟨i + 1, hw, ?_, fun h => ?_⟩
      · rw [Nat.mod_add_mod]; congr 1; omega
      · rw [hn', Nat.add_mod_right] at h
        have := mod_inj_of_lt t cap (i + 1) 0 (by omega) (by omega) (by simpa using h)
        omega
    · left
      rw [List.getElem?_append_right hi, List.getElem?_singleton] at hw
      simp only [List.length_tail] at hi hw
      by_cases h0 : i - (items.length - 1) = 0
      · rw [ite_eq_left h0] at hw
        refine ⟨?_, by simpa using hw.symm⟩
        rw [Nat.mod_add_mod]; congr 1; omega
      · rw [ite_eq_right h0] at hw; simp at hw

/-! ## Go `int` arithmetic -/

/-- The searches' midpoint `int(uint(left+right) >> 1)`, for `0 ≤ left ≤ right`
(no overflow: `right < 2^62`). -/
theorem mid_sint (l r : w64) (hl : 0 ≤ sint.Z l) (hlr : sint.Z l ≤ sint.Z r)
    (hr : sint.Z r < 2 ^ 62) :
    sint.Z ((l + r) >>> W64 1) = (sint.Z l + sint.Z r) / 2 := by
  word

/-- Go's `%` on `int` (`BitVec.srem`, truncating) of a non-negative by a positive number
is the mathematical remainder. -/
theorem srem_of_nonneg (a b : w64) (ha : 0 ≤ sint.Z a) (hb : 0 < sint.Z b) :
    BitVec.srem a b = W64 (sint.Z a % sint.Z b) := by
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_srem]
  have ha' : a.toInt = sint.Z a := rfl
  have hb' : b.toInt = sint.Z b := rfl
  rw [ha', hb', Int.tmod_eq_emod_of_nonneg ha]
  have h0 : 0 ≤ sint.Z a % sint.Z b := Int.emod_nonneg _ (by omega)
  have h3 : sint.Z a % sint.Z b < sint.Z b := Int.emod_lt_of_pos _ hb
  have : sint.Z b < 2 ^ 63 := by word
  word

/-- `moduloIndex`'s `(index + len) % len`, without overflow. -/
theorem srem_add_len (index len : w64) (cap : Int) (hlen : sint.Z len = cap) (hcap : 0 < cap)
    (h1 : -cap ≤ sint.Z index) (h2 : sint.Z index + cap < 2 ^ 63) :
    BitVec.srem (index + len) len = W64 (sint.Z index % cap) := by
  rw [srem_of_nonneg _ _ (by word) (by omega)]
  have hadd : sint.Z (index + len) = sint.Z index + cap := by word
  rw [hadd, hlen, Int.add_emod_right]

/-- `at`'s index `(tail + i) % len(buffer)` is slot `ringSlot tail cap i`. -/
theorem ringSlot_sint (tail i : w64) (cap : Nat) (hc : 0 < cap) (hc2 : cap ≤ 2 ^ 61)
    (ht : 0 ≤ sint.Z tail ∧ sint.Z tail < cap) (hi : 0 ≤ sint.Z i ∧ sint.Z i < cap) :
    sint.Z (W64 (sint.Z (tail + i) % (cap : Int))) = (ringSlot tail cap (sint.nat i) : Int) := by
  have h1 : sint.Z (tail + i) = ((sint.nat tail + sint.nat i : Nat) : Int) := by word
  rw [h1, ← Int.natCast_emod, ringSlot]
  have : (sint.nat tail + sint.nat i) % cap < cap := Nat.mod_lt _ hc
  generalize (sint.nat tail + sint.nat i) % cap = m at this ⊢
  word

/-- `PeekLatest`'s index `(head - 1 + len(buffer)) % len(buffer)` is the slot of the
newest of `n > 0` items. -/
theorem latest_slot (tail head len : w64) (cap n : Nat) (hc : 0 < cap) (hc2 : cap ≤ 2 ^ 61)
    (hn : 0 < n) (ht : 0 ≤ sint.Z tail ∧ sint.Z tail < cap)
    (hh : sint.Z head = (sint.Z tail + n) % cap) (hl : sint.Z len = cap) :
    sint.Z (W64 (sint.Z (head - W64 1 + len) % sint.Z len)) =
      (ringSlot tail cap (n - 1) : Int) := by
  have h0 : 0 ≤ sint.Z head := by rw [hh]; exact Int.emod_nonneg _ (by omega)
  have h1 : sint.Z head < cap := by rw [hh]; exact Int.emod_lt_of_pos _ (by omega)
  have h2 : sint.Z (head - W64 1 + len) = sint.Z head + (cap - 1) := by word
  rw [h2, hh, hl, Int.emod_add_emod]
  have h3 : sint.Z tail + (n : Int) + ((cap : Int) - 1) =
      ((sint.nat tail + (n - 1) : Nat) : Int) + cap := by
    have : sint.Z tail = (sint.nat tail : Int) := by word
    omega
  rw [h3, Int.add_emod_right, ← Int.natCast_emod, ringSlot]
  have : (sint.nat tail + (n - 1)) % cap < cap := Nat.mod_lt _ hc
  generalize (sint.nat tail + (n - 1)) % cap = m at this ⊢
  word

/-- `Append`'s `(x + 1) % len(buffer)`, for `x` (`head` or `tail`) in `[0, cap)`. -/
theorem sint_srem_succ (x len : w64) (cap : Nat) (hl : sint.Z len = cap) (hc2 : cap ≤ 2 ^ 61)
    (h0 : 0 ≤ sint.Z x) (h1 : sint.Z x < cap) :
    sint.Z (BitVec.srem (x + W64 1) len) = (sint.Z x + 1) % cap := by
  rw [srem_of_nonneg _ _ (by word) (by omega), hl]
  have : sint.Z (x + W64 1) = sint.Z x + 1 := by word
  rw [this]
  have h2 : 0 ≤ (sint.Z x + 1) % (cap : Int) := Int.emod_nonneg _ (by omega)
  have h3 : (sint.Z x + 1) % (cap : Int) < cap := Int.emod_lt_of_pos _ (by omega)
  generalize (sint.Z x + 1) % (cap : Int) = m at h2 h3 ⊢
  word

/-! ## The predicate -/

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]
variable {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T'] {V : Type}

/-- The triple of the `revisionOf` closure a ring buffer stores (`RevisionOf[T]`): on
an item `p` modelling `v`, it returns `revOf v`. -/
def revisionOfSpec (f : GoFunc) (isItem : T' → V → IProp GF) (revOf : V → w64) : IProp GF :=
  iprop(∀ (p : T') (v : V),
    {{ isItem p v }} (App (Val #f) (Val #p)) {{ RET #(revOf v); True }})

instance revisionOfSpec_persistent (f : GoFunc) (isItem : T' → V → IProp GF)
    (revOf : V → w64) : Persistent (revisionOfSpec f isItem revOf) := by
  unfold revisionOfSpec; infer_instance

/-- The triple of an `IterFunc[T]` closure `iter` the iteration methods call on the
visited items `vis`, in loop-invariant style: called on the `i`-th visited item (its
revision and a Go item `p` modelling it) with `P i`, it returns whether to go on, with
`P (i + 1)` if so and the final postcondition `Q` if not. It does not get the ring
buffer, which the method holds while it iterates. -/
def iterSpec (iter : GoFunc) (isItem : T' → V → IProp GF) (revOf : V → w64) (vis : List V)
    (P : Nat → IProp GF) (Q : IProp GF) : IProp GF :=
  iprop(∀ (i : Nat) (p : T') (v : V), ⌜vis[i]? = some v⌝ -∗
    {{ P i ∗ isItem p v }}
      (App (App (Val #iter) (Val #(revOf v))) (Val #p))
    {{ (cont : Bool), RET #cont; if cont then P (i + 1) else Q }})

instance iterSpec_persistent (iter : GoFunc) (isItem : T' → V → IProp GF) (revOf : V → w64)
    (vis : List V) (P : Nat → IProp GF) (Q : IProp GF) :
    Persistent (iterSpec iter isItem revOf vis P Q) := by
  unfold iterSpec; infer_instance

/-- The physical facts of a ring of `cap` slots holding `n` items: what the struct's
`head`, `tail`, `size` and the buffer's length are. `cap ≤ 2^61` keeps the index
arithmetic (`tail + i + len(buffer)` in `at`) from overflowing a Go `int`. -/
structure RingOk (rb : ringBuffer T') (cap n : Nat) : Prop where
  cap_pos : 0 < cap
  cap_le : cap ≤ 2 ^ 61
  len : sint.Z rb.buffer'.len = cap
  size : sint.Z rb.size' = n
  size_le : n ≤ cap
  tail_lt : 0 ≤ sint.Z rb.tail' ∧ sint.Z rb.tail' < cap
  head : sint.Z rb.head' = (sint.Z rb.tail' + n) % cap

/-- `r` is a `ringBuffer[T]` of capacity `cap` holding `items`, oldest first:

* `r` points to the struct `rb`, whose `buffer` slice holds the `cap` entries `ents`
  (`RingOk`: `size`, `tail`, `head` and the length);
* logical index `i` is at slot `ringSlot rb.tail' cap i`, whose entry's `revision` is
  `revOf items[i]` (`%Hrev`, pure, for the searches) and whose `item` satisfies
  `isItem` with `items[i]` (`#Hitems`); unused slots hold anything;
* the revisions are strictly increasing (`RevSorted`);
* the stored `revisionOf` closure meets `revisionOfSpec`.

`dq` is the fraction of the struct and the buffer held (`DFrac.own 1`, the default, to
write: `Append`, `RebaseHistory`; any fraction to read); `ownRingBuffer_fractional` splits
it. -/
def ownRingBuffer (r : Loc) (cap : Nat) (isItem : T' → V → IProp GF) (revOf : V → w64)
    (items : List V) (dq : DFrac := DFrac.own 1) : IProp GF :=
  iprop(∃ (rb : ringBuffer T') (ents : List (entry T')),
    "Hr" ∷ r ↦{dq} rb ∗
    "Hbuf" ∷ rb.buffer' ↦*{dq} ents ∗
    "%Hok" ∷ ⌜RingOk rb cap items.length⌝ ∗
    "%Hrev" ∷ ⌜∀ (i : Nat) (v : V), items[i]? = some v →
      ∃ e, ents[ringSlot rb.tail' cap i]? = some e ∧ e.revision' = revOf v⌝ ∗
    "#Hitems" ∷ □ (∀ (i : Nat) (v : V) (e : entry T'), ⌜items[i]? = some v⌝ -∗
      ⌜ents[ringSlot rb.tail' cap i]? = some e⌝ -∗ isItem e.item' v) ∗
    "%Hsorted" ∷ ⌜RevSorted revOf items⌝ ∗
    "#HrevOf" ∷ revisionOfSpec rb.revisionOf' isItem revOf)

/-- Re-seal `ownRingBuffer` from its parts. -/
theorem ownRingBuffer_intro (r : Loc) (cap : Nat) (isItem : T' → V → IProp GF)
    (revOf : V → w64) (items : List V) (rb : ringBuffer T') (ents : List (entry T'))
    (Hok : RingOk rb cap items.length)
    (Hrev : ∀ (i : Nat) (v : V), items[i]? = some v →
      ∃ e, ents[ringSlot rb.tail' cap i]? = some e ∧ e.revision' = revOf v)
    (Hsorted : RevSorted revOf items) (dq : DFrac := DFrac.own 1) :
    ⊢ (r ↦{dq} rb : IProp GF) -∗ rb.buffer' ↦*{dq} ents -∗
      □ (∀ (i : Nat) (v : V) (e : entry T'), ⌜items[i]? = some v⌝ -∗
        ⌜ents[ringSlot rb.tail' cap i]? = some e⌝ -∗ isItem e.item' v) -∗
      revisionOfSpec rb.revisionOf' isItem revOf -∗
      ownRingBuffer r cap isItem revOf items dq := by
  iintro Hr Hbuf #Hitems #HrevOf
  unfold ownRingBuffer
  iexists rb, ents
  simp only [named]
  iframe Hr Hbuf Hitems HrevOf
  ipureintro
  exact ⟨Hok, Hrev, Hsorted⟩

/-- The struct of a ring, to read a field (`size`) and give it back unchanged. -/
theorem ownRingBuffer_struct_acc (r : Loc) (cap : Nat) (isItem : T' → V → IProp GF)
    (revOf : V → w64) (items : List V) :
    ownRingBuffer r cap isItem revOf items ⊢
      ∃ rb : ringBuffer T', (r ↦ rb : IProp GF) ∗ ⌜sint.Z rb.size' = items.length⌝ ∗
        ((r ↦ rb : IProp GF) -∗ ownRingBuffer r cap isItem revOf items) := by
  iintro H
  iNamed H
  iexists rb
  iframe Hr
  isplit
  · ipureintro; exact Hok.size
  iintro Hr
  iapply ownRingBuffer_intro r cap isItem revOf items rb ents Hok Hrev Hsorted $$ Hr Hbuf Hitems HrevOf

/-- `ownRingBuffer` is fractional in the fraction of the struct and buffer it holds (with
the same items: the halves of a shared ring agree on everything). -/
theorem ownRingBuffer_fractional (r : Loc) (cap : Nat) (isItem : T' → V → IProp GF)
    (revOf : V → w64) (items : List V) :
    Fractional (fun q => ownRingBuffer r cap isItem revOf items (DFrac.own q)) where
  fractional q1 q2 := by
    have hr : ∀ rb : ringBuffer T', (r ↦{DFrac.own (q1 + q2)} rb : IProp GF) ⊣⊢
        r ↦{DFrac.own q1} rb ∗ r ↦{DFrac.own q2} rb := fun rb =>
      (typedPointsto_dfractional (GF := GF) r rb).dfractional (DFrac.own q1) (DFrac.own q2)
    have hb : ∀ (sl : GoSlice) (ents : List (entry T')),
        (sl ↦*{DFrac.own (q1 + q2)} ents : IProp GF) ⊣⊢
          sl ↦*{DFrac.own q1} ents ∗ sl ↦*{DFrac.own q2} ents := fun sl ents =>
      (ownSlice_dfractional (GF := GF) sl ents).dfractional (DFrac.own q1) (DFrac.own q2)
    refine ⟨?_, ?_⟩
    · iintro H
      iNamed H
      icases (hr rb).1 $$ Hr with ⟨Hr1, Hr2⟩
      icases (hb rb.buffer' ents).1 $$ Hbuf with ⟨Hb1, Hb2⟩
      isplitl [Hr1 Hb1]
      · iapply ownRingBuffer_intro r cap isItem revOf items rb ents Hok Hrev Hsorted (DFrac.own q1)
          $$ Hr1 Hb1 Hitems HrevOf
      · iapply ownRingBuffer_intro r cap isItem revOf items rb ents Hok Hrev Hsorted (DFrac.own q2)
          $$ Hr2 Hb2 Hitems HrevOf
    · iintro ⟨H1, H2⟩
      iNamedSuffix H1 "1"
      iNamedSuffix H2 "2"
      icombine Hr1 Hr2 gives %Heq
      subst Heq
      icombine Hbuf1 Hbuf2 gives %Heq
      subst Heq
      iapply ownRingBuffer_intro r cap isItem revOf items rb ents Hok1 Hrev1 Hsorted1
        (DFrac.own (q1 + q2)) $$ [Hr1 Hr2] [Hbuf1 Hbuf2] Hitems1 HrevOf1
      · iapply (hr rb).2; iframe
      · iapply (hb rb.buffer' ents).2; iframe

/-- `ownRingBuffer` bounds the number of items by the capacity, and that by `2^61`. -/
theorem ownRingBuffer_length (r : Loc) (cap : Nat) (isItem : T' → V → IProp GF)
    (revOf : V → w64) (items : List V) (dq : DFrac := DFrac.own 1) :
    ownRingBuffer r cap isItem revOf items dq ⊢ ⌜items.length ≤ cap ∧ cap ≤ 2 ^ 61⌝ := by
  iintro H
  iNamed H
  ipureintro
  exact ⟨Hok.size_le, Hok.cap_le⟩

end defs

end EtcdGrove
end Perennial
