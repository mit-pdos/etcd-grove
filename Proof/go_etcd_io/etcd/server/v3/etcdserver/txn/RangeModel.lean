/-
The server's range (`range.go`: `executeRange` and its helpers), purely (unit 2). Lean-first;
`notes/STATUS.md`, "The server's txn package", unit 2.

`executeRange` reads the range of a request `o` (an `OpFull`, `Requests.lean`) through mvcc,
then filters, sorts, limits and assembles. This file states what it computes, over the state
the read answers (`stateAt log atRev`: `Lemmas.lean`'s bridge from mvcc's index answers), and
relates it to the client model's `rangeSel`/`rangeKvsOk` (`InvEtcd.lean`).

* **The limit mvcc reads with** (`rangeLimitOf`, `rangeLimit`): the request's limit plus one
  when it is positive and below `MaxInt64`, the ordering is the default (`isDefaultOrd` of the
  request's raw target and order) and there is no revision filter; else no limit (`0`).
* **What mvcc reads** (`kvRead`): with `FastKeysOnly` (`fastKeysOnly`: keys-only and not sorted
  by value) a key-value without its value *and its lease* (mvcc's `kvPtrIs false`): the
  server's keys-only responses carry lease `0` unless sorted by value.
* **The key-values sorted** (`srvPre`): the state's in the range, at most `rangeLimitOf o` of
  them, as read, those passing the revision filters (`kvFilterOk`); none if count-only.
* **Sorted** (`srvSorted`): a permutation sorted by the target, ascending or descending
  (`OpFull.effSortOrder`: the server sorts exactly when it is `1` or `2`; Go's `sort.Sort` is
  not stable, so ties are in any order); unsorted otherwise.
* **Limited and assembled** (`srvTrunc`, `srvMore`, `respKv`): the first `limit`, `More` when
  more remained, values dropped if keys-only.

**Where the server and the client model differ** (`srvRangeOk_rangeKvsOk`): (1) a fast keys-only
response's key-values have lease `0` (`leaseZ`); (2) a sort by a target other than the key with
no order (`SortOrder = NONE`: the server sorts ascending) and a positive limit (no revision
filter) sorts only the first `limit + 1` keys of the range, since `rangeLimit` tests the
request's raw order (`IsDefaultOrdering(target, NONE)` is true) while `sortRangeResults` tests
the adjusted one (`cutEarly`): the response is not the first `limit` of the sorted range
(`issues/etcd-range-sort-limit.md`). Outside these, the response is `rangeKvsOk` of `rangeSel`.

**The sort's premises**: `sort.Sort`'s axiom wants at most `2 ^ 62` elements and a strict weak
order; the comparators `(a - b) < 0` on versions and revisions are the signed order only for
values less than `2 ^ 63` apart. A log with at most `2 ^ 62` changes (`LogSmall`) gives both:
at most that many keys (`stateAt_small`), revisions and versions in `[0, 2 ^ 62]` (`kvOk`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.Lemmas
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.Requests
public import Perennial.Proof.slices.SortBasics

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace txn

open mvcc

/-! ## The request's options -/

/-- `IsDefaultOrdering(target, order)`: no order, or ascending by key (mvcc's own order). -/
def isDefaultOrd (target order : w64) : Bool :=
  decide (order = W64 0 ∨ (target = W64 0 ∧ order = W64 1))

/-- A protobuf enumeration value (`int32`) as the request's `OpFull` holds it (sign-extended):
equal to a small constant iff the `int32` is. -/
theorem sext32_eq (x : w32) (c : Int) (hc0 : -2 ^ 31 ≤ c) (hc1 : c < 2 ^ 31) :
    (W64 (sint.Z x) = W64 c) ↔ x = W32 c := by
  constructor
  · intro h
    have h1 : sint.Z (W64 (sint.Z x)) = sint.Z (W64 c) := by rw [h]
    have h2 : sint.Z (W64 (sint.Z x)) = sint.Z x := by word
    have h3 : sint.Z (W64 c) = c := by word
    have h4 : sint.Z (W32 c) = c := by word
    rw [h2, h3] at h1
    apply BitVec.eq_of_toInt_eq
    unfold sint.Z at h1 h4
    rw [h1, h4]
  · intro h; subst h; congr 1; word

theorem isDefaultOrd_sext (target order : w32) :
    isDefaultOrd (W64 (sint.Z target)) (W64 (sint.Z order)) =
      decide (order = W32 0 ∨ (target = W32 0 ∧ order = W32 1)) := by
  unfold isDefaultOrd
  simp only [sext32_eq order 0 (by omega) (by omega), sext32_eq target 0 (by omega) (by omega),
    sext32_eq order 1 (by omega) (by omega)]

/-- `HasRevisionFilters(r)`. -/
def hasRevFilters (o : OpFull) : Bool :=
  decide (o.base.minModRev ≠ W64 0 ∨ o.base.maxModRev ≠ W64 0 ∨
    o.base.minCreateRev ≠ W64 0 ∨ o.base.maxCreateRev ≠ W64 0)

/-- `rangeLimit(r)`: the limit `executeRange` reads with: none (`0`) if the ordering is not the
default or there is a revision filter; one more than the request's (to tell `More`) if it is
positive and below `MaxInt64`. -/
def rangeLimitOf (o : OpFull) : w64 :=
  let l := if isDefaultOrd o.sortTarget o.sortOrder = false ∨ hasRevFilters o = true then W64 0
    else o.base.limit
  if 0 < sint.Z l ∧ sint.Z l < 2 ^ 63 - 1 then l + W64 1 else l

/-- mvcc reads keys and revisions only (`FastKeysOnly`): keys-only, not sorted by value. -/
def fastKeysOnly (o : OpFull) : Bool := o.keysOnly && decide (o.sortTarget ≠ W64 4)

/-- A key-value as mvcc's read gives it: without value and lease for a fast keys-only read. -/
def kvRead (fast : Bool) (v : EtcdKv) : EtcdKv :=
  if fast then { v with value := [], lease := W64 0 } else v

/-- **The key-values `executeRange` sorts**: the state's in the range, at most `rangeLimitOf o`
of them, as mvcc reads them, those passing the revision filters; none if count-only. -/
def srvPre (o : OpFull) (s : List EtcdKv) : List EtcdKv :=
  if o.base.countOnly then []
  else ((takeLimit (limitOf (rangeLimitOf o)) (rangeIn s o)).map (kvRead (fastKeysOnly o))).filter
    (kvFilterOk o)

/-- **Sorted as the server sorts** (`sortRangeResults`): `l` is `pre` sorted by the target,
ascending (`effSortOrder = 1`) or descending (`2`), ties in any order (a permutation: Go's
`sort.Sort` is not stable); `pre` itself for any other order. -/
def srvSorted (o : OpFull) (pre l : List EtcdKv) : Prop :=
  l.Perm pre ∧
    (o.effSortOrder = W64 1 → l.Pairwise (kvLeBy o.sortTarget)) ∧
    (o.effSortOrder = W64 2 → l.Pairwise (fun a b => kvLeBy o.sortTarget b a)) ∧
    (o.effSortOrder ≠ W64 1 → o.effSortOrder ≠ W64 2 → l = pre)

/-- `More`: a positive limit cut the sorted key-values. -/
def srvMore (o : OpFull) (l : List EtcdKv) : Bool :=
  decide (0 < sint.Z o.base.limit ∧ sint.Z o.base.limit < (l.length : Int))

/-- The first `limit` (a positive limit). -/
def srvTrunc (o : OpFull) (l : List EtcdKv) : List EtcdKv :=
  if srvMore o l then l.take (sint.Z o.base.limit).toNat else l

/-- A response's key-value: no value if keys-only. -/
def respKv (o : OpFull) (v : EtcdKv) : EtcdKv :=
  if o.keysOnly then { v with value := [] } else v

/-- **The response's key-values and `More`** for the state `s`. -/
def srvRangeOk (o : OpFull) (s : List EtcdKv) (kvs : List EtcdKv) (more : Bool) : Prop :=
  ∃ l, srvSorted o (srvPre o s) l ∧ more = srvMore o l ∧ kvs = (srvTrunc o l).map (respKv o)

/-- **The response's count**: the number of keys in the range if count-only (or all counted:
`withTotal`), else at most the limit mvcc read with (`totalOf`). -/
def srvCount (o : OpFull) (s : List EtcdKv) (withTotal : Bool) : w64 :=
  W64 (if o.base.countOnly then ((rangeIn s o).length : Int)
    else (totalOf (limitOf (rangeLimitOf o)) withTotal (rangeIn s o).length : Int))

/-- The count-only request `Count` makes (key, range end, revision). -/
def countOp (k re : GoString) (rev : w64) : OpFull :=
  rangeOpOf k re rev (W64 0) (W32 0) (W32 0) false false true (W64 0) (W64 0) (W64 0) (W64 0)

/-- A sort that is cut early (`issues/etcd-range-sort-limit.md`): the server sorts and mvcc
read with a positive limit (the request's target is not the key, its order `NONE`, its limit
positive, no revision filter). -/
def cutEarly (o : OpFull) : Prop :=
  (o.effSortOrder = W64 1 ∨ o.effSortOrder = W64 2) ∧ 0 < sint.Z (rangeLimitOf o)

/-- A fast keys-only read zeroes the lease. -/
def leaseZ (fast : Bool) (v : EtcdKv) : EtcdKv := if fast then { v with lease := W64 0 } else v

/-- The request's sort target is one of the protobuf's (`KEY` .. `VALUE`): `sortRangeResults`
panics (`lg.Panic("unexpected sort target")`) on any other when it sorts. The gRPC layer
rejects others (`checkRangeRequest`). -/
def validSortTarget (o : OpFull) : Prop := 0 ≤ sint.Z o.sortTarget ∧ sint.Z o.sortTarget ≤ 4

/-! ## The comparators -/

/-- **The sorters' `Less`** (`kvSortBy*`), by target (`1` version, `2` create revision, `3` mod
revision, `4` value, else the key), on values whose revisions and versions are non-negative
(`kvOk`): Go's `(a - b) < 0` is then the signed order. -/
def kvLtBy (target : w64) (a b : EtcdKv) : Bool :=
  if target = W64 1 then decide (sint.Z a.version < sint.Z b.version)
  else if target = W64 2 then decide (sint.Z a.createRev < sint.Z b.createRev)
  else if target = W64 3 then decide (sint.Z a.modRev < sint.Z b.modRev)
  else if target = W64 4 then decide (go.GoStringLt a.value b.value)
  else decide (go.GoStringLt a.key b.key)

theorem kvLtBy_key (a b : EtcdKv) : kvLtBy (W64 0) a b = decide (go.GoStringLt a.key b.key) := by
  unfold kvLtBy; rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide)]

theorem kvLtBy_version (a b : EtcdKv) :
    kvLtBy (W64 1) a b = decide (sint.Z a.version < sint.Z b.version) := by
  unfold kvLtBy; rw [ite_eq_left rfl]

theorem kvLtBy_create (a b : EtcdKv) :
    kvLtBy (W64 2) a b = decide (sint.Z a.createRev < sint.Z b.createRev) := by
  unfold kvLtBy; rw [ite_eq_right (by decide), ite_eq_left rfl]

theorem kvLtBy_mod (a b : EtcdKv) :
    kvLtBy (W64 3) a b = decide (sint.Z a.modRev < sint.Z b.modRev) := by
  unfold kvLtBy; rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl]

theorem kvLtBy_value (a b : EtcdKv) :
    kvLtBy (W64 4) a b = decide (go.GoStringLt a.value b.value) := by
  unfold kvLtBy; rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl]

/-- A key-value whose version and revisions are non-negative. -/
def kvOk (v : EtcdKv) : Prop := 0 ≤ sint.Z v.version ∧ 0 ≤ sint.Z v.createRev ∧ 0 ≤ sint.Z v.modRev

/-- Go's `(a - b) < 0` on non-negative 64-bit integers is `a < b` (no overflow: the difference
of two values in `[0, 2 ^ 63)` is in `(-2 ^ 63, 2 ^ 63)`). -/
theorem sub_neg_iff (a b : w64) (ha : 0 ≤ sint.Z a) (hb : 0 ≤ sint.Z b) :
    decide (sint.Z (a - b) < sint.Z (W64 0)) = decide (sint.Z a < sint.Z b) := by
  have h : sint.Z (a - b) = sint.Z a - sint.Z b := by word
  rw [h]
  simp only [show sint.Z (W64 0) = 0 from rfl]
  congr 1
  apply propext
  omega

theorem goStringLt_asymm' {a b : GoString} (h : go.GoStringLt a b) : ¬ go.GoStringLt b a :=
  fun h' => goStringLt_irrefl _ (goStringLt_trans h h')

/-- The strict order on strings is a strict weak order. -/
theorem goStringLt_swo {E : Type} (f : E → GoString) :
    slices.StrictWeakOrder (fun a b : E => go.GoStringLt (f a) (f b)) where
  strict_weak_order_irrefl x := goStringLt_irrefl _
  strict_weak_order_trans _ _ _ h1 h2 := goStringLt_trans h1 h2
  strict_weak_order_equiv := {
    refl := fun _ => ⟨goStringLt_irrefl _, goStringLt_irrefl _⟩
    symm := fun h => ⟨h.2, h.1⟩
    trans := fun h1 h2 => by
      have e1 := goStringLt_eq_of_not_lt h1.1 h1.2
      have e2 := goStringLt_eq_of_not_lt h2.1 h2.2
      refine ⟨?_, ?_⟩ <;> rw [e1, e2] <;> exact goStringLt_irrefl _ }

theorem intLt_swo {E : Type} (f : E → w64) :
    slices.StrictWeakOrder (fun a b : E => sint.Z (f a) < sint.Z (f b)) where
  strict_weak_order_irrefl _ := by omega
  strict_weak_order_trans _ _ _ h1 h2 := by omega
  strict_weak_order_equiv :=
    ⟨fun _ => by omega, fun h => by omega, fun h1 h2 => by omega⟩

/-- Every target's `Less` is a strict weak order (on any type, through `f`). -/
theorem kvLtBy_swo {E : Type} (target : w64) (f : E → EtcdKv) :
    slices.StrictWeakOrder (fun a b : E => kvLtBy target (f a) (f b) = true) := by
  unfold kvLtBy
  by_cases h1 : target = W64 1
  · simp only [h1, ↓reduceIte, decide_eq_true_eq]; exact intLt_swo (fun x => (f x).version)
  by_cases h2 : target = W64 2
  · simp only [h2, show W64 2 ≠ W64 1 by decide, ↓reduceIte, decide_eq_true_eq]
    exact intLt_swo (fun x => (f x).createRev)
  by_cases h3 : target = W64 3
  · simp only [h3, show W64 3 ≠ W64 1 by decide, show W64 3 ≠ W64 2 by decide, ↓reduceIte,
      decide_eq_true_eq]
    exact intLt_swo (fun x => (f x).modRev)
  by_cases h4 : target = W64 4
  · simp only [h4, show W64 4 ≠ W64 1 by decide, show W64 4 ≠ W64 2 by decide,
      show W64 4 ≠ W64 3 by decide, ↓reduceIte, decide_eq_true_eq]
    exact goStringLt_swo (fun x => (f x).value)
  · simp only [h4, h3, h2, h1, ↓reduceIte, decide_eq_true_eq]
    exact goStringLt_swo (fun x => (f x).key)

/-- Not less (flipped) is the client model's `kvLeBy`. -/
theorem kvLtBy_false_iff (target : w64) (a b : EtcdKv) :
    kvLtBy target b a = false ↔ kvLeBy target a b := by
  unfold kvLtBy kvLeBy
  have hs : ∀ x y : GoString, decide (go.GoStringLt y x) = false ↔ go.GoStringLe x y := by
    intro x y
    simp only [decide_eq_false_iff_not, go.GoStringLe]
    constructor
    · intro h
      by_cases hxy : go.GoStringLt x y
      · exact Or.inr hxy
      · exact Or.inl (goStringLt_eq_of_not_lt hxy h)
    · rintro (h | h)
      · subst h; exact goStringLt_irrefl _
      · exact goStringLt_asymm' h
  split
  · simp only [decide_eq_false_iff_not]; omega
  split
  · simp only [decide_eq_false_iff_not]; omega
  split
  · simp only [decide_eq_false_iff_not]; omega
  split
  · exact hs _ _
  · exact hs _ _

/-- **A sort by `Less`** (no later element less than an earlier one, `sort.Sort`'s post) is
sorted by the client's `kvLeBy`. -/
theorem pairwise_of_sorted {E : Type} (f : E → EtcdKv) (target : w64) (l : List E)
    (h : ∀ (i j : Nat) (a b : E), l[i]? = some a → l[j]? = some b → i < j →
      kvLtBy target (f b) (f a) = false) :
    (l.map f).Pairwise (kvLeBy target) := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  simp only [List.getElem_map]
  have hi' : i < l.length := by simpa using hi
  have hj' : j < l.length := by simpa using hj
  exact (kvLtBy_false_iff _ _ _).1
    (h i j l[i] l[j] (List.getElem?_eq_getElem hi') (List.getElem?_eq_getElem hj') hij)

/-- The same, for the flipped order (`sort.Reverse`). -/
theorem pairwise_of_sorted_rev {E : Type} (f : E → EtcdKv) (target : w64) (l : List E)
    (h : ∀ (i j : Nat) (a b : E), l[i]? = some a → l[j]? = some b → i < j →
      kvLtBy target (f a) (f b) = false) :
    (l.map f).Pairwise (fun a b => kvLeBy target b a) := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  simp only [List.getElem_map]
  have hi' : i < l.length := by simpa using hi
  have hj' : j < l.length := by simpa using hj
  exact (kvLtBy_false_iff _ _ _).1
    (h i j l[i] l[j] (List.getElem?_eq_getElem hi') (List.getElem?_eq_getElem hj') hij)

/-! ## Small logs: the sort's premises -/

/-- The number of changes of a log. -/
def logChanges (log : Log) : Nat := (log.map List.length).sum

/-- A log with at most `2 ^ 62` changes (every store that ever ran). -/
def LogSmall (log : Log) : Prop := logChanges log ≤ 2 ^ 62

/-- **The sort's premise**: a request that sorts (`effSortOrder` `1` or `2`) reads a small log
(`LogSmall`: `sort.Sort`'s at most `2 ^ 62` elements, the comparators' non-negative values). -/
def sortOk (o : OpFull) (log : Log) : Prop :=
  (o.effSortOrder = W64 1 ∨ o.effSortOrder = W64 2) → LogSmall log

/-- What a state of the first `n` revisions after `P` changes satisfies: at most `P` keys, mod
and create revisions in `[0, n)`, versions in `[1, P]`. -/
def StateBound (n P : Nat) (s : List EtcdKv) : Prop :=
  s.length ≤ P ∧ ∀ v ∈ s, 0 ≤ sint.Z v.modRev ∧ sint.Z v.modRev < n ∧
    0 ≤ sint.Z v.createRev ∧ sint.Z v.createRev < n ∧ 1 ≤ sint.Z v.version ∧
    sint.Z v.version ≤ P

theorem btInsert_length_le {V : Type} {less : V → V → Prop} [DecidableRel less] (v : V) :
    ∀ l : List V, (btInsert less v l).length ≤ l.length + 1
  | [] => by simp [btInsert]
  | w :: ws => by
    unfold btInsert
    split
    · have := btInsert_length_le (less := less) v ws; simp; omega
    · split <;> simp

theorem stateBound_mono {n n' P P' : Nat} {s : List EtcdKv} (h : StateBound n P s)
    (hn : n ≤ n') (hP : P ≤ P') : StateBound n' P' s := by
  refine ⟨by have := h.1; omega, fun v hv => ?_⟩
  have := h.2 v hv
  omega

theorem putKv_length_le (r : w64) (k val : GoString) (l : w64) (s : List EtcdKv) :
    (putKv r k val l s).length ≤ s.length + 1 := by
  unfold putKv; exact btInsert_length_le _ _

/-- A key-value put again at `r`. -/
def bumpKv (r : w64) (val : GoString) (l : w64) (w : EtcdKv) : EtcdKv :=
  { w with modRev := r, version := w.version + W64 1, value := val, lease := l }

/-- A key-value created at `r`. -/
def newKv (r : w64) (k val : GoString) (l : w64) : EtcdKv :=
  { key := k, createRev := r, modRev := r, version := W64 1, value := val, lease := l }

theorem putKv_mem {r : w64} {k val : GoString} {l : w64} {s : List EtcdKv} {x : EtcdKv}
    (hx : x ∈ putKv r k val l s) :
    x ∈ s ∨ (∃ w ∈ s, x = bumpKv r val l w) ∨ x = newKv r k val l := by
  unfold putKv at hx
  rcases btInsert_mem hx with h | h
  · subst h
    split
    · rename_i w hw
      exact Or.inr (Or.inl ⟨w, List.mem_of_find?_eq_some hw, rfl⟩)
    · exact Or.inr (Or.inr rfl)
  · exact Or.inl h

theorem stateBound_applyChange (n P r : Nat) (hr : r < n) (hn : n ≤ 2 ^ 63) (hP : P + 1 ≤ 2 ^ 62)
    (s : List EtcdKv) (c : Change) (h : StateBound n P s) :
    StateBound n (P + 1) (applyChange (W64 r) s c) := by
  have hrz : sint.Z (W64 (r : Int)) = r := by word
  cases c with
  | del k =>
    simp only [applyChange]
    refine ⟨by have := List.length_filter_le (fun x => !decide (x.key = k)) s; have := h.1; omega,
      fun v hv => ?_⟩
    have := h.2 v (List.mem_filter.1 hv).1
    omega
  | put k val l =>
    simp only [applyChange]
    refine ⟨by have := putKv_length_le (W64 r) k val l s; have := h.1; omega, fun v hv => ?_⟩
    rcases putKv_mem hv with hv | ⟨w, hwm, hx⟩ | hx
    · have := h.2 v hv
      omega
    · have hb := h.2 w hwm
      have hver : sint.Z (w.version + W64 1) = sint.Z w.version + 1 := by
        have : sint.Z w.version ≤ 2 ^ 62 := by omega
        word
      subst hx
      simp only [bumpKv]
      rw [hver, hrz]
      omega
    · subst hx
      simp only [newKv]
      have h1 : sint.Z (W64 1) = 1 := rfl
      rw [hrz, h1]
      omega

theorem stateBound_applyChanges (n P r : Nat) (hr : r < n) (hn : n ≤ 2 ^ 63) :
    ∀ (cs : List Change) (s : List EtcdKv), P + cs.length ≤ 2 ^ 62 → StateBound n P s →
      StateBound n (P + cs.length) (applyChanges (W64 r) s cs) := by
  intro cs
  induction cs generalizing P with
  | nil => intro s _ h; simpa [applyChanges] using h
  | cons c cs ih =>
    intro s hP h
    unfold applyChanges
    rw [List.foldl_cons]
    have h1 := stateBound_applyChange n P r hr hn (by simp at hP; omega) s c h
    have := ih (P + 1) (applyChange (W64 r) s c) (by simp at hP; omega) h1
    unfold applyChanges at this
    simpa [Nat.add_assoc, Nat.add_comm 1] using this

theorem stateBound_stateAfter :
    ∀ (log : Log), log.length ≤ 2 ^ 63 → logChanges log ≤ 2 ^ 62 →
      StateBound log.length (logChanges log) (stateAfter log) := by
  intro log0
  obtain ⟨rl, rfl⟩ : ∃ rl : Log, log0 = rl.reverse := ⟨log0.reverse, by simp⟩
  induction rl with
  | nil => intro _ _; exact ⟨by simp [stateAfter], fun v hv => by simp [stateAfter] at hv⟩
  | cons cs rl ih =>
    rw [List.reverse_cons]
    generalize rl.reverse = log at ih ⊢
    intro hlen hch
    have hch' : logChanges (log ++ [cs]) = logChanges log + cs.length := by
      simp [logChanges]
    rw [hch'] at hch ⊢
    rw [stateAfter_snoc]
    have h0 := ih (by simp at hlen; omega) (by omega)
    have h1 := stateBound_mono (n' := (log ++ [cs]).length) h0 (by simp) (Nat.le_refl _)
    exact stateBound_applyChanges _ _ log.length (by simp) hlen cs _ hch h1

theorem logChanges_take (log : Log) (n : Nat) : logChanges (log.take n) ≤ logChanges log := by
  induction log generalizing n with
  | nil => simp [logChanges]
  | cons cs log ih =>
    cases n with
    | zero => simp [logChanges]
    | succ n => have := ih n; simp [logChanges] at *; omega

/-- **A small log's states**: at most `2 ^ 62` keys, each with non-negative revisions and
version. -/
theorem stateAt_small (log : Log) (hlen : log.length < 2 ^ 63) (h : LogSmall log) (r : Nat) :
    (stateAt log r).length ≤ 2 ^ 62 ∧ ∀ v ∈ stateAt log r, kvOk v := by
  have hc := logChanges_take log (r + 1)
  have hb := stateBound_stateAfter (log.take (r + 1)) (by simp; omega) (by unfold LogSmall at h; omega)
  unfold stateAt
  refine ⟨by have := hb.1; unfold LogSmall at h; omega, fun v hv => ?_⟩
  have := hb.2 v hv
  exact ⟨by omega, by omega, by omega⟩

/-! ## The server's range against the client's -/

theorem kvFilterOk_kvRead (o : OpFull) (f : Bool) (v : EtcdKv) :
    kvFilterOk o (kvRead f v) = kvFilterOk o v := by
  unfold kvRead; cases f <;> rfl

theorem kvLeBy_kvRead (t : w64) (f : Bool) (hf : f = true → t ≠ W64 4) (a b : EtcdKv) :
    kvLeBy t (kvRead f a) (kvRead f b) ↔ kvLeBy t a b := by
  unfold kvRead
  cases f with
  | false => rfl
  | true =>
    have := hf rfl
    unfold kvLeBy
    simp only [↓reduceIte, this]

theorem respKv_kvRead (o : OpFull) (v : EtcdKv) :
    respKv o (kvRead (fastKeysOnly o) v) =
      leaseZ (fastKeysOnly o) (if o.keysOnly then { v with value := [] } else v) := by
  unfold respKv kvRead leaseZ fastKeysOnly
  cases hk : o.keysOnly <;> by_cases ht : o.sortTarget = W64 4 <;>
    simp only [ht, ne_eq, not_true, not_false_eq_true, decide_true, decide_false,
      Bool.and_true, Bool.and_false, ↓reduceIte, Bool.false_eq_true] <;> rfl

/-- A permutation of a map is the map of a permutation. -/
theorem perm_map_exists {α β : Type} (f : α → β) :
    ∀ {l₁ : List β} {l : List α}, l₁.Perm (l.map f) → ∃ l' : List α, l'.Perm l ∧ l'.map f = l₁ := by
  intro l₁ l h
  generalize hl₂ : l.map f = l₂ at h
  induction h generalizing l with
  | nil => exact ⟨[], by cases l <;> simp_all, rfl⟩
  | cons x _ ih =>
    cases l with
    | nil => simp at hl₂
    | cons a l =>
      simp only [List.map_cons, List.cons.injEq] at hl₂
      obtain ⟨l', hp, hm⟩ := ih hl₂.2
      exact ⟨a :: l', hp.cons a, by simp [hm, hl₂.1]⟩
  | swap x y _ =>
    cases l with
    | nil => simp at hl₂
    | cons a l =>
      cases l with
      | nil => simp at hl₂
      | cons b l =>
        simp only [List.map_cons, List.cons.injEq] at hl₂
        obtain ⟨h1, h2, h3⟩ := hl₂
        exact ⟨b :: a :: l, List.Perm.swap a b l, by simp [h1, h2, h3]⟩
  | trans _ _ ih1 ih2 =>
    obtain ⟨l2, hp2, hm2⟩ := ih2 hl₂
    obtain ⟨l1, hp1, hm1⟩ := ih1 hm2
    exact ⟨l1, hp1.trans hp2, hm1⟩

instance kvLeBy_dec (t : w64) : DecidableRel (kvLeBy t) := fun a b => by
  unfold kvLeBy; infer_instance

/-- A sorted permutation exists (`mergeSort`), ascending or descending. -/
theorem exists_sorted (t : w64) (sel : List EtcdKv) :
    ∃ l : List EtcdKv, l.Perm sel ∧ l.Pairwise (kvLeBy t) := by
  have htot : ∀ a b, kvLeBy t a b ∨ kvLeBy t b a := by
    intro a b
    by_cases h : kvLtBy t b a = false
    · exact Or.inl ((kvLtBy_false_iff t a b).1 h)
    · right
      apply (kvLtBy_false_iff t b a).1
      have hswo := kvLtBy_swo (E := EtcdKv) t id
      have hba : kvLtBy t b a = true := by simpa using h
      cases hab : kvLtBy t a b
      · rfl
      · exact absurd (hswo.strict_weak_order_trans _ _ _ hba hab) (hswo.strict_weak_order_irrefl _)
  have htrans : ∀ a b c, kvLeBy t a b → kvLeBy t b c → kvLeBy t a c := by
    intro a b c h1 h2
    have hswo := kvLtBy_swo (E := EtcdKv) t id
    rw [← kvLtBy_false_iff] at *
    cases h : kvLtBy t c a
    · rfl
    · exfalso
      -- c < a, ¬ b < a, ¬ c < b: incomparability transitivity
      have e := hswo.strict_weak_order_equiv
      by_cases hab : kvLtBy t a b = true
      · exact absurd (hswo.strict_weak_order_trans _ _ _ h hab) (by simp [h2])
      · have hab' : kvLtBy t a b = false := by simpa using hab
        have hbc : ¬ (kvLtBy t b c = true) := fun hbc =>
          absurd (hswo.strict_weak_order_trans _ _ _ hbc h) (by simp [h1])
        -- a ~ b (incomparable); then c < a gives c < b
        have hinc : ¬ (kvLtBy t a b = true) ∧ ¬ (kvLtBy t b a = true) := by simp [hab', h1]
        cases hcb : kvLtBy t c b
        · have hinc2 : ¬ (kvLtBy t b c = true) ∧ ¬ (kvLtBy t c b = true) :=
            ⟨hbc, by simp [hcb]⟩
          have := e.trans hinc hinc2
          exact this.2 h
        · simp [hcb] at h2
  refine ⟨sel.mergeSort (fun a b => decide (kvLeBy t a b)), List.mergeSort_perm _ _, ?_⟩
  have := List.pairwise_mergeSort (le := fun a b => decide (kvLeBy t a b))
    (by intro a b c h1 h2; simp only [decide_eq_true_eq] at *; exact htrans a b c h1 h2)
    (by intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; exact htot a b) sel
  exact this.imp (fun h => by simpa using h)

theorem exists_sorted_rev (t : w64) (sel : List EtcdKv) :
    ∃ l : List EtcdKv, l.Perm sel ∧ l.Pairwise (fun a b => kvLeBy t b a) := by
  obtain ⟨l, hp, hs⟩ := exists_sorted t sel
  refine ⟨l.reverse, (List.reverse_perm l).trans hp, ?_⟩
  rw [List.pairwise_reverse]; exact hs

/-- The client's response for the count-only case: nothing, whatever the order. -/
theorem rangeKvsOk_countOnly (o : OpFull) (sel : List EtcdKv) (h : o.base.countOnly = true) :
    rangeKvsOk o sel [] := by
  by_cases h1 : o.effSortOrder = W64 1
  · obtain ⟨l, hp, hs⟩ := exists_sorted o.sortTarget sel
    refine ⟨l, hp, (fun h0 => by rw [h1] at h0; cases h0), (fun _ => hs), (fun h2 => ?_),
      (by simp [h])⟩
    rw [h1] at h2; cases h2
  by_cases h2 : o.effSortOrder = W64 2
  · obtain ⟨l, hp, hs⟩ := exists_sorted_rev o.sortTarget sel
    refine ⟨l, hp, (fun h0 => by rw [h2] at h0; cases h0), (fun h => absurd h h1), (fun _ => hs),
      (by simp [h])⟩
  · exact ⟨sel, List.Perm.refl _, (fun _ => rfl), (fun h => absurd h h1), (fun h => absurd h h2),
      (by simp [h])⟩

theorem filter_true_of_noFilters (o : OpFull) (h : hasRevFilters o = false) (l : List EtcdKv) :
    l.filter (kvFilterOk o) = l := by
  unfold hasRevFilters at h
  simp only [decide_eq_false_iff_not, not_or, ne_eq, Decidable.not_not] at h
  apply List.filter_eq_self.2
  intro v _
  unfold kvFilterOk
  simp [h.1, h.2.1, h.2.2.1, h.2.2.2]

theorem rangeLimitOf_pos (o : OpFull) (h : 0 < sint.Z (rangeLimitOf o)) :
    isDefaultOrd o.sortTarget o.sortOrder = true ∧ hasRevFilters o = false ∧
      0 < sint.Z o.base.limit ∧
      (sint.Z (rangeLimitOf o) = sint.Z o.base.limit + 1 ∨
        (sint.Z (rangeLimitOf o) = sint.Z o.base.limit ∧ sint.Z o.base.limit = 2 ^ 63 - 1)) := by
  unfold rangeLimitOf at h ⊢
  simp only at h ⊢
  by_cases hc : isDefaultOrd o.sortTarget o.sortOrder = false ∨ hasRevFilters o = true
  · simp only [hc, ↓reduceIte] at h
    exfalso
    split at h <;> word
  · have hd : isDefaultOrd o.sortTarget o.sortOrder = true := by
      cases h' : isDefaultOrd o.sortTarget o.sortOrder <;> simp_all
    have hn : hasRevFilters o = false := by cases h' : hasRevFilters o <;> simp_all
    simp only [hc, ↓reduceIte] at h ⊢
    refine ⟨hd, hn, ?_⟩
    split at h
    · rename_i hl
      refine ⟨hl.1, Or.inl ?_⟩
      simp only [hl, and_self, ↓reduceIte]
      word
    · rename_i hl
      refine ⟨h, Or.inr ?_⟩
      simp only [hl, ↓reduceIte]
      refine ⟨?_, ?_⟩ <;> (first | trivial | rfl | word)

/-- `effSortOrder` of a request whose `sortSet` is as `rangeOpOf` sets it: the server sorts
(order `1` or `2`) only off its default ordering. -/
theorem effSortOrder_sorts (o : OpFull)
    (hset : o.base.sortSet = decide (o.sortOrder ≠ W64 0 ∨ o.sortTarget ≠ W64 0))
    (h : o.effSortOrder = W64 1 ∨ o.effSortOrder = W64 2) :
    isDefaultOrd o.sortTarget o.sortOrder = true → o.sortOrder = W64 0 ∧ o.sortTarget ≠ W64 0 := by
  intro hd
  unfold OpFull.effSortOrder at h
  unfold isDefaultOrd at hd
  rw [hset] at h
  simp only [decide_eq_true_eq] at hd
  rcases hd with h0 | ⟨ht, ho⟩
  · refine ⟨h0, fun ht => ?_⟩
    simp [h0, ht] at h
  · simp [ho, ht] at h

theorem srvTrunc_map (o : OpFull) (f : EtcdKv → EtcdKv) (L : List EtcdKv) :
    srvTrunc o (L.map f) = (srvTrunc o L).map f := by
  unfold srvTrunc srvMore
  simp only [List.length_map]
  split <;> simp [List.map_take]

theorem srvTrunc_eq (o : OpFull) (L : List EtcdKv) :
    srvTrunc o L = if 0 < sint.Z o.base.limit then L.take (sint.Z o.base.limit).toNat else L := by
  unfold srvTrunc srvMore
  by_cases hpos : 0 < sint.Z o.base.limit
  · by_cases hlt : sint.Z o.base.limit < (L.length : Int)
    · simp [hpos, hlt]
    · simp only [hpos, hlt, and_false, decide_false, Bool.false_eq_true, ↓reduceIte]
      rw [List.take_of_length_le (by omega)]
  · simp [hpos]

/-- The client's response key-value (`rangeKvsOk`'s map). -/
def clientResp (o : OpFull) (v : EtcdKv) : EtcdKv :=
  if o.keysOnly then { v with value := [] } else v

theorem respKv_map_kvRead (o : OpFull) (L : List EtcdKv) :
    (L.map (kvRead (fastKeysOnly o))).map (respKv o) =
      (L.map (clientResp o)).map (leaseZ (fastKeysOnly o)) := by
  simp only [List.map_map]
  congr 1
  funext v
  simp [clientResp, respKv_kvRead]

/-- **The server's range is the client's** (`rangeKvsOk` of `rangeSel`), up to the lease of a
fast keys-only read (`leaseZ`), unless the sort is cut early (`cutEarly`); and `More` is the
client's (`getRespMore`'s) below the largest limit. -/
theorem srvRangeOk_rangeKvsOk (o : OpFull) (s : List EtcdKv) (kvs : List EtcdKv) (more : Bool)
    (hset : o.base.sortSet = decide (o.sortOrder ≠ W64 0 ∨ o.sortTarget ≠ W64 0))
    (h : srvRangeOk o s kvs more) (hcut : ¬ cutEarly o) :
    ∃ kvs', rangeKvsOk o (rangeSel s o) kvs' ∧ kvs = kvs'.map (leaseZ (fastKeysOnly o)) ∧
      (o.base.countOnly = false → sint.Z o.base.limit < 2 ^ 63 - 1 →
        more = decide (0 < sint.Z o.base.limit ∧
          sint.Z o.base.limit < ((rangeSel s o).length : Int))) := by
  obtain ⟨l, ⟨hperm, hasc, hdesc, hnone⟩, hmore, hkvs⟩ := h
  by_cases hco : o.base.countOnly = true
  · have hpre : srvPre o s = [] := by unfold srvPre; simp [hco]
    rw [hpre] at hperm
    have hl : l = [] := List.Perm.eq_nil hperm
    subst hl
    refine ⟨[], rangeKvsOk_countOnly o _ hco, by simp [hkvs, srvTrunc], fun h => by simp [hco] at h⟩
  have hco' : o.base.countOnly = false := by simpa using hco
  have hfast : fastKeysOnly o = true → o.sortTarget ≠ W64 4 := by
    unfold fastKeysOnly; simp
  have hmapsel : ((rangeIn s o).map (kvRead (fastKeysOnly o))).filter (kvFilterOk o) =
      (rangeSel s o).map (kvRead (fastKeysOnly o)) := by
    unfold rangeSel
    rw [List.filter_map]
    congr 1
    apply List.filter_congr
    intro v _
    simp [Function.comp, kvFilterOk_kvRead]
  -- the client's key-values for a list `L` the server sorted
  have hclient : ∀ L : List EtcdKv, kvs = ((srvTrunc o L).map (clientResp o)).map
      (leaseZ (fastKeysOnly o)) → kvs = ((if o.base.countOnly then []
        else ((if 0 < sint.Z o.base.limit then L.take (sint.Z o.base.limit).toNat else L).map
          (fun v => if o.keysOnly then { v with value := [] } else v)))).map
            (leaseZ (fastKeysOnly o)) := by
    intro L hL
    rw [hL, srvTrunc_eq, hco']
    rfl
  by_cases hsort : o.effSortOrder = W64 1 ∨ o.effSortOrder = W64 2
  · -- sorted: mvcc read the whole range
    have hL : ¬ 0 < sint.Z (rangeLimitOf o) := fun hp => hcut ⟨hsort, hp⟩
    have hpre : srvPre o s = (rangeSel s o).map (kvRead (fastKeysOnly o)) := by
      unfold srvPre
      simp only [hco', Bool.false_eq_true, ↓reduceIte]
      unfold limitOf
      simp only [hL, ↓reduceIte, takeLimit]
      exact hmapsel
    rw [hpre] at hperm
    obtain ⟨l', hp', hm'⟩ := perm_map_exists (kvRead (fastKeysOnly o)) hperm
    subst hm'
    refine ⟨_, ⟨l', hp', ?_, ?_, ?_, rfl⟩, hclient l' ?_, ?_⟩
    · intro h0; rcases hsort with h | h <;> rw [h] at h0 <;> cases h0
    · intro h1
      have := hasc h1
      rw [List.pairwise_map] at this
      exact this.imp (fun h => (kvLeBy_kvRead _ _ hfast _ _).1 h)
    · intro h2
      have := hdesc h2
      rw [List.pairwise_map] at this
      exact this.imp (fun h => (kvLeBy_kvRead _ _ hfast _ _).1 h)
    · rw [hkvs, srvTrunc_map, respKv_map_kvRead]
    · intro _ _
      rw [hmore]; unfold srvMore
      simp [hp'.length_eq]
  · -- not sorted: `l` is what mvcc read
    have hl := hnone (fun h => hsort (Or.inl h)) (fun h => hsort (Or.inr h))
    by_cases hL : 0 < sint.Z (rangeLimitOf o)
    · obtain ⟨hdef, hnf, hlim, hL'⟩ := rangeLimitOf_pos o hL
      have hselin : rangeSel s o = rangeIn s o := by
        unfold rangeSel; exact filter_true_of_noFilters o hnf _
      have hpre : srvPre o s =
          ((rangeIn s o).take (sint.Z (rangeLimitOf o)).toNat).map (kvRead (fastKeysOnly o)) := by
        unfold srvPre
        simp only [hco', Bool.false_eq_true, ↓reduceIte]
        unfold limitOf
        simp only [hL, ↓reduceIte, takeLimit]
        exact filter_true_of_noFilters o hnf _
      -- the order is the default: `effSortOrder = 0`
      have heff : o.effSortOrder = W64 0 := by
        unfold isDefaultOrd at hdef
        simp only [decide_eq_true_eq] at hdef
        unfold OpFull.effSortOrder at hsort ⊢
        rw [hset] at hsort ⊢
        rcases hdef with ho | ⟨ht, ho⟩
        · by_cases ht : o.sortTarget = W64 0
          · simp [ho, ht]
          · exfalso; apply hsort; left
            simp only [ho, ht, ne_eq, not_false_eq_true, not_true_eq_false,
              or_true, decide_true, Bool.true_eq_false, ↓reduceIte,
              and_self]
        · simp [ho, ht]
      rw [hl, hpre] at hkvs hmore
      have hLn : (sint.Z o.base.limit).toNat ≤ (sint.Z (rangeLimitOf o)).toNat := by omega
      refine ⟨_, ⟨rangeSel s o, List.Perm.refl _, (fun _ => rfl), (fun h => by rw [heff] at h; cases h),
          (fun h => by rw [heff] at h; cases h), rfl⟩, hclient (rangeSel s o) ?_, ?_⟩
      · rw [hkvs, srvTrunc_map, respKv_map_kvRead, srvTrunc_eq, srvTrunc_eq, hselin]
        simp only [hlim, ↓reduceIte, List.take_take, Nat.min_eq_left hLn]
      · intro _ hmax
        rw [hmore, hselin]
        unfold srvMore
        simp only [List.length_map, List.length_take, hlim, true_and]
        congr 1
        apply propext
        omega
    · have hpre : srvPre o s = (rangeSel s o).map (kvRead (fastKeysOnly o)) := by
        unfold srvPre
        simp only [hco', Bool.false_eq_true, ↓reduceIte]
        unfold limitOf
        simp only [hL, ↓reduceIte, takeLimit]
        exact hmapsel
      rw [hl, hpre] at hkvs hmore
      refine ⟨_, ⟨rangeSel s o, List.Perm.refl _, (fun _ => rfl), (fun h => absurd (Or.inl h) hsort),
          (fun h => absurd (Or.inr h) hsort), rfl⟩, hclient (rangeSel s o) ?_, ?_⟩
      · rw [hkvs, srvTrunc_map, respKv_map_kvRead]
      · intro _ _
        rw [hmore]; unfold srvMore
        simp

end txn
end EtcdGrove
end Perennial
