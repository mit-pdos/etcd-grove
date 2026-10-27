/-
The pure model of client-go's thread-safe store (`tools/cache/thread_safe_store.go`): its items,
the indexers' functions, and the indices, as the abstract state `St` and the physical index `Ix`
the proofs relate it to. Lean-first; phase 2 of the DaemonSet plan (`notes/k8s-daemonset-plan.md`).

* An indexer is a pure function `F : GoInterface → List GoString` of an object (the index
  function's contract, `StoreDefs.lean`'s `fnOk`, says the Go function computes it).
* `inIdx F it v k`: key `k` is in the index of value `v` under `F` when `k`'s object is not
  `nil` and `v ∈ F obj` (a `nil` object is stored but never indexed: `updateSingleIndex` skips it).
* The physical index of one indexer (`IxN`) maps each indexed value to its set's location and
  keys; `viewN` is the keys per value (none for a value it lacks). `nameOk F it X`: `X`'s keys
  are exactly those `inIdx`. `updN_ok` is what `updateSingleIndex` relies on: deleting the key
  from the sets of its old object's values, then adding it to those of the new object's values,
  keeps `nameOk` for the items changed at that key.
-/
module

public import Proof.k8s_io.client_go.tools.cache.Keys
public import Proof.k8s_io.apimachinery.pkg.util.sets.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open sets

section model
variable [FfiSyntax]

/-- An indexer's function of an object. -/
abbrev Fn : Type := GoInterface → List GoString
/-- The items, by key. -/
abbrev Items : Type := GMap GoString GoInterface
/-- A set of keys (`sets.Set[string]`). -/
abbrev KSet : Type := GMap GoString Elem
/-- One indexer's physical index: each value's set (its location and keys). -/
abbrev IxN : Type := GMap GoString (Loc × KSet)
/-- The physical indices: each indexer's index (its location and contents). -/
abbrev Ix : Type := GMap GoString (Loc × IxN)

/-- The object at a key (`nil` if none, as `c.items[key]`). -/
def objAt (it : Items) (k : GoString) : GoInterface := (it !! k).getD interface.nil

/-- The values an object is indexed under (none for `nil`, which is not indexed). -/
def valsOf (F : Fn) (o : GoInterface) : List GoString := if o = interface.nil then [] else F o

/-- Key `k` is in the index of value `v`. -/
def inIdx (F : Fn) (it : Items) (v k : GoString) : Prop := v ∈ valsOf F (objAt it k)

/-- The keys of value `v` in an indexer's physical index. -/
def viewN (X : IxN) (v : GoString) : KSet := ((X !! v).map Prod.snd).getD ∅

/-- An indexer's physical index is exact for the items. -/
def nameOk (F : Fn) (it : Items) (X : IxN) : Prop := ∀ v k, k ∈ viewN X v ↔ inIdx F it v k

/-- An indexer's physical index (empty if none). -/
def ixAt (ix : Ix) (n : GoString) : IxN := ((ix !! n).map Prod.snd).getD ∅

/-- The physical indices are exact for the items, for each indexer, and only indexers have one. -/
def ixOk (fns : GMap GoString Fn) (it : Items) (ix : Ix) : Prop :=
  (∀ n, n ∈ ix → n ∈ fns) ∧ ∀ n F, fns !! n = some F → nameOk F it (ixAt ix n)

/-- **The store's abstract state**: its items, its resource version and its indexers. -/
structure St where
  items : Items
  rv : GoString
  fns : GMap GoString Fn

/-- `Update(key, obj)`/`Add`: the object stored; the resource version becomes the object's when
its accessor has one (`rvo`). -/
def St.update (σ : St) (k : GoString) (o : GoInterface) (rvo : Option GoString) : St :=
  { σ with items := <[k := o]> σ.items, rv := rvo.getD σ.rv }

/-- `DeleteWithObject(key, obj)`/`Delete`: the key removed; the resource version as `update`'s. -/
def St.delete (σ : St) (k : GoString) (rvo : Option GoString) : St :=
  { σ with items := GMap.delete k σ.items, rv := rvo.getD σ.rv }

/-- `Replace(items, rv)`: the items and resource version replaced. -/
def St.replace (σ : St) (it : Items) (rv : GoString) : St := { σ with items := it, rv := rv }

/-- `Bookmark(rv)`: the resource version set. -/
def St.bookmark (σ : St) (rv : GoString) : St := { σ with rv := rv }

/-! ### Updating one indexer's index -/

/-- The keys per value after deleting `k` from the sets of `vs`. -/
def delVals (V : GoString → KSet) (vs : List GoString) (k : GoString) : GoString → KSet :=
  fun v => if v ∈ vs then GMap.delete k (V v) else V v

/-- The keys per value after adding `k` to the sets of `vs`. -/
def addVals (V : GoString → KSet) (vs : List GoString) (k : GoString) : GoString → KSet :=
  fun v => if v ∈ vs then <[k := present]> (V v) else V v

theorem delVals_nil (V : GoString → KSet) (k : GoString) : delVals V [] k = V := by
  funext v; simp [delVals]

theorem addVals_nil (V : GoString → KSet) (k : GoString) : addVals V [] k = V := by
  funext v; simp [addVals]

theorem mem_ins (m : KSet) (k k' : GoString) : k ∈ <[k' := present]> m ↔ k = k' ∨ k ∈ m := by
  simp only [GMap.mem_iff, GMap.lookup_insert_eq_iff]
  by_cases h : k' = k
  · subst h; simp
  · simp [h, Ne.symm h]

theorem mem_del (m : KSet) (k k' : GoString) : k ∈ GMap.delete k' m ↔ k ≠ k' ∧ k ∈ m := by
  simp only [GMap.mem_iff, GMap.lookup_delete_iff]
  by_cases h : k' = k
  · subst h; simp
  · simp [h, Ne.symm h]

theorem delVals_snoc (V : GoString → KSet) (vs : List GoString) (v k : GoString) :
    delVals V (vs ++ [v]) k = fun w => if w = v then GMap.delete k (delVals V vs k w)
      else delVals V vs k w := by
  funext w
  unfold delVals
  by_cases hw : w = v
  · subst hw
    by_cases hin : w ∈ vs
    · simp only [List.mem_append, hin, true_or, ↓reduceIte]
      ext k'
      simp only [GMap.lookup_delete_iff]
      split <;> rfl
    · simp [hin]
  · simp [hw]

theorem addVals_snoc (V : GoString → KSet) (vs : List GoString) (v k : GoString) :
    addVals V (vs ++ [v]) k = fun w => if w = v then <[k := present]> (addVals V vs k w)
      else addVals V vs k w := by
  funext w
  unfold addVals
  by_cases hw : w = v
  · subst hw
    by_cases hin : w ∈ vs
    · simp only [List.mem_append, hin, true_or, ↓reduceIte]
      ext k'
      simp only [GMap.lookup_insert_eq_iff]
      split <;> rfl
    · simp [hin]
  · simp [hw]

/-- **`updateSingleIndex`'s step** (`thread_safe_store.go:174`): the items changed only at `key`;
the index had exactly the keys of the old items. Deleting `key` from the sets of its old object's
values and adding it to those of its new object's values gives exactly the keys of the new
items. -/
theorem updN_ok {F : Fn} {it it' : Items} {key : GoString} {V : GoString → KSet}
    (hV : ∀ v k, k ∈ V v ↔ inIdx F it v k)
    (hsame : ∀ k, k ≠ key → objAt it' k = objAt it k) :
    ∀ v k, k ∈ addVals (delVals V (valsOf F (objAt it key)) key)
      (valsOf F (objAt it' key)) key v ↔ inIdx F it' v k := by
  intro v k
  unfold addVals delVals
  by_cases hk : k = key
  · subst hk
    unfold inIdx
    by_cases hnew : v ∈ valsOf F (objAt it' k)
    · simp only [hnew, ↓reduceIte, mem_ins, true_or]
    · simp only [hnew, ↓reduceIte, iff_false]
      by_cases hold : v ∈ valsOf F (objAt it k)
      · simp [hold, mem_del]
      · simp only [hold, ↓reduceIte]
        intro h
        exact hold ((hV v k).1 h)
  · have hi : inIdx F it' v k ↔ inIdx F it v k := by unfold inIdx; rw [hsame k hk]
    rw [hi, ← hV v k]
    split <;> split <;> simp [mem_ins, mem_del, hk]

/-- The optimized case of `updateSingleIndex`: the old and new objects index under the same single
value, so the index (exact for the old items) is exact for the new. -/
theorem updN_same {F : Fn} {it it' : Items} {key : GoString} {V : GoString → KSet} (a : GoString)
    (hV : ∀ v k, k ∈ V v ↔ inIdx F it v k)
    (hsame : ∀ k, k ≠ key → objAt it' k = objAt it k)
    (hold : valsOf F (objAt it key) = [a]) (hnew : valsOf F (objAt it' key) = [a]) :
    ∀ v k, k ∈ V v ↔ inIdx F it' v k := by
  intro v k
  rw [hV v k]
  by_cases hk : k = key
  · subst hk; unfold inIdx; rw [hold, hnew]
  · unfold inIdx; rw [hsame k hk]

end model

end cache
end EtcdGrove
end Perennial
