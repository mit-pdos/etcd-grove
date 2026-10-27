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

/-- **The store's abstract state**: its items, its resource version and its indexers, each named
by its index in the client's family of index functions (`Fam : Nat → Fn`, a parameter of the
store's specs; a function is not a countable value, so the ghost state holds the index). -/
structure St where
  items : Items
  rv : GoString
  fnIds : GMap GoString Nat

/-- The indexers' functions. -/
def St.fns (Fam : Nat → Fn) (σ : St) : GMap GoString Fn := GMap.fmap Fam σ.fnIds

instance St.countable : Pos.Countable St :=
  .ofInjective (fun σ => Pos.Countable.encode (σ.items, σ.rv, σ.fnIds)) (by
    rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
    simp only [Pos.encode_eq_iff, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rfl)

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

/-- What `updateSingleIndex` leaves in the indexer's index: the key deleted from the sets of the
old object's values and added to those of the new object's, or (the optimized case: both objects
index under the same single value) the index unchanged. -/
def updNPost (F : Fn) (old new : GoInterface) (key : GoString) (V V' : GoString → KSet) : Prop :=
  V' = addVals (delVals V (valsOf F old) key) (valsOf F new) key ∨
  ∃ a, valsOf F old = [a] ∧ valsOf F new = [a] ∧ V' = V

/-- `updateSingleIndex` keeps an index exact when the items change at the key only. -/
theorem nameOk_upd {F : Fn} {it it' : Items} {key : GoString} {X X' : IxN}
    (hX : nameOk F it X) (hsame : ∀ k, k ≠ key → objAt it' k = objAt it k)
    (h : updNPost F (objAt it key) (objAt it' key) key (viewN X) (viewN X')) :
    nameOk F it' X' := by
  intro v k
  rcases h with h | ⟨a, ha, hb, h⟩
  · rw [h]; exact updN_ok hX hsame v k
  · rw [h]; exact updN_same a hX hsame ha hb v k

/-- **`updateIndices`' loop invariant**: the indexers visited so far (`done`) are exact for the
new items, the others for the old ones; only indexers have an index. -/
def ixOkPart (fns : GMap GoString Fn) (it it' : Items) (done : List GoString) (ix : Ix) : Prop :=
  (∀ n, n ∈ ix → n ∈ fns) ∧
  ∀ n F, fns !! n = some F → nameOk F (if n ∈ done then it' else it) (ixAt ix n)

theorem ixOkPart_nil {fns : GMap GoString Fn} {it it' : Items} {ix : Ix} (h : ixOk fns it ix) :
    ixOkPart fns it it' [] ix := by
  refine ⟨h.1, fun n F hF => ?_⟩
  simp only [List.not_mem_nil, ↓reduceIte]
  exact h.2 n F hF

theorem ixOkPart_done {fns : GMap GoString Fn} {it it' : Items} {done : List GoString} {ix : Ix}
    (h : ixOkPart fns it it' done ix) (hall : ∀ n, n ∈ fns → n ∈ done) : ixOk fns it' ix := by
  refine ⟨h.1, fun n F hF => ?_⟩
  have hn : n ∈ fns := by simp [GMap.mem_iff, hF]
  have := h.2 n F hF
  simp only [hall n hn, ↓reduceIte] at this
  exact this

/-- One step of `updateIndices`: indexer `name` (not yet visited) updated by `updateSingleIndex`. -/
theorem ixOkPart_step {fns : GMap GoString Fn} {it it' : Items} {done : List GoString}
    {ix ix' : Ix} {name key : GoString} {F : Fn}
    (h : ixOkPart fns it it' done ix) (hF : fns !! name = some F) (hnd : name ∉ done)
    (hsame : ∀ k, k ≠ key → objAt it' k = objAt it k)
    (hother : ∀ n, n ≠ name → ix' !! n = ix !! n)
    (hupd : updNPost F (objAt it key) (objAt it' key) key (viewN (ixAt ix name))
      (viewN (ixAt ix' name))) :
    ixOkPart fns it it' (done ++ [name]) ix' := by
  refine ⟨fun n hn => ?_, fun n G hG => ?_⟩
  · by_cases hnn : n = name
    · subst hnn; simp [GMap.mem_iff, hF]
    · apply h.1 n
      rw [GMap.mem_iff] at hn ⊢
      rwa [hother n hnn] at hn
  · by_cases hnn : n = name
    · subst hnn
      rw [hF] at hG; cases hG
      have h0 := h.2 n F hF
      simp only [hnd, ↓reduceIte] at h0
      simp only [List.mem_append, List.mem_singleton, or_true, ↓reduceIte]
      exact nameOk_upd h0 hsame hupd
    · have hx : ixAt ix' n = ixAt ix n := by unfold ixAt; rw [hother n hnn]
      rw [hx]
      have h0 := h.2 n G hG
      have hm : (n ∈ done ++ [name]) ↔ n ∈ done := by simp [hnn]
      simp only [hm]
      exact h0

end model

end cache
end EtcdGrove
end Perennial
