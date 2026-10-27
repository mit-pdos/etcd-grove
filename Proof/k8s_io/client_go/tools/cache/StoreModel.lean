/-
The pure model of client-go's thread-safe store (`tools/cache/thread_safe_store.go`): its items,
the items' recorded index values, and the indices, as the abstract state `St` and the physical
index `Ix` the proofs relate it to. Lean-first; phase 2 of the DaemonSet plan
(`notes/k8s-daemonset-plan.md`).

* **Index values are recorded per item** (`IV`: key → indexer name → values; 2026-10-27, phase 4's
  third round): an index function reads its object in the heap, so its values are no pure function
  of the interface value; the store's lock invariant (`TSDefs.lean`'s `tsP`) records them, with each
  indexer's contract a relation between an object and its values (`StoreDefs.lean`'s `Fn`, `fnOk`).
* `inIdx W v k`: key `k` is in the index of value `v` for an indexer whose values per key are `W`
  (`ivAt iv n`). `ivWf`: values only for present, non-`nil` items (a `nil` object is stored but
  never indexed: `updateSingleIndex` skips it) and only under the indexers' names.
* The physical index of one indexer (`IxN`) maps each indexed value to its set's location and
  keys; `viewN` is the keys per value (none for a value it lacks). `nameOk W X`: `X`'s keys are
  exactly those `inIdx`. `updN_ok` is what `updateSingleIndex` relies on: deleting the key from the
  sets of its old values, then adding it to those of its new values, keeps `nameOk` for the values
  changed at that key (`ixOk_step`: one indexer's step of the indices' update).
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

/-- The items, by key. -/
abbrev Items : Type := GMap GoString GoInterface
/-- A set of keys (`sets.Set[string]`). -/
abbrev KSet : Type := GMap GoString Elem
/-- One indexer's physical index: each value's set (its location and keys). -/
abbrev IxN : Type := GMap GoString (Loc × KSet)
/-- The physical indices: each indexer's index (its location and contents). -/
abbrev Ix : Type := GMap GoString (Loc × IxN)
/-- One item's index values: for each indexer, by name, the values its object is indexed under. -/
abbrev Vals : Type := GMap GoString (List GoString)
/-- **The items' index values**, by key (recorded per item: an index function reads its object in
the heap, so its values are not a pure function of the interface value). -/
abbrev IV : Type := GMap GoString Vals

/-- The object at a key (`nil` if none, as `c.items[key]`). -/
def objAt (it : Items) (k : GoString) : GoInterface := (it !! k).getD interface.nil

/-- An item's values under indexer `n` (none if it has none recorded). -/
def vsAt (vs : Vals) (n : GoString) : List GoString := (vs !! n).getD []

/-- The index values recorded for key `k`. -/
def ivOf (iv : IV) (k : GoString) : Vals := (iv !! k).getD ∅

/-- The values recorded for key `k` under indexer `n`. -/
def ivAt (iv : IV) (n k : GoString) : List GoString := vsAt (ivOf iv k) n

/-- Key `k` is in the index of value `v`, for an indexer whose values per key are `W`. -/
def inIdx (W : GoString → List GoString) (v k : GoString) : Prop := v ∈ W k

/-- The keys of value `v` in an indexer's physical index. -/
def viewN (X : IxN) (v : GoString) : KSet := ((X !! v).map Prod.snd).getD ∅

/-- An indexer's physical index is exact for the values `W` per key. -/
def nameOk (W : GoString → List GoString) (X : IxN) : Prop := ∀ v k, k ∈ viewN X v ↔ inIdx W v k

/-- An indexer's physical index (empty if none). -/
def ixAt (ix : Ix) (n : GoString) : IxN := ((ix !! n).map Prod.snd).getD ∅

/-- The location of value `v`'s set in indexer `n`'s index (`nil` if none). -/
def setLoc (ix : Ix) (n v : GoString) : Loc :=
  ((ix !! n).bind (fun e => (e.2 !! v).map Prod.fst)).getD null

/-- The physical indices are exact for the recorded values `iv`, for each indexer (`fns`'s names),
and only indexers have one. -/
def ixOk {R : Type _} (fns : GMap GoString R) (iv : IV) (ix : Ix) : Prop :=
  (∀ n, n ∈ ix → n ∈ fns) ∧ ∀ n, n ∈ fns → nameOk (ivAt iv n) (ixAt ix n)

/-- Values are recorded only for present, non-`nil` items (a `nil` object is stored but never
indexed: `updateSingleIndex` skips it) and only under the indexers' names. -/
def ivWf {R : Type _} (fns : GMap GoString R) (it : Items) (iv : IV) : Prop :=
  ∀ k n, (objAt it k = interface.nil ∨ n ∉ fns) → ivAt iv n k = []

/-- **The store's abstract state**: its items, its resource version and its indexers, each named
by its index in the client's family of index functions' contracts (`Fam`, a parameter of the
store's specs, `StoreDefs.lean`'s `Fn`: relations between an object and its values; not a
countable value, so the ghost state holds the index). -/
structure St where
  items : Items
  rv : GoString
  fnIds : GMap GoString Nat

/-- The indexers' functions. -/
def St.fns {R : Type _} (Fam : Nat → R) (σ : St) : GMap GoString R := GMap.fmap Fam σ.fnIds

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

/-- The resource version `DeleteWithObject(key, obj)` takes: none for a `nil` object. -/
def rvOfObj (rvOf : GoInterface → Option GoString) (o : GoInterface) : Option GoString :=
  if o = interface.nil then none else rvOf o

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

/-- **`updateSingleIndex`'s step** (`thread_safe_store.go:174`): the values per key changed only at
`key` (from `W` to `W'`); the index had exactly the keys of `W`. Deleting `key` from the sets of its
old values and adding it to those of its new values gives exactly the keys of `W'`. -/
theorem updN_ok {W W' : GoString → List GoString} {key : GoString} {V : GoString → KSet}
    (hV : ∀ v k, k ∈ V v ↔ inIdx W v k)
    (hsame : ∀ k, k ≠ key → W' k = W k) :
    ∀ v k, k ∈ addVals (delVals V (W key) key) (W' key) key v ↔ inIdx W' v k := by
  intro v k
  unfold addVals delVals
  by_cases hk : k = key
  · subst hk
    unfold inIdx
    by_cases hnew : v ∈ W' k
    · simp only [hnew, ↓reduceIte, mem_ins, true_or]
    · simp only [hnew, ↓reduceIte, iff_false]
      by_cases hold : v ∈ W k
      · simp [hold, mem_del]
      · simp only [hold, ↓reduceIte]
        intro h
        exact hold ((hV v k).1 h)
  · have hi : inIdx W' v k ↔ inIdx W v k := by unfold inIdx; rw [hsame k hk]
    rw [hi, ← hV v k]
    split <;> split <;> simp [mem_ins, mem_del, hk]

/-- The optimized case of `updateSingleIndex`: the old and new values are the same single value, so
the index (exact for the old values) is exact for the new. -/
theorem updN_same {W W' : GoString → List GoString} {key : GoString} {V : GoString → KSet}
    (a : GoString)
    (hV : ∀ v k, k ∈ V v ↔ inIdx W v k)
    (hsame : ∀ k, k ≠ key → W' k = W k)
    (hold : W key = [a]) (hnew : W' key = [a]) :
    ∀ v k, k ∈ V v ↔ inIdx W' v k := by
  intro v k
  rw [hV v k]
  by_cases hk : k = key
  · subst hk; unfold inIdx; rw [hold, hnew]
  · unfold inIdx; rw [hsame k hk]

/-- The items at some keys (`Replace`'s re-indexing, the keys visited so far). -/
def restrictK (it : Items) (ks : List GoString) : Items :=
  GMap.filter (fun k _ => decide (k ∈ ks)) it

theorem objAt_restrictK (it : Items) (ks : List GoString) (k : GoString) :
    objAt (restrictK it ks) k = if k ∈ ks then objAt it k else interface.nil := by
  unfold objAt restrictK
  rw [GMap.lookup_filter]
  cases it !! k <;> by_cases h : k ∈ ks <;> simp [h, Option.filter]

theorem restrictK_all (it : Items) (ks : List GoString) (h : ∀ k, k ∈ it → k ∈ ks) :
    restrictK it ks = it := by
  ext k
  unfold restrictK
  rw [GMap.lookup_filter]
  cases hk : it !! k with
  | none => rfl
  | some o =>
    have : k ∈ ks := h k (by rw [GMap.mem_iff, hk]; rfl)
    simp [Option.filter, this]

theorem restrictK_nil (it : Items) : restrictK it [] = ∅ := by
  ext k
  unfold restrictK
  rw [GMap.lookup_filter]
  cases it !! k <;> simp [Option.filter]

theorem vsAt_insert (vs : Vals) (n m : GoString) (l : List GoString) :
    vsAt (<[m := l]> vs) n = if n = m then l else vsAt vs n := by
  unfold vsAt
  by_cases h : n = m
  · subst h; simp
  · simp [h, Ne.symm h]

theorem ivAt_insert (iv : IV) (key n k : GoString) (vs : Vals) :
    ivAt (<[key := vs]> iv) n k = if k = key then vsAt vs n else ivAt iv n k := by
  unfold ivAt ivOf
  by_cases h : k = key
  · subst h; simp
  · simp [h, Ne.symm h]

theorem vsAt_empty (n : GoString) : vsAt ∅ n = [] := by simp [vsAt]

theorem ivAt_empty (n k : GoString) : ivAt ∅ n k = [] := by simp [ivAt, ivOf, vsAt]

/-- `ixOk` depends on the recorded values of the indexers only. -/
theorem ixOk_congr {R : Type _} {fns : GMap GoString R} {iv iv' : IV} {ix : Ix}
    (h : ixOk fns iv ix) (he : ∀ n, n ∈ fns → ∀ k, ivAt iv' n k = ivAt iv n k) :
    ixOk fns iv' ix := by
  refine ⟨h.1, fun n hn v k => ?_⟩
  unfold inIdx; rw [he n hn k]; exact h.2 n hn v k

/-- No index for no values. -/
theorem ixOk_empty {R : Type _} (fns : GMap GoString R) : ixOk fns ∅ ∅ := by
  refine ⟨fun n hn => by simp [GMap.mem_iff] at hn, fun n _ v k => ?_⟩
  unfold ixAt viewN inIdx
  simp [GMap.mem_iff, ivAt_empty]

/-- What `updateSingleIndex` leaves in the indexer's index, from the old values `ovs` to the new
`nvs`: the key deleted from the sets of the old values and added to those of the new, or (the
optimized case: both the same single value) the index unchanged. -/
def updNPost (ovs nvs : List GoString) (key : GoString) (V V' : GoString → KSet) : Prop :=
  V' = addVals (delVals V ovs key) nvs key ∨
  ∃ a, ovs = [a] ∧ nvs = [a] ∧ V' = V

/-- `updateSingleIndex` keeps an index exact when the values change at the key only. -/
theorem nameOk_upd {W W' : GoString → List GoString} {key : GoString} {X X' : IxN}
    (hX : nameOk W X) (hsame : ∀ k, k ≠ key → W' k = W k)
    (h : updNPost (W key) (W' key) key (viewN X) (viewN X')) :
    nameOk W' X' := by
  intro v k
  rcases h with h | ⟨a, ha, hb, h⟩
  · rw [h]; exact updN_ok hX hsame v k
  · rw [h]; exact updN_same a hX hsame ha hb v k

/-- **One step of the indices' update** (`updateIndices`' loop, `AddIndexers`' and `Replace`'s
re-indexing): `key`'s values `vs`; indexer `name`'s index updated by `updateSingleIndex` from its
values in `vs` to `nvs`. The indices stay exact, for the values with `name`'s replaced. -/
theorem ixOk_step {R : Type _} {fns : GMap GoString R} {iv : IV} {ix ix' : Ix} {vs : Vals}
    {name key : GoString} {nvs : List GoString}
    (h : ixOk fns (<[key := vs]> iv) ix) (hname : name ∈ fns)
    (hother : ∀ n, n ≠ name → ix' !! n = ix !! n)
    (hupd : updNPost (vsAt vs name) nvs key (viewN (ixAt ix name)) (viewN (ixAt ix' name))) :
    ixOk fns (<[key := <[name := nvs]> vs]> iv) ix' := by
  refine ⟨fun n hn => ?_, fun n hn => ?_⟩
  · by_cases hnn : n = name
    · subst hnn; exact hname
    · apply h.1 n
      rw [GMap.mem_iff] at hn ⊢
      rwa [hother n hnn] at hn
  · by_cases hnn : n = name
    · subst hnn
      have h0 := h.2 n hn
      refine nameOk_upd (W := ivAt (<[key := vs]> iv) n) (key := key) h0 (fun k hk => ?_) ?_
      · rw [ivAt_insert, ivAt_insert]; simp [hk]
      · rw [ivAt_insert, ivAt_insert]; simp only [↓reduceIte, vsAt_insert]; exact hupd
    · have hx : ixAt ix' n = ixAt ix n := by unfold ixAt; rw [hother n hnn]
      rw [hx]
      have he : ivAt (<[key := <[name := nvs]> vs]> iv) n = ivAt (<[key := vs]> iv) n := by
        funext k; rw [ivAt_insert, ivAt_insert, vsAt_insert]; simp [hnn]
      rw [he]; exact h.2 n hn

/-- Recording a key's values as they were changes nothing. -/
theorem ivAt_insert_self (iv : IV) (key n k : GoString) :
    ivAt (<[key := ivOf iv key]> iv) n k = ivAt iv n k := by
  rw [ivAt_insert]; split <;> simp_all [ivAt]

theorem objAt_insert (it : Items) (k k' : GoString) (o : GoInterface) :
    objAt (<[k := o]> it) k' = if k' = k then o else objAt it k' := by
  unfold objAt
  by_cases h : k' = k
  · subst h; simp
  · simp [h, Ne.symm h]

theorem objAt_delete (it : Items) (k k' : GoString) :
    objAt (GMap.delete k it) k' = if k' = k then interface.nil else objAt it k' := by
  unfold objAt
  by_cases h : k' = k
  · subst h; simp
  · simp [h, Ne.symm h]

theorem ivOf_insert (iv : IV) (k k' : GoString) (vs : Vals) :
    ivOf (<[k := vs]> iv) k' = if k' = k then vs else ivOf iv k' := by
  unfold ivOf
  by_cases h : k' = k
  · subst h; simp
  · simp [h, Ne.symm h]

/-- `ivWf` after storing `o` at `k` with values `vs` (none if `o` is `nil` or for a non-indexer). -/
theorem ivWf_insert {R : Type _} {fns : GMap GoString R} {it : Items} {iv : IV} {k : GoString}
    {o : GoInterface} {vs : Vals} (h : ivWf fns it iv)
    (hvs : ∀ n, (o = interface.nil ∨ n ∉ fns) → vsAt vs n = []) :
    ivWf fns (<[k := o]> it) (<[k := vs]> iv) := by
  intro k' n hk'
  rw [objAt_insert] at hk'
  rw [ivAt_insert]
  by_cases hkk : k' = k
  · simp only [hkk, ↓reduceIte] at hk' ⊢; exact hvs n hk'
  · simp only [hkk, ↓reduceIte] at hk' ⊢; exact h k' n hk'

/-- `ivWf` after deleting `k`, its values `vs` none. -/
theorem ivWf_delete {R : Type _} {fns : GMap GoString R} {it : Items} {iv : IV} {k : GoString}
    {vs : Vals} (h : ivWf fns it iv) (hvs : ∀ n, vsAt vs n = []) :
    ivWf fns (GMap.delete k it) (<[k := vs]> iv) := by
  intro k' n hk'
  rw [objAt_delete] at hk'
  rw [ivAt_insert]
  by_cases hkk : k' = k
  · simp only [hkk, ↓reduceIte]; exact hvs n
  · simp only [hkk, ↓reduceIte] at hk' ⊢; exact h k' n hk'

theorem ivWf_empty {R : Type _} (fns : GMap GoString R) (it : Items) : ivWf fns it ∅ :=
  fun _ _ _ => ivAt_empty _ _

/-- The new values `vs` of a key (`updateIndices`' result) are none where `ivWf` wants none: under
non-indexers they are the old ones (none), and for `nil` none under the indexers. -/
theorem vs_wf {R : Type _} {fns : GMap GoString R} {it : Items} {iv : IV} {key : GoString}
    {o : GoInterface} {vs : Vals} (hwf : ivWf fns it iv)
    (hnil : o = interface.nil → ∀ n, n ∈ fns → vsAt vs n = [])
    (hrest : ∀ n, n ∉ fns → vsAt vs n = ivAt iv n key) :
    ∀ n, (o = interface.nil ∨ n ∉ fns) → vsAt vs n = [] := by
  intro n h
  by_cases hn : n ∈ fns
  · rcases h with h | h
    · exact hnil h n hn
    · exact absurd hn h
  · rw [hrest n hn]; exact hwf key n (Or.inr hn)

/-- One more key visited (`Replace`'s and `AddIndexers`' loops over the items). -/
theorem restrictK_snoc (it : Items) (ks : List GoString) (k : GoString) (o : GoInterface)
    (h : it !! k = some o) :
    restrictK it (ks ++ [k]) = <[k := o]> (restrictK it ks) := by
  ext k'
  unfold restrictK
  rw [GMap.lookup_filter]
  by_cases hk : k' = k
  · subst hk; simp [h, Option.filter]
  · rw [GMap.lookup_insert_ne _ _ (Ne.symm hk), GMap.lookup_filter]
    cases it !! k' <;> simp [Option.filter, hk]

end model

end cache
end EtcdGrove
end Perennial
