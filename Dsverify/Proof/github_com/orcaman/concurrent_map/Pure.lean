/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/cmap/Pure.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The concurrent map's pure vocabulary: the hash `fnv32F` (the Go loop of `fnv32` as a fold), the
shard of a key `shardOf n k`, the part of a map in a shard `shardPart n i M`, and the trace of
an `IterCb` pass (`iterTrace`), with the facts the proofs and the clients use.
-/
module

public import Perennial.Golang.Theory

@[expose] public section

noncomputable section

namespace Perennial.github_com.orcaman.concurrent_map

set_option linter.unusedSectionVars false

variable [GooseExts]

/-- One step of `fnv32`'s loop: `hash *= prime32; hash ^= uint32(key[i])`. -/
def fnv32Step (h : w32) (b : w8) : w32 := h * W32 16777619 ^^^ W32 (uint.Z b)

/-- `fnv32(key)`, as Go computes it. -/
def fnv32F (key : GoString) : w32 := key.foldl fnv32Step (W32 2166136261)

/-- The shard of key `k` in a map of `n` shards: `uint(fnv32(k)) % uint(n)`. -/
def shardOf (n : Nat) (k : GoString) : Nat := uint.nat (fnv32F k) % n

/-- The entries of `M` whose key is in shard `i` (of `n`). -/
def shardPart (n i : Nat) (M : GMap GoString GoInterface) : GMap GoString GoInterface :=
  M.filter (fun k _ => decide (shardOf n k = i))

theorem shardOf_lt (n : Nat) (k : GoString) (h : 0 < n) : shardOf n k < n :=
  Nat.mod_lt _ h

theorem lookup_shardPart (n i : Nat) (M : GMap GoString GoInterface) (k : GoString) :
    shardPart n i M !! k = if shardOf n k = i then M !! k else none := by
  unfold shardPart
  rw [GMap.lookup_filter]
  cases M !! k <;> by_cases h : shardOf n k = i <;> simp [h, Option.filter]

theorem lookup_shardPart_same (n : Nat) (M : GMap GoString GoInterface) (k : GoString) :
    shardPart n (shardOf n k) M !! k = M !! k := by
  rw [lookup_shardPart]; simp

theorem shardPart_empty (n i : Nat) : shardPart n i (∅ : GMap GoString GoInterface) = ∅ := by
  apply GMap.map_eq; intro k; rw [lookup_shardPart]; split <;> rfl

theorem shardPart_insert (n i : Nat) (M : GMap GoString GoInterface) (k : GoString)
    (v : GoInterface) :
    shardPart n i (<[k := v]> M) =
      if shardOf n k = i then <[k := v]> (shardPart n i M) else shardPart n i M := by
  apply GMap.map_eq; intro k'
  by_cases hk : k = k'
  · subst hk
    by_cases h : shardOf n k = i <;> simp [lookup_shardPart, h]
  · by_cases h : shardOf n k = i <;> by_cases h' : shardOf n k' = i <;>
      simp [lookup_shardPart, h, h', hk]

theorem shardPart_delete (n i : Nat) (M : GMap GoString GoInterface) (k : GoString) :
    shardPart n i (GMap.delete k M) =
      if shardOf n k = i then GMap.delete k (shardPart n i M) else shardPart n i M := by
  apply GMap.map_eq; intro k'
  by_cases hk : k = k'
  · subst hk
    by_cases h : shardOf n k = i <;> simp [lookup_shardPart, h]
  · by_cases h : shardOf n k = i <;> by_cases h' : shardOf n k' = i <;>
      simp [lookup_shardPart, h, h', hk]

/-! ### Map entries as lists -/

/-- The entries of `M` at the keys `keys`, in their order. -/
def entriesOf (M : GMap GoString GoInterface) (keys : List GoString) :
    List (GoString × GoInterface) :=
  keys.filterMap (fun k => (M !! k).map (fun v => (k, v)))

theorem entriesOf_take_succ (M : GMap GoString GoInterface) (keys : List GoString) (j : Nat)
    (k : GoString) (v : GoInterface) (hk : keys[j]? = some k) (hv : M !! k = some v) :
    entriesOf M (keys.take (j + 1)) = entriesOf M (keys.take j) ++ [(k, v)] := by
  unfold entriesOf
  rw [List.take_add_one, hk]
  simp [List.filterMap_append, hv]

theorem nodup_of_map_fst {A B : Type} (l : List (A × B)) (h : (l.map Prod.fst).Nodup) :
    l.Nodup :=
  List.Pairwise.of_map Prod.fst (fun _ _ h e => h (congrArg Prod.fst e)) h

theorem toList_nodup (M : GMap GoString GoInterface) : M.toList.Nodup :=
  nodup_of_map_fst _ (GMap.toList_keys_nodup M)

theorem entriesOf_keys (M : GMap GoString GoInterface) (keys : List GoString) :
    (entriesOf M keys).map Prod.fst = keys.filter (fun k => (M !! k).isSome) := by
  induction keys with
  | nil => rfl
  | cons k keys ih =>
    unfold entriesOf at ih ⊢
    cases h : M !! k <;> simp [h, ih]

theorem entriesOf_perm (M : GMap GoString GoInterface) (keys : List GoString)
    (hmem : ∀ k, k ∈ keys ↔ (M !! k).isSome) (hnd : keys.Nodup) :
    (entriesOf M keys).Perm M.toList := by
  have hnd' : (entriesOf M keys).Nodup := by
    apply nodup_of_map_fst
    rw [entriesOf_keys]
    exact hnd.filter _
  rw [List.perm_ext_iff_of_nodup hnd' (toList_nodup M)]
  rintro ⟨k, v⟩
  rw [GMap.mem_toList]
  unfold entriesOf
  simp only [List.mem_filterMap, Option.map_eq_some_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨k', _, v', h, rfl, rfl⟩; exact h
  · intro h; exact ⟨k, (hmem k).2 (by simp [h]), v, h, rfl, rfl⟩

/-- Two maps with disjoint domains, listed one after the other, list their union `C`. -/
theorem toList_append_perm (A B C : GMap GoString GoInterface)
    (hdis : ∀ k, (A !! k).isSome → (B !! k).isSome → False)
    (hC : ∀ k v, C !! k = some v ↔ A !! k = some v ∨ B !! k = some v) :
    (A.toList ++ B.toList).Perm C.toList := by
  have hnd : (A.toList ++ B.toList).Nodup := by
    rw [List.nodup_append]
    refine ⟨toList_nodup A, toList_nodup B, ?_⟩
    rintro ⟨k, v⟩ ha ⟨k', v'⟩ hb heq
    cases heq
    rw [GMap.mem_toList] at ha hb
    exact hdis k (by simp [ha]) (by simp [hb])
  rw [List.perm_ext_iff_of_nodup hnd (toList_nodup C)]
  rintro ⟨k, v⟩
  rw [List.mem_append, GMap.mem_toList, GMap.mem_toList, GMap.mem_toList, hC]

/-! ### The trace of an `IterCb` pass -/

/-- After `i` shards: `obs` are the maps observed at their read locks (one per shard), and the
entries visited `vis` are, shard by shard, a permutation of the observed map's part in it. -/
def iterTraceUpTo (n i : Nat) (obs : List (GMap GoString GoInterface))
    (vis : List (GoString × GoInterface)) : Prop :=
  obs.length = i ∧ ∃ ls : List (List (GoString × GoInterface)), ls.length = i ∧
    vis = ls.flatten ∧
    ∀ (j : Nat) (M : GMap GoString GoInterface) (l : List (GoString × GoInterface)),
      obs[j]? = some M → ls[j]? = some l → l.Perm (shardPart n j M).toList

/-- A whole pass over the `n` shards. -/
def iterTrace (n : Nat) (obs : List (GMap GoString GoInterface))
    (vis : List (GoString × GoInterface)) : Prop :=
  0 < n ∧ iterTraceUpTo n n obs vis

theorem iterTraceUpTo_nil (n : Nat) : iterTraceUpTo n 0 [] [] :=
  ⟨rfl, [], rfl, rfl, fun _ _ _ h => by simp at h⟩

theorem iterTraceUpTo_snoc (n i : Nat) (obs : List (GMap GoString GoInterface))
    (vis : List (GoString × GoInterface)) (M : GMap GoString GoInterface)
    (l : List (GoString × GoInterface)) (h : iterTraceUpTo n i obs vis)
    (hl : l.Perm (shardPart n i M).toList) :
    iterTraceUpTo n (i + 1) (obs ++ [M]) (vis ++ l) := by
  obtain ⟨hlen, ls, hls, rfl, hperm⟩ := h
  refine ⟨by simp [hlen], ls ++ [l], by simp [hls], by simp, ?_⟩
  intro j M' l' hM hl'
  by_cases hj : j < i
  · rw [List.getElem?_append_left (by omega)] at hM
    rw [List.getElem?_append_left (by omega)] at hl'
    exact hperm j M' l' hM hl'
  · have hj' : j = i := by
      have := (List.getElem?_eq_some_iff.mp hM).1
      simp [hlen] at this; omega
    subst hj'
    rw [List.getElem?_append_right (by omega), hlen, Nat.sub_self] at hM
    rw [List.getElem?_append_right (by omega), hls, Nat.sub_self] at hl'
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hM hl'
    subst hM hl'
    exact hl

/-! ### What a pass gives a client -/

/-- (1') A key present in the map at every shard's observation is visited, with the value one
observation saw. -/
theorem iterTrace_visits (n : Nat) (obs : List (GMap GoString GoInterface))
    (vis : List (GoString × GoInterface)) (k : GoString) (h : iterTrace n obs vis)
    (hk : ∀ M ∈ obs, (M !! k).isSome) :
    ∃ v, (k, v) ∈ vis ∧ ∃ M ∈ obs, M !! k = some v := by
  obtain ⟨hn, hlen, ls, hls, rfl, hperm⟩ := h
  have hj := shardOf_lt n k hn
  obtain ⟨M, hM⟩ : ∃ M, obs[shardOf n k]? = some M :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨l, hl⟩ : ∃ l, ls[shardOf n k]? = some l :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have hMmem : M ∈ obs := List.mem_of_getElem? hM
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hk M hMmem)
  refine ⟨v, ?_, M, hMmem, hv⟩
  have hin : (k, v) ∈ (shardPart n (shardOf n k) M).toList := by
    rw [GMap.mem_toList, lookup_shardPart_same]; exact hv
  have hin' : (k, v) ∈ l := (hperm _ _ _ hM hl).mem_iff.mpr hin
  exact List.mem_flatten.mpr ⟨l, List.mem_of_getElem? hl, hin'⟩

/-- (1') with the value: an entry present at every observation is visited. -/
theorem iterTrace_visits_entry (n : Nat) (obs : List (GMap GoString GoInterface))
    (vis : List (GoString × GoInterface)) (k : GoString) (v : GoInterface)
    (h : iterTrace n obs vis) (hk : ∀ M ∈ obs, M !! k = some v) : (k, v) ∈ vis := by
  obtain ⟨v', hv', M, hM, hMk⟩ := iterTrace_visits n obs vis k h (fun M hM => by simp [hk M hM])
  rw [hk M hM] at hMk
  cases hMk
  exact hv'

/-- The parts of `M` in the shards below `i`. -/
private def belowPart (n i : Nat) (M : GMap GoString GoInterface) : GMap GoString GoInterface :=
  M.filter (fun k _ => decide (shardOf n k < i))

/-- (2') When every observation saw the same map `M` (no concurrent writer), the entries
visited are exactly `M`'s, each once. -/
theorem iterTrace_perm (n : Nat) (obs : List (GMap GoString GoInterface))
    (vis : List (GoString × GoInterface)) (M : GMap GoString GoInterface)
    (h : iterTrace n obs vis) (hobs : ∀ M' ∈ obs, M' = M) : vis.Perm M.toList := by
  obtain ⟨hn, hlen, ls, hls, rfl, hperm⟩ := h
  have hstep : ∀ i, i ≤ n → (ls.take i).flatten.Perm (belowPart n i M).toList := by
    intro i
    induction i with
    | zero =>
      intro _
      have : belowPart n 0 M = ∅ := by
        apply GMap.map_eq; intro k; simp [belowPart, Option.filter]
        cases M !! k <;> rfl
      simp [this]
    | succ i ih =>
      intro hi
      obtain ⟨l, hl⟩ : ∃ l, ls[i]? = some l := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      obtain ⟨M', hM'⟩ : ∃ M', obs[i]? = some M' := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      have hMeq : M' = M := hobs M' (List.mem_of_getElem? hM')
      subst hMeq
      rw [List.take_add_one, hl]
      simp only [Option.toList_some, List.flatten_append, List.flatten_singleton]
      refine (List.Perm.append (ih (by omega)) (hperm i _ l hM' hl)).trans ?_
      apply toList_append_perm
      · intro k h1 h2
        simp only [belowPart, GMap.lookup_filter] at h1
        rw [lookup_shardPart] at h2
        cases hM : M' !! k <;> simp_all [Option.filter]
      · intro k v
        simp only [belowPart, GMap.lookup_filter, lookup_shardPart]
        cases hM : M' !! k <;> by_cases h1 : shardOf n k < i <;> by_cases h2 : shardOf n k = i <;>
          simp_all [Option.filter] <;> omega
  have := hstep n (Nat.le_refl n)
  rw [List.take_of_length_le (by omega)] at this
  have hb : belowPart n n M = M := by
    apply GMap.map_eq; intro k
    simp only [belowPart, GMap.lookup_filter]
    cases M !! k <;> simp [Option.filter, shardOf_lt n k hn]
  rw [hb] at this
  exact this

/-- (3') Deleting the keys of a list of `M`'s entries (all of them) empties `M`. -/
theorem foldl_delete_empty (ks : List GoString) (M : GMap GoString GoInterface)
    (h : ∀ k, (M !! k).isSome → k ∈ ks) :
    ks.foldl (fun M k => GMap.delete k M) M = ∅ := by
  induction ks generalizing M with
  | nil =>
    apply (GMap.mapEmpty _).2
    intro k
    cases hk : M !! k
    · simp only [List.foldl_nil]; exact hk
    · exact absurd (h k (by simp [hk])) (by simp)
  | cons k ks ih =>
    simp only [List.foldl_cons]
    apply ih
    intro k' hk'
    by_cases e : k = k'
    · subst e; simp at hk'
    · rw [GMap.lookup_delete_ne _ e] at hk'
      rcases List.mem_cons.mp (h k' hk') with h' | h'
      · exact absurd h'.symm e
      · exact h'

/-- (3') Removing each key a pass visited, when no writer ran during the pass, empties the
map. -/
theorem iterTrace_remove_all (n : Nat) (obs : List (GMap GoString GoInterface))
    (vis : List (GoString × GoInterface)) (M : GMap GoString GoInterface)
    (h : iterTrace n obs vis) (hobs : ∀ M' ∈ obs, M' = M) :
    (vis.map Prod.fst).foldl (fun M k => GMap.delete k M) M = ∅ := by
  have hp := iterTrace_perm n obs vis M h hobs
  apply foldl_delete_empty
  intro k hk
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hk
  have : (k, v) ∈ vis := hp.mem_iff.mpr ((GMap.mem_toList M k v).mpr hv)
  exact List.mem_map.mpr ⟨(k, v), this, rfl⟩

end Perennial.github_com.orcaman.concurrent_map
