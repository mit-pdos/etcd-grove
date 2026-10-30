/-
Pure lemmas of `releaseRange` and `ReleasePendingPages`: lists gathered over a map's keys, the
entries `releaseRange` changes, the swap-removal of its inner loop, and `FLState.equiv`.
-/
module

public import Proof.go_etcd_io.bbolt.internal.freelist.Iface

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

/-- Elements contributing nothing can be dropped from a `flatMap`. -/
theorem flatMap_filter_nil {α β : Type} (l : List α) (p : α → Bool) (g : α → List β)
    (h : ∀ a, p a = false → g a = []) : l.flatMap g = (l.filter p).flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases hp : p a = true
    · simp [List.filter_cons, hp, ih]
    · simp [List.filter_cons, hp, ih, h a (by simpa using hp)]

theorem flatMap_append_perm {α β : Type} (l : List α) (f g : α → List β) :
    (l.flatMap (fun a => f a ++ g a)).Perm (l.flatMap f ++ l.flatMap g) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons, List.append_assoc]
    refine List.Perm.append_left _ ((List.Perm.append_left _ ih).trans ?_)
    rw [← List.append_assoc, ← List.append_assoc]
    exact List.Perm.append_right _ List.perm_append_comm

theorem flatMap_perm_mem {α β : Type} (l : List α) {f g : α → List β}
    (h : ∀ a ∈ l, (f a).Perm (g a)) : (l.flatMap f).Perm (l.flatMap g) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons]
    exact List.Perm.append (h a List.mem_cons_self) (ih fun x hx => h x (List.mem_cons_of_mem _ hx))

/-- A list gathered over (a superset of) a map's keys, in their order: the same gathered over
the map's bindings. -/
theorem map_flatMap_keys {V : Type} (m : GMap w64 V) (d : V) (f : w64 → V → List w64)
    (keys : List w64) (hk : ∀ k, (m !! k).isSome → k ∈ keys) (hnd : keys.Nodup) :
    (keys.flatMap (fun t => ((m !! t).map (f t)).getD [])).Perm
      (m.toList.flatMap (fun kv => f kv.1 kv.2)) := by
  have hkf : (keys.filter (fun t => (m !! t).isSome)).Nodup := hnd.sublist List.filter_sublist
  have hl : ((keys.filter (fun t => (m !! t).isSome)).map (fun t => (t, (m !! t).getD d))).Perm
      m.toList := by
    refine toList_perm_of (by simpa [List.map_map, Function.comp_def] using hkf) (fun k v => ?_)
    simp only [List.mem_map, List.mem_filter, Prod.mk.injEq]
    constructor
    · rintro ⟨t, ⟨_, ht⟩, rfl, rfl⟩
      cases h : m !! t with
      | none => simp [h] at ht
      | some w => simp
    · intro h
      exact ⟨k, ⟨hk k (by simp [h]), by simp [h]⟩, rfl, by simp [h]⟩
  rw [flatMap_filter_nil keys (fun t => (m !! t).isSome) _
    (fun a ha => by cases h : m !! a <;> simp_all)]
  refine List.Perm.trans ?_ (hl.flatMap_right _)
  rw [List.flatMap_map]
  apply List.Perm.of_eq
  apply flatMap_congr_mem
  intro t ht
  simp only [List.mem_filter] at ht
  cases h : m !! t with
  | none => simp [h] at ht
  | some w => simp

theorem flatIds_keys' (m : GMap w64 Pending) (keys : List w64)
    (hk : ∀ k, (m !! k).isSome → k ∈ keys) (hnd : keys.Nodup) :
    (keys.flatMap (fun t => ((m !! t).map (fun pd => pd.ids)).getD [])).Perm (flatIds m) :=
  map_flatMap_keys m ⟨[], [], 0⟩ (fun _ pd => pd.ids) keys hk hnd

theorem lookup_union {V : Type} (m₁ m₂ : GMap w64 V) (k : w64) :
    (m₁ ∪ m₂) !! k = (m₁ !! k).or (m₂ !! k) := rfl

theorem lookup_fmap {V V' : Type} (f : V → V') (m : GMap w64 V) (k : w64) :
    (GMap.fmap f m) !! k = (m !! k).map f := rfl

/-- `releaseRange(b, e)`'s entry of `k`. -/
def rrEntry (b e k : w64) (pd : Pending) : Option Pending :=
  if rrTouched b e k pd then
    (if (rrKeep b e pd).ids.isEmpty then none else some (rrKeep b e pd))
  else some pd

/-- `releaseRange(b, e)`'s ids of the entry of `k` (none if it is not looked at). -/
def rrRelOpt (b e k : w64) (pd : Pending) : List w64 := if rrTouched b e k pd then rrRel b e pd else []

theorem releaseRange_lookup {σ : FLState} {b e : w64} (hbe : ¬ uint.Z e < uint.Z b) (k : w64) :
    (σ.releaseRange b e).pending !! k = (σ.pending !! k).bind (rrEntry b e k) := by
  unfold FLState.releaseRange
  rw [if_neg hbe]
  simp only [lookup_union, lookup_filter, lookup_fmap]
  cases σ.pending !! k with
  | none => rfl
  | some pd =>
    unfold rrEntry
    by_cases ht : rrTouched b e k pd = true
    · by_cases hk : (rrKeep b e pd).ids.isEmpty = true
      · simp [Option.filter, ht, hk]; exact List.isEmpty_iff.1 hk
      · simp [Option.filter, ht, hk]; exact fun h => hk (List.isEmpty_iff.2 h)
    · simp [Option.filter, ht]

theorem pairs_fst {pd : Pending} (h : pd.ids.length = pd.alloctx.length) :
    pd.pairs.map Prod.fst = pd.ids := List.map_fst_zip (by omega)

theorem pairs_snd {pd : Pending} (h : pd.ids.length = pd.alloctx.length) :
    pd.pairs.map Prod.snd = pd.alloctx := List.map_snd_zip (by omega)

/-- An entry's ids: those `releaseRange` frees and those it keeps. -/
theorem ids_perm_rr {pd : Pending} (b e : w64) (h : pd.ids.length = pd.alloctx.length) :
    pd.ids.Perm (rrRel b e pd ++ (rrKeep b e pd).ids) := by
  rw [← pairs_fst h]
  unfold rrRel rrKeep
  simp only
  rw [← List.map_append]
  exact ((List.filter_append_perm (fun x => inTxRange b e x.2) pd.pairs).map _).symm

theorem rrKeep_len (b e : w64) (pd : Pending) :
    (rrKeep b e pd).ids.length = (rrKeep b e pd).alloctx.length := by simp [rrKeep]

/-- `l[j] = l[last]; l = l[:last]` and `l[j]`: `l`, up to order. -/
theorem swap_take_perm {α : Type} (l : List α) (j : Nat) (hj : j < l.length) :
    ((l.set j l[l.length - 1]).take (l.length - 1) ++ [l[j]]).Perm l := by
  obtain ⟨A, x, B, rfl, hA⟩ : ∃ A x B, l = A ++ x :: B ∧ A.length = j :=
    ⟨l.take j, l[j], l.drop (j + 1), by simp, by simp; omega⟩
  subst hA
  rcases List.eq_nil_or_concat B with rfl | ⟨B', y, rfl⟩
  · simp [List.set_append_right, List.take_left']
  · simp only [List.concat_eq_append]
    have hlast : (A ++ x :: (B' ++ [y]))[(A ++ x :: (B' ++ [y])).length - 1]'(by simp) = y := by
      simp [List.getElem_append_right]
    have hj : (A ++ x :: (B' ++ [y]))[A.length]'(by simp) = x := by simp
    rw [hlast, hj, List.set_append_right _ _ (Nat.le_refl _), Nat.sub_self, List.set_cons_zero]
    rw [show (A ++ x :: (B' ++ [y])).length - 1 = (A ++ y :: B').length by simp,
      show A ++ y :: (B' ++ [y]) = (A ++ y :: B') ++ [y] by simp, List.take_left]
    rw [List.append_assoc]
    refine List.Perm.append_left A ?_
    exact (List.perm_append_singleton x (y :: B')).trans
      (List.Perm.cons x (List.perm_append_singleton y B').symm)

/-- Two lists, one of elements failing `p` and one of elements satisfying it, together a
permutation of `L`: each is `L`'s part, up to order. -/
theorem part_perm {α : Type} {p : α → Bool} {l₁ l₂ L : List α} (h₁ : ∀ x ∈ l₁, p x = false)
    (h₂ : ∀ x ∈ l₂, p x = true) (h : (l₁ ++ l₂).Perm L) :
    l₁.Perm (L.filter (fun x => !p x)) ∧ l₂.Perm (L.filter p) := by
  have a := h.filter (fun x => !p x)
  have b := h.filter p
  rw [List.filter_append, List.filter_eq_self.2 (by simpa using h₁),
    List.filter_eq_nil_iff.2 (by simpa using h₂), List.append_nil] at a
  rw [List.filter_append, List.filter_eq_nil_iff.2 (by simpa using h₁),
    List.filter_eq_self.2 (by simpa using h₂), List.nil_append] at b
  exact ⟨a, b⟩

/-- The entry `o` of `k` after `releaseRange(b, e)` looked at it: an entry it does not look at
is unchanged, one it looks at keeps its pairs allocated outside `[b, e]` (up to order), and is
gone if none is left. -/
def rrGood (σ : FLState) (b e k : w64) (o : Option Pending) : Prop :=
  match σ.pending !! k with
  | none => o = none
  | some pd =>
    if rrTouched b e k pd then
      (match o with
       | none => (rrKeep b e pd).ids = []
       | some q => q.equiv (rrKeep b e pd) ∧ q.ids ≠ [] ∧ q.ids.length = q.alloctx.length)
    else o = some pd

/-- The ids `releaseRange(b, e)` frees, gathered over the keys. -/
def rrRelKeys (σ : FLState) (b e : w64) (keys : List w64) : List w64 :=
  keys.flatMap (fun t => ((σ.pending !! t).map (rrRelOpt b e t)).getD [])

theorem rrKeep_pairs (b e : w64) (pd : Pending) :
    (rrKeep b e pd).pairs = pd.pairs.filter (fun x => !inTxRange b e x.2) := by
  simp [rrKeep, Pending.pairs, List.zip_map']

theorem pairs_of_list (Q : List (w64 × w64)) (lrb : w64) :
    (⟨Q.map Prod.fst, Q.map Prod.snd, lrb⟩ : Pending).pairs = Q := by
  simp [Pending.pairs, List.zip_map']

theorem equiv_ids {q r : Pending} (h : q.equiv r) (hq : q.ids.length = q.alloctx.length)
    (hr : r.ids.length = r.alloctx.length) : q.ids.Perm r.ids := by
  rw [← pairs_fst hq, ← pairs_fst hr]; exact h.1.map _

/-- After `releaseRange(b, e)`: the entries `G` (`rrGood`), the freed ids `L` (gathered in the
order of the keys) merged into the free ids `free'`. -/
theorem releaseRange_ok {σ : FLState} {b e : w64} {keys L free' : List w64} {G : GMap w64 Pending}
    (hwf : σ.WF) (hbe : ¬ uint.Z e < uint.Z b)
    (hk : ∀ k, k ∈ keys ↔ (σ.pending !! k).isSome) (hnd : keys.Nodup)
    (hG : ∀ k, rrGood σ b e k (G !! k)) (hL : L.Perm (rrRelKeys σ b e keys)) :
    σ.allIds.Perm ((σ.free ++ L) ++ flatIds G) ∧
    ((σ.free ++ L).Nodup ∧ (∀ y ∈ L, 2 ≤ uint.Z y) ∧ σ.free.length + L.length < 2 ^ 63) ∧
    (free'.Perm (σ.free ++ L) → PgidsIncr free' →
      ({ σ with free := free', pending := G } : FLState).WF ∧
      (∀ x, ({ σ with free := free', pending := G } : FLState).cached x ↔ σ.cached x) ∧
      ({ σ with free := free', pending := G } : FLState).equiv (σ.releaseRange b e)) := by
  have hGdom : ∀ k, (G !! k).isSome → k ∈ keys := by
    intro k hgk; apply (hk k).2
    have := hG k; unfold rrGood at this
    cases h : σ.pending !! k with
    | none => rw [h] at this; simp [this] at hgk
    | some _ => simp
  have hper : ∀ t ∈ keys, (((σ.pending !! t).map (fun pd => pd.ids)).getD []).Perm
      (((σ.pending !! t).map (rrRelOpt b e t)).getD [] ++
        ((G !! t).map (fun pd => pd.ids)).getD []) := by
    intro t _
    have := hG t; unfold rrGood at this
    cases h : σ.pending !! t with
    | none => rw [h] at this; simp [this]
    | some pd =>
      rw [h] at this; simp only at this
      have hl := hwf.2.2.2.2 t pd h
      simp only [Option.map_some, Option.getD_some]
      unfold rrRelOpt
      by_cases ht : rrTouched b e t pd = true
      · rw [if_pos ht] at this ⊢
        refine (ids_perm_rr b e hl).trans (List.Perm.append_left _ ?_)
        cases hgt : G !! t with
        | none => rw [hgt] at this; simp [this]
        | some q =>
          rw [hgt] at this
          exact (equiv_ids this.1 this.2.2 (rrKeep_len b e pd)).symm
      · rw [if_neg ht] at this ⊢
        rw [this]; simp
  have hpend : σ.pendingIds.Perm (L ++ flatIds G) := by
    rw [pendingIds_eq]
    refine (flatIds_keys' σ.pending keys (fun k h => (hk k).2 h) hnd).symm.trans ?_
    refine (flatMap_perm_mem keys hper).trans ((flatMap_append_perm _ _ _).trans ?_)
    exact List.Perm.append hL.symm (flatIds_keys' G keys hGdom hnd)
  have hall : σ.allIds.Perm ((σ.free ++ L) ++ flatIds G) := by
    unfold FLState.allIds; rw [List.append_assoc]; exact List.Perm.append_left _ hpend
  obtain ⟨h1, h2, h3, h4, h5⟩ := hwf
  refine ⟨hall, ⟨(List.nodup_append.1 (hall.nodup_iff.1 h1)).1, fun y hy => ?_, ?_⟩, ?_⟩
  · exact h2 y (hall.mem_iff.2 (List.mem_append_left _ (List.mem_append_right _ hy)))
  · have := hall.length_eq; simp only [List.length_append] at this; omega
  intro hf hinc
  have hperm : ({ σ with free := free', pending := G } : FLState).allIds.Perm σ.allIds :=
    (List.Perm.append_right (flatIds G) hf).trans hall.symm
  obtain ⟨hw, hc⟩ := move_ok ⟨h1, h2, h3, h4, h5⟩ hperm hinc (fun t q hq => by
    have := hG t; unfold rrGood at this
    simp only at hq
    cases h : σ.pending !! t with
    | none => rw [h, hq] at this; cases this
    | some pd =>
      rw [h] at this; simp only at this
      split at this
      · rw [hq] at this; exact this.2.2
      · rw [hq] at this; have e := Option.some.inj this; subst e; exact h5 t _ h)
  refine ⟨hw, hc, ?_, ?_, ?_, ?_, ?_⟩
  · unfold FLState.releaseRange; rw [if_neg hbe]
    refine hf.trans (List.Perm.append_left _ (hL.trans ?_))
    have := map_flatMap_keys (σ.pending.filter (rrTouched b e)) ⟨[], [], 0⟩
      (fun _ pd => rrRel b e pd) keys
      (fun k h => (hk k).2 (by rw [lookup_filter] at h; cases h' : σ.pending !! k <;> simp_all))
      hnd
    refine List.Perm.trans (List.Perm.of_eq (flatMap_congr_mem fun t _ => ?_)) this
    rw [lookup_filter]; unfold rrRelOpt
    cases σ.pending !! t with
    | none => rfl
    | some pd => by_cases ht : rrTouched b e t pd = true <;> simp [Option.filter, ht]
  · unfold FLState.releaseRange; rw [if_neg hbe]
  · unfold FLState.releaseRange; rw [if_neg hbe]
  · intro t
    rw [releaseRange_lookup hbe]
    have := hG t; unfold rrGood at this
    simp only
    cases h : σ.pending !! t with
    | none => rw [h] at this; simp [this]
    | some pd =>
      rw [h] at this; simp only at this
      simp only [Option.bind_some]
      unfold rrEntry
      split at this
      · rename_i ht; rw [if_pos ht]
        cases hgt : G !! t with
        | none => rw [hgt] at this; simp [this]
        | some q =>
          rw [hgt] at this
          have hlen := (equiv_ids this.1 this.2.2 (rrKeep_len b e pd)).length_eq
          have hne : (rrKeep b e pd).ids.isEmpty = false := by
            cases hk' : (rrKeep b e pd).ids with
            | nil => rw [hk'] at hlen; exact absurd (List.eq_nil_of_length_eq_zero hlen) this.2.1
            | cons _ _ => rfl
          simp [hne]
      · rename_i ht; rw [if_neg ht, this]
  · intro t p q hp hq
    rw [releaseRange_lookup hbe] at hq
    have := hG t; unfold rrGood at this
    simp only at hp
    cases h : σ.pending !! t with
    | none => rw [h] at hq; cases hq
    | some pd =>
      rw [h] at this hq; simp only at this
      simp only [Option.bind_some] at hq
      unfold rrEntry at hq
      split at this
      · rename_i ht; rw [if_pos ht] at hq
        rw [hp] at this
        split at hq
        · cases hq
        · cases hq; exact this.1
      · rename_i ht; rw [if_neg ht] at hq
        rw [hp] at this; cases this; cases hq; exact Pending.equiv_refl _

/-! `FLState.equiv` and the release functions. -/

theorem Pending.equiv_symm {p q : Pending} (h : p.equiv q) : q.equiv p := ⟨h.1.symm, h.2.symm⟩

theorem Pending.equiv_trans {p q r : Pending} (h₁ : p.equiv q) (h₂ : q.equiv r) : p.equiv r :=
  ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩

theorem FLState.equiv_refl (σ : FLState) : σ.equiv σ :=
  ⟨List.Perm.refl _, List.Perm.refl _, rfl, fun _ => Iff.rfl, fun t p q hp hq => by
    rw [hp] at hq; cases hq; exact Pending.equiv_refl p⟩

theorem FLState.equiv_symm {σ τ : FLState} (h : σ.equiv τ) : τ.equiv σ :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, fun t => (h.2.2.2.1 t).symm,
    fun t p q hp hq => Pending.equiv_symm (h.2.2.2.2 t q p hq hp)⟩

theorem FLState.equiv_trans {σ τ μ : FLState} (h₁ : σ.equiv τ) (h₂ : τ.equiv μ) : σ.equiv μ := by
  refine ⟨h₁.1.trans h₂.1, h₁.2.1.trans h₂.2.1, h₁.2.2.1.trans h₂.2.2.1,
    fun t => (h₁.2.2.2.1 t).trans (h₂.2.2.2.1 t), fun t p r hp hr => ?_⟩
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.1 ((h₁.2.2.2.1 t).1 (by simp [hp]))
  exact Pending.equiv_trans (h₁.2.2.2.2 t p q hp hq) (h₂.2.2.2.2 t q r hq hr)

/-- Every pending entry has as many allocating transactions as ids. -/
def PendLen (σ : FLState) : Prop :=
  ∀ t p, σ.pending !! t = some p → p.ids.length = p.alloctx.length

theorem release_pendLen {σ : FLState} (h : PendLen σ) (txid : w64) : PendLen (σ.release txid) := by
  intro t p hp
  unfold FLState.release at hp; simp only [lookup_filter] at hp
  apply h t p
  cases h' : σ.pending !! t <;> simp_all [Option.filter]

theorem releaseRange_pendLen {σ : FLState} (h : PendLen σ) (b e : w64) :
    PendLen (σ.releaseRange b e) := by
  by_cases hbe : uint.Z e < uint.Z b
  · unfold FLState.releaseRange; rw [if_pos hbe]; exact h
  intro t p hp
  rw [releaseRange_lookup hbe] at hp
  cases h' : σ.pending !! t with
  | none => rw [h'] at hp; cases hp
  | some pd =>
    rw [h'] at hp
    simp only [Option.bind_some] at hp
    unfold rrEntry at hp
    by_cases ht : rrTouched b e t pd = true
    · rw [if_pos ht] at hp
      by_cases he : (rrKeep b e pd).ids.isEmpty = true
      · rw [if_pos he] at hp; cases hp
      · rw [if_neg he] at hp; rw [← Option.some.inj hp]; exact rrKeep_len b e pd
    · rw [if_neg ht] at hp; rw [← Option.some.inj hp]; exact h t pd h'

/-- The keys of a state's pending map. -/
def pendKeys (σ : FLState) : List w64 := σ.pending.toList.map Prod.fst

theorem pendKeys_iff (σ : FLState) (k : w64) : k ∈ pendKeys σ ↔ (σ.pending !! k).isSome := by
  unfold pendKeys
  simp only [List.mem_map, Prod.exists, exists_and_right, exists_eq_right, GMap.mem_toList]
  cases σ.pending !! k <;> simp

theorem pendKeys_nodup (σ : FLState) : (pendKeys σ).Nodup := GMap.toList_keys_nodup _

/-- Equivalent entries, filtered alike, gather equivalent ids. -/
theorem flatMap_equiv {σ τ : FLState} (h : σ.equiv τ) (hσ : PendLen σ) (hτ : PendLen τ)
    (f : w64 → Pending → List w64)
    (hf : ∀ t p q, σ.pending !! t = some p → τ.pending !! t = some q → (f t p).Perm (f t q)) :
    ((pendKeys σ).flatMap (fun t => ((σ.pending !! t).map (f t)).getD [])).Perm
      ((pendKeys σ).flatMap (fun t => ((τ.pending !! t).map (f t)).getD [])) := by
  apply flatMap_perm_mem
  intro t _
  cases hp : σ.pending !! t with
  | none =>
    have : τ.pending !! t = none := by
      cases hq : τ.pending !! t
      · rfl
      · have := (h.2.2.2.1 t).2 (by simp [hq]); simp [hp] at this
    simp [this]
  | some p =>
    obtain ⟨q, hq⟩ := Option.isSome_iff_exists.1 ((h.2.2.2.1 t).1 (by simp [hp]))
    simp only [hq, Option.map_some, Option.getD_some]
    exact hf t p q hp hq

theorem release_congr {σ τ : FLState} (h : σ.equiv τ) (hσ : PendLen σ) (hτ : PendLen τ)
    (txid : w64) : (σ.release txid).equiv (τ.release txid) := by
  have hkτ : ∀ k, (τ.pending !! k).isSome → k ∈ pendKeys σ :=
    fun k hk => (pendKeys_iff σ k).2 ((h.2.2.2.1 k).2 hk)
  refine ⟨?_, h.2.1, h.2.2.1, fun t => ?_, fun t p q hp hq => ?_⟩
  · unfold FLState.release
    refine List.Perm.append h.1 ?_
    have a := map_flatMap_keys (σ.pending.filter (fun t _ => decide (uint.Z t ≤ uint.Z txid)))
      ⟨[], [], 0⟩ (fun _ pd => pd.ids) (pendKeys σ)
      (fun k hk => (pendKeys_iff σ k).2 (by rw [lookup_filter] at hk; cases h' : σ.pending !! k <;> simp_all))
      (pendKeys_nodup σ)
    have b := map_flatMap_keys (τ.pending.filter (fun t _ => decide (uint.Z t ≤ uint.Z txid)))
      ⟨[], [], 0⟩ (fun _ pd => pd.ids) (pendKeys σ)
      (fun k hk => hkτ k (by rw [lookup_filter] at hk; cases h' : τ.pending !! k <;> simp_all))
      (pendKeys_nodup σ)
    refine a.symm.trans (List.Perm.trans ?_ b)
    apply flatMap_perm_mem
    intro t _
    simp only [lookup_filter]
    cases hp : σ.pending !! t with
    | none =>
      have : τ.pending !! t = none := by
        cases hq : τ.pending !! t
        · rfl
        · have := (h.2.2.2.1 t).2 (by simp [hq]); simp [hp] at this
      simp [this, Option.filter]
    | some p =>
      obtain ⟨q, hq⟩ := Option.isSome_iff_exists.1 ((h.2.2.2.1 t).1 (by simp [hp]))
      rw [hq]
      by_cases ht : uint.Z t ≤ uint.Z txid
      · simp [Option.filter, ht]; exact equiv_ids (h.2.2.2.2 t p q hp hq) (hσ t p hp) (hτ t q hq)
      · simp [Option.filter, ht]
  · unfold FLState.release; simp only [lookup_filter]
    cases hp : σ.pending !! t with
    | none =>
      have : τ.pending !! t = none := by
        cases hq : τ.pending !! t
        · rfl
        · have := (h.2.2.2.1 t).2 (by simp [hq]); simp [hp] at this
      simp [this, Option.filter]
    | some p =>
      obtain ⟨q, hq⟩ := Option.isSome_iff_exists.1 ((h.2.2.2.1 t).1 (by simp [hp]))
      rw [hq]; simp [Option.filter]
  · unfold FLState.release at hp hq; simp only [lookup_filter] at hp hq
    cases hp' : σ.pending !! t with
    | none => rw [hp'] at hp; cases hp
    | some p' =>
      cases hq' : τ.pending !! t with
      | none => rw [hq'] at hq; cases hq
      | some q' =>
        rw [hp'] at hp; rw [hq'] at hq
        have e1 : p = p' := by simp [Option.filter] at hp; exact hp.2.symm
        have e2 : q = q' := by simp [Option.filter] at hq; exact hq.2.symm
        subst e1; subst e2
        exact h.2.2.2.2 t p q hp' hq'

theorem rrEntry_congr {b e k : w64} {p q : Pending} (h : p.equiv q) :
    match rrEntry b e k p, rrEntry b e k q with
    | none, none => True
    | some p', some q' => p'.equiv q'
    | _, _ => False := by
  have ht : rrTouched b e k p = rrTouched b e k q := by unfold rrTouched; rw [h.2]
  have hk : (rrKeep b e p).pairs.Perm (rrKeep b e q).pairs := by
    rw [rrKeep_pairs, rrKeep_pairs]; exact h.1.filter _
  have hl : (rrKeep b e p).ids.length = (rrKeep b e q).ids.length := by
    simp only [rrKeep, List.length_map]; exact (h.1.filter _).length_eq
  unfold rrEntry
  rw [ht]
  by_cases htq : rrTouched b e k q = true
  · rw [if_pos htq, if_pos htq]
    have he : (rrKeep b e p).ids.isEmpty = (rrKeep b e q).ids.isEmpty := by
      cases h1 : (rrKeep b e p).ids <;> cases h2 : (rrKeep b e q).ids <;> simp_all
    rw [he]
    by_cases hq : (rrKeep b e q).ids.isEmpty = true
    · rw [if_pos hq, if_pos hq]; trivial
    · rw [if_neg hq, if_neg hq]; exact ⟨hk, rfl⟩
  · rw [if_neg htq, if_neg htq]; exact h

theorem releaseRange_congr {σ τ : FLState} (h : σ.equiv τ) (hσ : PendLen σ) (hτ : PendLen τ)
    (b e : w64) : (σ.releaseRange b e).equiv (τ.releaseRange b e) := by
  by_cases hbe : uint.Z e < uint.Z b
  · unfold FLState.releaseRange; rw [if_pos hbe, if_pos hbe]; exact h
  have hkτ : ∀ k, (τ.pending !! k).isSome → k ∈ pendKeys σ :=
    fun k hk => (pendKeys_iff σ k).2 ((h.2.2.2.1 k).2 hk)
  refine ⟨?_, ?_, ?_, fun t => ?_, fun t p q hp hq => ?_⟩
  · unfold FLState.releaseRange; rw [if_neg hbe, if_neg hbe]
    refine List.Perm.append h.1 ?_
    have a := map_flatMap_keys (σ.pending.filter (rrTouched b e)) ⟨[], [], 0⟩
      (fun _ pd => rrRel b e pd) (pendKeys σ)
      (fun k hk => (pendKeys_iff σ k).2 (by rw [lookup_filter] at hk; cases h' : σ.pending !! k <;> simp_all))
      (pendKeys_nodup σ)
    have b' := map_flatMap_keys (τ.pending.filter (rrTouched b e)) ⟨[], [], 0⟩
      (fun _ pd => rrRel b e pd) (pendKeys σ)
      (fun k hk => hkτ k (by rw [lookup_filter] at hk; cases h' : τ.pending !! k <;> simp_all))
      (pendKeys_nodup σ)
    refine a.symm.trans (List.Perm.trans ?_ b')
    apply flatMap_perm_mem
    intro t _
    simp only [lookup_filter]
    cases hp : σ.pending !! t with
    | none =>
      have : τ.pending !! t = none := by
        cases hq : τ.pending !! t
        · rfl
        · have := (h.2.2.2.1 t).2 (by simp [hq]); simp [hp] at this
      simp [this, Option.filter]
    | some p =>
      obtain ⟨q, hq⟩ := Option.isSome_iff_exists.1 ((h.2.2.2.1 t).1 (by simp [hp]))
      rw [hq]
      have ht : rrTouched b e t p = rrTouched b e t q := by
        unfold rrTouched; rw [(h.2.2.2.2 t p q hp hq).2]
      by_cases ht' : rrTouched b e t p = true
      · simp [Option.filter, ht', ← ht]
        unfold rrRel
        exact ((h.2.2.2.2 t p q hp hq).1.filter _).map _
      · simp [Option.filter, ht', ← ht]
  · unfold FLState.releaseRange; rw [if_neg hbe, if_neg hbe]; exact h.2.1
  · unfold FLState.releaseRange; rw [if_neg hbe, if_neg hbe]; exact h.2.2.1
  · rw [releaseRange_lookup hbe, releaseRange_lookup hbe]
    cases hp : σ.pending !! t with
    | none =>
      have : τ.pending !! t = none := by
        cases hq : τ.pending !! t
        · rfl
        · have := (h.2.2.2.1 t).2 (by simp [hq]); simp [hp] at this
      simp [this]
    | some p =>
      obtain ⟨q, hq⟩ := Option.isSome_iff_exists.1 ((h.2.2.2.1 t).1 (by simp [hp]))
      rw [hq]
      simp only [Option.bind_some]
      have := rrEntry_congr (b := b) (e := e) (k := t) (h.2.2.2.2 t p q hp hq)
      revert this
      cases rrEntry b e t p <;> cases rrEntry b e t q <;> simp
  · rw [releaseRange_lookup hbe] at hp hq
    cases hp' : σ.pending !! t with
    | none => rw [hp'] at hp; cases hp
    | some p' =>
      obtain ⟨q', hq'⟩ := Option.isSome_iff_exists.1 ((h.2.2.2.1 t).1 (by simp [hp']))
      rw [hp'] at hp; rw [hq'] at hq
      simp only [Option.bind_some] at hp hq
      have := rrEntry_congr (b := b) (e := e) (k := t) (h.2.2.2.2 t p' q' hp' hq')
      rw [hp, hq] at this
      exact this

/-- A sorted permutation of the read-only transactions is `sortedTxids` of them. -/
theorem sortedTxids_eq {l ys : List w64} (hs : PgidsSorted ys) (hp : ys.Perm l) :
    ys = sortedTxids l := by
  have hm : (sortedTxids l).Pairwise (fun a b => decide (uint.Z a ≤ uint.Z b) = true) :=
    List.pairwise_mergeSort (fun a b c h1 h2 => by simp at h1 h2 ⊢; omega)
      (fun a b => by
        rcases Int.le_total (uint.Z a) (uint.Z b) with h | h
        · simp only [decide_eq_true h, Bool.true_or]
        · simp only [decide_eq_true h, Bool.or_true]) l
  refine List.Perm.eq_of_pairwise (le := fun a b => decide (uint.Z a ≤ uint.Z b) = true)
    (fun a b _ _ h1 h2 => by simp at h1 h2; word) (hs.imp fun h => by simpa using h) hm
    (hp.trans (List.mergeSort_perm l _).symm)

end bbolt
end EtcdGrove
end Perennial
