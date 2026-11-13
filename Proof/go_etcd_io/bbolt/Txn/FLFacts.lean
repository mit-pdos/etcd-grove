/-
The freelist's steps at a writer's begin and rollback, as the writer side sees them (U5 of
`notes/bbolt-proof-plan.md`): `ReleasePendingPages` moves pending ids to the free ids, every
pending entry after it a part of one before (`Model/Store`'s private `relOK`, read through
`import all`); `Rollback` deletes the writer's pending entry, the free ids unchanged.
-/
module

public import Proof.go_etcd_io.bbolt.Model.Store
import all Proof.go_etcd_io.bbolt.Model.Store

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt


section flfacts
variable [GooseExts]
set_option linter.unusedSectionVars false

/-- Membership in the pending slots, by entry. -/
theorem pendSlots_mem_iff (fl : FLPg) (s : Nat) :
    s ∈ pendSlots fl ↔ ∃ t pd x, fl.pending !! t = some pd ∧ x ∈ pd.ids ∧ x.toNat = s :=
  mem_pendSlots fl s

/-- Membership in the pending ids, by entry. -/
theorem pendingIds_mem_iff (fl : FLPg) (x : w64) :
    x ∈ fl.pendingIds ↔ ∃ t pd, fl.pending !! t = some pd ∧ x ∈ pd.ids := by
  simp only [FLPg.pendingIds, List.mem_flatMap]
  constructor
  · rintro ⟨⟨t, pd⟩, hkv, hx⟩
    exact ⟨t, pd, (GMap.mem_toList _ _ _).1 hkv, hx⟩
  · rintro ⟨t, pd, hp, hx⟩
    exact ⟨(t, pd), (GMap.mem_toList _ _ _).2 hp, hx⟩

/-- **`ReleasePendingPages`' bookkeeping**: a free id after it was free or pending before; a
pending entry after it is part of the same transaction's entry before; the free and pending ids
together unchanged. -/
theorem releasePending_sub (fl : FLPg) (ro : List w64)
    (hro : ∀ t ∈ ro, 1 ≤ t.toNat ∧ t.toNat + 1 < 2 ^ 64)
    (hwf : ∀ t p, fl.pending !! t = some p → p.ids.length = p.alloctx.length) :
    (∀ x ∈ (fl.releasePending ro).free, x ∈ fl.free ∨
        ∃ t pd, fl.pending !! t = some pd ∧ x ∈ pd.ids) ∧
    (∀ t pd' x, (fl.releasePending ro).pending !! t = some pd' → x ∈ pd'.ids →
        ∃ pd, fl.pending !! t = some pd ∧ x ∈ pd.ids) ∧
    (∀ x, x ∈ (fl.releasePending ro).allIds ↔ x ∈ fl.allIds) := by
  obtain ⟨-, r2, r3, r4, -, -⟩ := relOK_releasePending fl ro hro hwf
  refine ⟨fun x hx => ?_, fun t pd' x hp hx => ?_, fun x => r4.mem_iff⟩
  · rcases r2 x hx with h | ⟨t, pd, i, hp, hi, -⟩
    · exact .inl h
    · exact .inr ⟨t, pd, hp, List.mem_of_getElem? hi⟩
  · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hx
    obtain ⟨pd, j, hp0, hj, -⟩ := r3 t pd' i x hp hi
    exact ⟨pd, hp0, List.mem_of_getElem? hj⟩

/-- `Rollback` keeps the free ids. -/
theorem rollback_free (fl : FLPg) (T : w64) : (fl.rollback T).free = fl.free := by
  unfold FLPg.rollback; split
  · rfl
  · rfl

/-- `Rollback(T)` keeps every other transaction's pending entry. -/
theorem rollback_pending_ne (fl : FLPg) (T t : w64) (h : t ≠ T) :
    (fl.rollback T).pending !! t = fl.pending !! t := by
  unfold FLPg.rollback; split
  · rfl
  · simp only [FLPg.rollbackEntry]
    exact GMap.lookup_delete_ne _ (fun e => h e.symm)

/-- A pending entry after `Rollback` was one before. -/
theorem rollback_pending_sub (fl : FLPg) (T t : w64) (pd : Pending)
    (h : (fl.rollback T).pending !! t = some pd) : fl.pending !! t = some pd := by
  unfold FLPg.rollback at h; split at h
  · exact h
  · exact (rollback_pending fl T t pd h).2

/-- `release` keeps `allocs`. -/
theorem release_allocs (fl : FLPg) (t : w64) : (fl.release t).allocs = fl.allocs := rfl

/-- `releaseRange` keeps `allocs`. -/
theorem releaseRange_allocs (fl : FLPg) (b e : w64) : (fl.releaseRange b e).allocs = fl.allocs := by
  unfold FLPg.releaseRange; split
  · rfl
  · rfl

/-- **`ReleasePendingPages` keeps `allocs`.** -/
theorem releasePending_allocs (fl : FLPg) (ro : List w64) :
    (fl.releasePending ro).allocs = fl.allocs := by
  have key : ∀ (l : List w64) (acc : FLPg × w64),
      (l.foldl (fun (acc : FLPg × w64) t => (acc.1.releaseRange acc.2 (t - 1), t + 1)) acc).1.allocs =
        acc.1.allocs := by
    intro l
    induction l with
    | nil => intro acc; rfl
    | cons a l ih => intro acc; rw [List.foldl_cons, ih, releaseRange_allocs]
  unfold FLPg.releasePending
  dsimp only
  rw [releaseRange_allocs, key]
  split
  · rfl
  · rfl

omit [GooseExts] in
theorem foldl_insert_lookup (k v : w64) : ∀ (l : List (w64 × w64)) (m : GMap w64 w64),
    (l.foldl (fun m x => m.insert x.1 x.2) m) !! k = some v →
      m !! k = some v ∨ ∃ x ∈ l, x.1 = k ∧ x.2 = v := by
  intro l
  induction l with
  | nil => intro m h; exact .inl h
  | cons x l ih =>
    intro m h
    rw [List.foldl_cons] at h
    rcases ih _ h with h' | ⟨y, hy, e⟩
    · by_cases hk : x.1 = k
      · subst hk
        rw [GMap.lookup_insert] at h'
        exact .inr ⟨x, List.mem_cons_self, rfl, (Option.some.inj h').symm ▸ rfl⟩
      · rw [GMap.lookup_insert_ne _ _ hk] at h'
        exact .inl h'
    · exact .inr ⟨y, List.mem_cons_of_mem _ hy, e⟩

/-- **`allocs` after `Rollback(T)`**: an entry was there before, or comes back from `T`'s pending
entry (an id of it, with its recorded allocating transaction). -/
theorem rollback_allocs_lookup (fl : FLPg) (T k v : w64) (h : (fl.rollback T).allocs !! k = some v) :
    fl.allocs !! k = some v ∨ ∃ pd, fl.pending !! T = some pd ∧ k ∈ pd.ids ∧ v ∈ pd.alloctx := by
  unfold FLPg.rollback at h
  split at h
  · exact .inl h
  rename_i hne
  obtain ⟨pd, hpd⟩ := Option.ne_none_iff_exists'.1 hne
  simp only [FLPg.rollbackEntry, GMap.lookup_filter, Option.filter_eq_some_iff, hpd,
    Option.getD_some] at h
  rcases foldl_insert_lookup k v _ _ h.1 with h' | ⟨x, hx, e1, e2⟩
  · exact .inl h'
  · right
    have hz := (List.mem_filter.1 hx).1
    refine ⟨pd, hpd, e1 ▸ (List.of_mem_zip hz).1, e2 ▸ (List.of_mem_zip hz).2⟩

/-- The pending slots after `Rollback` were pending slots before. -/
theorem pendSlots_rollback_sub (fl : FLPg) (T : w64) (s : Nat)
    (h : s ∈ pendSlots (fl.rollback T)) : s ∈ pendSlots fl := by
  obtain ⟨t, pd, x, hp, hx, rfl⟩ := (mem_pendSlots _ _).1 h
  exact (mem_pendSlots _ _).2 ⟨t, pd, x, rollback_pending_sub fl T t pd hp, hx, rfl⟩

/-- `W64` of an id's value is the id. -/
theorem W64_toNat_self (x : w64) : W64 (x.toNat : Int) = x :=
  BitVec.eq_of_toNat_eq (toNat_W64_of_lt x.toNat x.isLt)

/-- **`flCurOK` carries over to a freelist `fl'`** whose ids are among `fl`'s, whose free ids
were free or committed-pending, whose committed-pending ids were, and which keeps each of `fl`'s
committed-pending ids committed-pending or frees it as an id that could be free. -/
theorem flCurOK_mono (fl fl' : FLPg) (C : CommitSt) (pg : List w8)
    (hall : ∀ x, x ∈ fl'.allIds → x ∈ fl.allIds)
    (hfree : ∀ x ∈ fl'.free, x ∈ fl.free ∨ committedPending fl C x)
    (hcp : ∀ x, committedPending fl' C x → committedPending fl C x)
    (hback : ∀ x, committedPending fl C x → committedPending fl' C x ∨
      (x.toNat < C.hwm ∧ x.toNat < 2 ^ 62 ∧ ¬ coversSlot C.pages x.toNat))
    (hal : ∀ f, C.flpg = some f → ∀ a, fl'.allocs !! W64 (f : Int) = some a →
      fl.allocs !! W64 (f : Int) = some a ∨ W64 (f : Int) ∈ fl.pendingIds)
    (h : flCurOK fl C pg) : flCurOK fl' C pg := by
  intro f hf
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14⟩ := h f hf
  refine ⟨a1, a2, a3, a4, a5, a6, a7, a8,
    fun s h1 h2 => ⟨(a9 s h1 h2).1, fun hm => (a9 s h1 h2).2 (hall _ hm)⟩, fun x hx => ?_,
    fun x hx => a11 x (hcp x hx), fun x hx => ?_, fun a ha => ?_, a14⟩
  rotate_right
  · rcases hal f hf a ha with h | h
    · exact a13 a h
    · exact absurd (List.mem_append_right _ h) (a9 f (Nat.le_refl _) (by omega)).2
  · rcases hfree x hx with h | h
    · exact a10 x h
    · exact a11 x h
  · rcases a12 x hx with h | h
    · exact hback x h
    · exact Or.inr h


end flfacts

end bbolt
end EtcdGrove
end Perennial
