/-
The freelist's state, as the writer side owns it (U0a of `notes/bbolt-proof-plan.md`; design
§3.2, §3.5): `FLPg`, the old `FLState` (`old/bbolt/.../internal/freelist/Model.lean`) without
`readonlyTXIDs`, which lives with `metalock` (`flRoOwn`, `Inv/Locks.lean`). Its operations are
`shared`'s methods (`internal/freelist/shared.go`) on the array implementation's sorted free
list.
-/
module

public import Proof.go_etcd_io.bbolt.Model.Page

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

/-- A transaction's pending pages (`txPending`): the ids, the transaction that allocated each
(`0` if unknown), and the start of the last `releaseRange` that looked at it. -/
structure Pending where
  ids : List w64
  alloctx : List w64
  lastReleaseBegin : w64
  deriving Inhabited, DecidableEq

instance Pending.countable : Pos.Countable Pending :=
  countableOfLeftInverse (fun p => (p.ids, p.alloctx, p.lastReleaseBegin))
    (fun p => ⟨p.1, p.2.1, p.2.2⟩) (fun _ => rfl)

/-- **The freelist minus its read-only transactions** (what `rwlock`'s side owns):
- `free`: the free ids, strictly increasing;
- `pending`: per transaction, the pages it freed (`Pending`);
- `allocs`: the transaction that allocated each page, as far as known. -/
structure FLPg where
  free : List w64
  pending : GMap w64 Pending
  allocs : GMap w64 w64
  deriving Inhabited

instance FLPg.countable : Pos.Countable FLPg :=
  countableOfLeftInverse (fun f => (f.free, f.pending, f.allocs)) (fun p => ⟨p.1, p.2.1, p.2.2⟩)
    (fun _ => rfl)

/-- The empty freelist (`newShared`; `Open`'s state before `loadFreelist`). -/
def FLPg.empty : FLPg := ⟨[], ∅, ∅⟩

/-- The ids sorted increasing (unsigned): `Pgids.Merge`'s result. -/
def sortPgids (l : List w64) : List w64 := l.mergeSort fun x y => decide (x.toNat ≤ y.toNat)

/-- The pending ids, all transactions together. -/
def FLPg.pendingIds (fl : FLPg) : List w64 := fl.pending.toList.flatMap fun kv => kv.2.ids

/-- The free and pending ids (`shared.cache`'s keys). -/
def FLPg.allIds (fl : FLPg) : List w64 := fl.free ++ fl.pendingIds

/-- Strictly increasing page ids. -/
def PgidsIncr (l : List w64) : Prop := l.Pairwise fun x y => x.toNat < y.toNat

/-- A well-formed freelist: free and pending ids distinct, at least 2, free increasing, fewer
than `2^63`, each pending entry with an allocating transaction per id. -/
def FLPg.WF (fl : FLPg) : Prop :=
  fl.allIds.Nodup ∧ (∀ id ∈ fl.allIds, 2 ≤ id.toNat) ∧ PgidsIncr fl.free ∧
  fl.allIds.length < 2 ^ 63 ∧
  (∀ t p, fl.pending !! t = some p → p.ids.length = p.alloctx.length)

/-- The `n` ids from `id` on. -/
def runIds (id : w64) (n : Nat) : List w64 := (List.range n).map fun j : Nat => id + W64 (j : Int)

/-- `x` is one of the `n` ids from `r` on. -/
def inRun (r : w64) (n : Nat) (x : w64) : Prop := r.toNat ≤ x.toNat ∧ x.toNat < r.toNat + n

instance (r : w64) (n : Nat) (x : w64) : Decidable (inRun r n x) := by
  unfold inRun; infer_instance

/-! ## The operations -/

/-- `Allocate(txid, n)` returned `r`: the `n` ids from `r` on are no longer free, and are
`txid`'s. -/
def FLPg.alloc (fl : FLPg) (txid r : w64) (n : Nat) : FLPg :=
  { fl with free := fl.free.filter (fun x => decide ¬ inRun r n x),
            allocs := fl.allocs.insert r txid }
proj_simps FLPg.alloc

/-- The `n` ids from `r` on are free (what `Allocate` returns). -/
def FLPg.canAlloc (fl : FLPg) (r : w64) (n : Nat) : Prop :=
  r.toNat + n ≤ 2 ^ 64 ∧ ∀ x, inRun r n x → x ∈ fl.free

/-- `Free(txid, p)` (`FLPg.freePages`: the name `free` is the field's) of a page of `n` slots from `id`: pending for `txid`, with the transaction
that allocated it (`0` if unknown), which `allocs` forgets. -/
def FLPg.freePages (fl : FLPg) (txid id : w64) (n : Nat) : FLPg :=
  let pd := (fl.pending !! txid).getD ⟨[], [], 0⟩
  { fl with
    pending := fl.pending.insert txid ⟨pd.ids ++ runIds id n,
      pd.alloctx ++ List.replicate n ((fl.allocs !! id).getD 0), pd.lastReleaseBegin⟩,
    allocs := fl.allocs.delete id }

/-- `Free` does not panic: the pages are neither metas, nor free, nor pending, `txid` did not
allocate the first, and there are not too many. -/
def FLPg.canFree (fl : FLPg) (txid id : w64) (n : Nat) : Prop :=
  2 ≤ id.toNat ∧ id.toNat + n < 2 ^ 64 ∧ (∀ x ∈ runIds id n, x ∉ fl.allIds) ∧
  (fl.allocs !! id).getD 0 ≠ txid ∧ fl.allIds.length + n < 2 ^ 63

/-- `release(txid)`: every page pending for a transaction at or before `txid` is free. -/
def FLPg.release (fl : FLPg) (txid : w64) : FLPg :=
  let rel := fl.pending.filter fun t _ => decide (t.toNat ≤ txid.toNat)
  { fl with free := sortPgids (fl.free ++ rel.toList.flatMap fun kv => kv.2.ids),
            pending := fl.pending.filter fun t _ => decide (txid.toNat < t.toNat) }

/-- A pair's allocating transaction is in `[b, e]` (`releaseRange`'s inner test). -/
def inRR (b e : w64) (x : w64 × w64) : Bool := decide (b.toNat ≤ x.2.toNat ∧ x.2.toNat ≤ e.toNat)

/-- `releaseRange`'s inner loop from index `j` on the pairs `Q`: the pairs left. -/
def srLoop (b e : w64) (j : Nat) (Q : List (w64 × w64)) : List (w64 × w64) :=
  if h : j < Q.length then
    if inRR b e Q[j] then
      srLoop b e j ((Q.set j (Q[Q.length - 1]'(by omega))).take (Q.length - 1))
    else srLoop b e (j + 1) Q
  else Q
termination_by Q.length - j + Q.length
decreasing_by
  · simp only [List.length_take, List.length_set]; omega
  · omega

theorem srLoop_rm {b e : w64} {j : Nat} {Q : List (w64 × w64)} (h : j < Q.length)
    (hin : inRR b e Q[j] = true) :
    srLoop b e j Q =
      srLoop b e j ((Q.set j (Q[Q.length - 1]'(by omega))).take (Q.length - 1)) := by
  rw [srLoop]; simp only [h, dite_true, hin, ite_true]

theorem srLoop_skip {b e : w64} {j : Nat} {Q : List (w64 × w64)} (h : j < Q.length)
    (hin : inRR b e Q[j] = false) : srLoop b e j Q = srLoop b e (j + 1) Q := by
  rw [srLoop]; simp only [h, dite_true, hin, Bool.false_eq_true, ite_false]

theorem srLoop_end {b e : w64} {j : Nat} {Q : List (w64 × w64)} (h : ¬ j < Q.length) :
    srLoop b e j Q = Q := by
  rw [srLoop]; simp only [h, dite_false]

/-- `l[j] = l[last]; l = l[:last]` and `l[j]`: `l`, up to order. -/
theorem swap_take_perm {α : Type} (l : List α) (j : Nat) (hj : j < l.length) :
    ((l.set j (l[l.length - 1]'(by omega))).take (l.length - 1) ++ [l[j]]).Perm l := by
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

/-- The loop keeps the pairs allocated outside `[b, e]`, up to order. -/
theorem srLoop_perm (b e : w64) : ∀ (n j : Nat) (Q : List (w64 × w64)),
    Q.length - j + Q.length ≤ n → (∀ x ∈ Q.take j, inRR b e x = false) →
    (srLoop b e j Q).Perm (Q.filter fun x => !inRR b e x)
  | 0, j, Q, hn, h => by
    have : Q = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; rw [srLoop_end (by simp)]; exact List.Perm.refl _
  | n + 1, j, Q, hn, h => by
    by_cases hj : j < Q.length
    · by_cases hin : inRR b e Q[j] = true
      · rw [srLoop_rm hj hin]
        have hsw := swap_take_perm Q j hj
        refine (srLoop_perm b e n j _ (by simp only [List.length_take, List.length_set]; omega)
          ?_).trans ?_
        · intro x hx
          rw [List.take_take, Nat.min_eq_left (by omega), List.take_set_of_le (Nat.le_refl _)] at hx
          exact h x hx
        · have := hsw.filter (fun x => !inRR b e x)
          rw [List.filter_append] at this
          simp only [List.filter_cons, List.filter_nil, hin, Bool.not_true, Bool.false_eq_true,
            ite_false, List.append_nil] at this
          exact this
      · have hin' : inRR b e Q[j] = false := by simpa using hin
        rw [srLoop_skip hj hin']
        refine srLoop_perm b e n (j + 1) Q (by omega) ?_
        intro x hx
        rw [List.take_add_one, List.getElem?_eq_getElem hj] at hx
        rcases List.mem_append.1 hx with hx | hx
        · exact h x hx
        · simp only [Option.toList_some, List.mem_singleton] at hx; subst hx; exact hin'
    · rw [srLoop_end hj]
      rw [List.take_of_length_le (by omega)] at h
      rw [List.filter_eq_self.2 (fun x hx => by rw [h x hx]; rfl)]

/-- A pair is kept by the loop iff it is allocated outside `[b, e]`. -/
theorem mem_srLoop (b e : w64) (Q : List (w64 × w64)) (x : w64 × w64) :
    x ∈ srLoop b e 0 Q ↔ x ∈ Q.filter (fun x => !inRR b e x) :=
  (srLoop_perm b e _ 0 Q (Nat.le_refl _) (by simp)).mem_iff

/-- `releaseRange(begin, end)` on one pending entry: the pages allocated in `[begin, end]` are
taken out (and returned), the others kept in the code's order (U2 fix: Go removes a pair by
moving the last one into its place, `srLoop`; the kept pairs are the others up to order,
`srLoop_perm`). -/
def releaseRangeOne (b e : w64) (p : Pending) : List w64 × Pending :=
  let both := p.ids.zip p.alloctx
  let K := srLoop b e 0 both
  ((both.filter (inRR b e)).map Prod.fst, ⟨K.map Prod.fst, K.map Prod.snd, b⟩)

/-- `releaseRange(begin, end)`: the pages pending for a transaction in `[begin, end]` that were
allocated in `[begin, end]` are free (an entry already released from `begin` is skipped; an
emptied entry is deleted). -/
def FLPg.releaseRange (fl : FLPg) (b e : w64) : FLPg :=
  if e.toNat < b.toNat then fl else
  let sel := fun (t : w64) (p : Pending) =>
    decide (b.toNat ≤ t.toNat ∧ t.toNat ≤ e.toNat ∧ p.lastReleaseBegin ≠ b)
  let touched := fl.pending.filter sel
  let freed := touched.toList.flatMap fun kv => (releaseRangeOne b e kv.2).1
  let kept := touched.fmap fun p => (releaseRangeOne b e p).2
  { fl with
    free := sortPgids (fl.free ++ freed),
    pending := (fl.pending.filter (fun t p => !sel t p)) ∪
      kept.filter (fun _ p => decide (p.ids ≠ [])) }

/-- `ReleasePendingPages()` with the read-only transactions `ro` (`readonlyTXIDs`): release
everything before the oldest reader, then every range between readers. -/
def FLPg.releasePending (fl : FLPg) (ro : List w64) : FLPg :=
  let ro := sortPgids ro
  let minid : w64 := (ro.head?).getD (W64 (-1))
  let fl := if 0 < minid.toNat then fl.release (minid - 1) else fl
  let (fl, minid) := ro.foldl (fun (acc : FLPg × w64) t =>
    (acc.1.releaseRange acc.2 (t - 1), t + 1)) (fl, minid)
  fl.releaseRange minid (W64 (-1))

/-- `Rollback(txid)` of `txid`'s pending entry: its pages are not pending any more (those
allocated by another transaction get their `allocs` back), and `txid`'s allocations are
forgotten. -/
def FLPg.rollbackEntry (fl : FLPg) (txid : w64) : FLPg :=
  let pd := (fl.pending !! txid).getD ⟨[], [], 0⟩
  let back := (pd.ids.zip pd.alloctx).filter fun x => decide (x.2 ≠ 0 ∧ x.2 ≠ txid)
  let allocs := back.foldl (fun m x => m.insert x.1 x.2) fl.allocs
  { fl with pending := fl.pending.delete txid,
            allocs := allocs.filter fun _ t => decide (t ≠ txid) }

/-- `Rollback(txid)` as the code does it (U2 fix): nothing without a pending entry for `txid`
(Go returns at once, `allocs` untouched), else `rollbackEntry`. -/
def FLPg.rollback (fl : FLPg) (txid : w64) : FLPg :=
  if fl.pending !! txid = none then fl else fl.rollbackEntry txid

/-- `Reload(p)`/`NoSyncReload(ids)`: the free ids are `ids` but the pending ones. -/
def FLPg.reload (fl : FLPg) (ids : List w64) : FLPg :=
  { fl with free := sortPgids (ids.filter fun x => decide (x ∉ fl.pendingIds)) }
proj_simps FLPg.reload

/-- `NoSyncReload(ids)`, the same as `Reload` on the ids `freepages` computed. -/
def FLPg.noSyncReload (fl : FLPg) (ids : List w64) : FLPg := fl.reload ids

/-- `Init(ids)` on a fresh freelist (`loadFreelist`): the free ids are `ids`. -/
def FLPg.ofInit (ids : List w64) : FLPg := { FLPg.empty with free := sortPgids ids }
proj_simps FLPg.ofInit

end bbolt
end EtcdGrove
end Perennial
