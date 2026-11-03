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

/-- `releaseRange(begin, end)` on one pending entry: the pages allocated in `[begin, end]` are
taken out (and returned). -/
def releaseRangeOne (b e : w64) (p : Pending) : List w64 × Pending :=
  let both := p.ids.zip p.alloctx
  let inR := fun (x : w64 × w64) => decide (b.toNat ≤ x.2.toNat ∧ x.2.toNat ≤ e.toNat)
  ((both.filter inR).map Prod.fst,
    ⟨(both.filter (fun x => !inR x)).map Prod.fst, (both.filter (fun x => !inR x)).map Prod.snd, b⟩)

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

/-- `Rollback(txid)`: `txid`'s pending pages are not pending any more (those allocated by
another transaction get their `allocs` back), and `txid`'s allocations are forgotten. -/
def FLPg.rollback (fl : FLPg) (txid : w64) : FLPg :=
  let pd := (fl.pending !! txid).getD ⟨[], [], 0⟩
  let back := (pd.ids.zip pd.alloctx).filter fun x => decide (x.2 ≠ 0 ∧ x.2 ≠ txid)
  let allocs := back.foldl (fun m x => m.insert x.1 x.2) fl.allocs
  { fl with pending := fl.pending.delete txid,
            allocs := allocs.filter fun _ t => decide (t ≠ txid) }

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
