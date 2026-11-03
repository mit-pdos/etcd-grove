/-
bbolt's MVCC rule as pure facts (U0a of `notes/bbolt-proof-plan.md`; design §3.2, §3.6): views,
registered readers, and what the freelist must satisfy so that no page a view sees is reused.

Ported from `old/bbolt/.../DBPred.lean` (`mvccView`, `flBelow`, `flCurOK`, `pagesAgree`) over
records: a view is the pages of transaction `txid` at the mapping `base`.
-/
module

public import Proof.go_etcd_io.bbolt.Model.TreeData
public import Proof.go_etcd_io.bbolt.Model.FL

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

section mvcc
variable [GooseExts]

/-- **A view** (a reader's, or the writer's base) of transaction `txid`, at the mapping `base`:
the pages it sees. -/
structure View where
  base : Loc
  txid : Nat
  pages : Pages
  /-- The root bucket's root page (what the view's `Tx.root` reads). -/
  root : Nat
  deriving Inhabited

instance View.countable : Pos.Countable View :=
  countableOfLeftInverse (fun v => (v.base, v.txid, v.pages, v.root))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩) (fun _ => rfl)

/-- The view of the committed state `C` at the mapping `base`. -/
def View.ofC (base : Loc) (C : CommitSt) : View := ⟨base, C.txid, C.pages, C.root⟩
proj_simps View.ofC

/-- The data a view holds (`treeData` of its pages and root): a reader's snapshot. -/
def View.data (v : View) : Data :=
  GMap.ofList ((treeEntries v.pages v.root).map fun e => (e.1, bktOfPage v.pages e.2))

/-- A registered reader (`pagesInv`'s registry): its view. -/
structure RdInfo where
  v : View
  deriving Inhabited

instance RdInfo.countable : Pos.Countable RdInfo :=
  countableOfLeftInverse (fun r => r.v) (fun v => ⟨v⟩) (fun _ => rfl)

/-- The slots of every pending page (`Free` records each slot of an extent). -/
def pendSlots (fl : FLPg) : List Nat := fl.pendingIds.map BitVec.toNat

/-- **bbolt's MVCC rule for a view** (old `mvccView`): its pages were allocated by its
transaction or before; a slot it covers is no meta page, not free, and pending only from a
transaction newer than the view that freed a page allocated by the view's transaction or
before. -/
def mvccView (fl : FLPg) (v : View) : Prop :=
  (∀ id pg, v.pages !! id = some pg → ∀ a, fl.allocs !! W64 (id : Int) = some a →
    a.toNat ≤ v.txid) ∧
  ∀ s, coversSlot v.pages s → 2 ≤ s ∧ W64 (s : Int) ∉ fl.free ∧
    ∀ t pd i, fl.pending !! t = some pd → pd.ids[i]? = some (W64 (s : Int)) →
      (pd.alloctx.getD i 0).toNat ≤ v.txid ∧ v.txid < t.toNat

/-- **The freelist is below the committed state** (old `flBelow`, round 4 N6: without its
writer clause, which `storeOK`'s `wtx`/`pub` clauses replace): free ids and the pending ids of
committed transactions below the high-water mark; every pending transaction committed or the
live writer's `w` (its allocations before it); the txid does not wrap; ids below `2^62`. -/
def flBelow (fl : FLPg) (C : CommitSt) (w : Option Nat) : Prop :=
  (∀ x ∈ fl.free, x.toNat < C.hwm) ∧
  (∀ t pd x, fl.pending !! t = some pd → x ∈ pd.ids → t.toNat ≤ C.txid → x.toNat < C.hwm) ∧
  (∀ t pd, fl.pending !! t = some pd →
    t.toNat ≤ C.txid ∨ (w = some t.toNat ∧ ∀ a ∈ pd.alloctx, a.toNat < t.toNat)) ∧
  C.txid + 1 < 2 ^ 64 ∧ (∀ x ∈ fl.free, x.toNat < 2 ^ 62) ∧
  (∀ x ∈ fl.pendingIds, x.toNat < 2 ^ 62)

/-- Slot `s` is pending only for the live writer `w` (a current tree's page it freed). -/
def pendingOnlyFromWriter (fl : FLPg) (w : Option Nat) (s : Nat) : Prop :=
  ∀ t pd, fl.pending !! t = some pd → W64 (s : Int) ∈ pd.ids → w = some t.toNat

/-- Two page maps that cover a slot see the same page there (views agree where they
overlap). -/
def pagesAgree (P Q : Pages) : Prop :=
  ∀ i pi j pj s, P !! i = some pi → Q !! j = some pj →
    i ≤ s → s < i + (1 + pageOverflow pi) → j ≤ s → s < j + (1 + pageOverflow pj) →
      i = j ∧ pi = pj

/-! ## Freelist pages (`freelist.Read`/`Write`, `page.go`'s `FreelistPageCount`) -/

/-- The header count of a freelist page, and the index its ids start at: a count of `0xFFFF`
means the count is the first `uint64` after the header. -/
def flCountIdx (pg : List w8) : Nat × Nat :=
  if pageCount pg < 0xFFFF then (pageCount pg, 0)
  else ((decode (bytesAt pg 16 8) : w64).toNat, 1)

/-- The ids of a freelist page. -/
def flIds (pg : List w8) : List w64 :=
  (List.range (flCountIdx pg).1).map fun i =>
    (decode (bytesAt pg (16 + 8 * (flCountIdx pg).2 + 8 * i) 8) : w64)

/-- `x` is pending for a committed transaction (`C.txid` or before). -/
def committedPending (fl : FLPg) (C : CommitSt) (x : w64) : Prop :=
  ∃ t pd, fl.pending !! t = some pd ∧ x ∈ pd.ids ∧ t.toNat ≤ C.txid

/-- **The synced freelist page `pg` can be reloaded** (old `flCurOK`, round 2 F4.2: over the
page's bytes, which are a W slot's, so it is stated in `wdbOK`): when `C` names a freelist page,
`pg` is a freelist page whose ids lie within it, are distinct, at least 2, not in its own
extent; they include every free id and every committed transaction's pending id, and each is
committed-pending or could be free (below the high-water mark, not a tree page). -/
def flCurOK (fl : FLPg) (C : CommitSt) (pg : List w8) : Prop :=
  ∀ f, C.flpg = some f →
    2 ≤ f ∧ f + (1 + pageOverflow pg) ≤ C.hwm ∧ pg.length = (1 + pageOverflow pg) * 4096 ∧
    pageFlags pg = freelistPageFlag ∧
    16 + 8 * (flCountIdx pg).2 + 8 * (flCountIdx pg).1 ≤ pg.length ∧
    (flIds pg).Nodup ∧ (∀ x ∈ flIds pg, 2 ≤ x.toNat) ∧
    (∀ x ∈ flIds pg, ¬ (f ≤ x.toNat ∧ x.toNat < f + (1 + pageOverflow pg))) ∧
    (∀ s, f ≤ s → s < f + (1 + pageOverflow pg) → ¬ coversSlot C.pages s ∧
      W64 (s : Int) ∉ fl.allIds) ∧
    (∀ x ∈ fl.free, x ∈ flIds pg) ∧ (∀ x, committedPending fl C x → x ∈ flIds pg) ∧
    (∀ x ∈ flIds pg, committedPending fl C x ∨
      (x.toNat < C.hwm ∧ x.toNat < 2 ^ 62 ∧ ¬ coversSlot C.pages x.toNat))

/-! ## Lemma statements (U3) -/

/-- `release(txid)` frees no page of a view of a transaction at or after `txid` (its pending
pages are newer than the view). Used by U3 (`store_release`). -/
theorem mvccView_release (fl : FLPg) (v : View) (txid : w64) (h : mvccView fl v)
    (ht : txid.toNat ≤ v.txid) : mvccView (fl.release txid) v := by
  sorry

/-- `releaseRange(b, e)` frees no page of a view outside `[b, e]`. Used by U3
(`store_release`). -/
theorem mvccView_releaseRange (fl : FLPg) (v : View) (b e : w64) (h : mvccView fl v)
    (ht : v.txid < b.toNat ∨ e.toNat < v.txid) : mvccView (fl.releaseRange b e) v := by
  sorry

/-- A writer's `Free` keeps the MVCC rule of every older view: a freed page of the view becomes
pending for a newer transaction, allocated at or before the view. Used by U3 (`store_free`). -/
theorem mvccView_free (fl : FLPg) (v : View) (txid id : w64) (n : Nat) (h : mvccView fl v)
    (ht : v.txid < txid.toNat) (hfree : fl.canFree txid id n)
    (hpg : (∃ pg, v.pages !! id.toNat = some pg ∧ 1 + pageOverflow pg = n) ∨
      ∀ j < n, ¬ coversSlot v.pages (id.toNat + j)) :
    mvccView (fl.freePages txid id n) v := by
  sorry

/-- `Allocate` takes free ids, which no view sees. Used by U3 (`store_alloc`). -/
theorem mvccView_alloc (fl : FLPg) (v : View) (txid r : w64) (n : Nat) (h : mvccView fl v)
    (ha : fl.canAlloc r n) : mvccView (fl.alloc txid r n) v := by
  sorry

end mvcc

end bbolt
end EtcdGrove
end Perennial
