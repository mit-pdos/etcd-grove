/-
# bbolt's `internal/freelist`: the free pages and their release discipline (batch 4d)

The freelist (`freelist.Interface`: the array and the hash map implementations, which differ only
in how they find a run of free pages) tracks, for the writer, which pages it may allocate, which
pages a committed (or committing) transaction freed but some reader may still see (*pending*),
and, beside them, the txids of the open read-only transactions (*readers*), which decide when a
pending page is safe to reuse.

## The model (`FLState`, transparent)

* `free`: the pages `Allocate` may hand out (`GSet Pgid`);
* `pending`: each pending page with the transaction that freed it and the one that allocated it
  (`PendingPg`; `alloc = 0`: not known, a page allocated before the freelist was last loaded);
* `allocs`: the first page of each run allocated since (`Allocate`), with its transaction, which
  `Free` moves into the pending entry and `Rollback` restores.

The readers are a multiset of txids, a `List Txid` up to order (`flReaders_perm`).

A pending page `(t, a)` is **releasable** with readers `R` when no reader `r` has `a ≤ r < t`:
no reader's snapshot holds the page (it was written by `a`, dropped by `t`). That is the safety
fact a client of `ReleasePendingPages` needs (bbolt's MVCC: a page is reused only once no open
read transaction can reach it); which releasable pages are released is the implementation's
(`releaseRange` skips an entry it already looked at from the same `begin`), but every page freed
before the oldest reader is (`mustRelease`).

## Resources (opaque)

* `flOwn fl F`: the freelist object behind the interface value `fl`, but its readers, is in
  state `F` (exclusive; the writer's: bbolt holds it under `rwlock`, or before the database is
  shared). Intended realization: a bundle per dynamic type (PRINCIPLES, "an interface value gets
  a bundle"): `fl` is a `*array` or a `*hashMap` whose `shared` fields `allocs`, `cache`,
  `pending` (and the array's `ids`, the hash map's span maps and count) hold `F` (`cache` the
  free and pending ids; the array's `ids` sorted; the spans maximal), with `F.wf`.
* `flReaders fl R`: its `readonlyTXIDs` field holds the multiset `R` (exclusive; bbolt holds it
  under `metalock`, where `beginTx` and `removeTx` add and remove a reader concurrently with the
  writer's `Allocate`/`Free`, which touch the other fields only).

The methods are called through the interface (`flCall fl m`: Go's `MethodResolve` on the
interface value, then the dynamic type's method); their specs are the bundle's triples
(`Interface__<M>.lean`), one per method for both implementations, proved once from the concrete
methods (`array.*`, `hashMap.*`, and `shared`'s promoted ones, whose own specs stay internal).

Laws: `flOwn_wf` (the model's invariant), `flOwn_timeless`, `flReaders_timeless`,
`flReaders_perm`.

## Bounds

`flMaxIds = 2^59` bounds the number of free and pending ids where the code counts or sorts them
(`EstimatedWritePageSize`'s `8 * (n + 1) + 16`, an `int`; Perennial's `sort.Sort` takes at most
`2^62` elements): a premise of those methods only. bbolt meets it from its file: every id is below
the high-water mark, at most `MaxMapSize / pageSize = 2^36`.

## Requirement snippets (`examples/specreq/bboltinternal/freelist.go`, `//go:build ignore`)

`ReqAllocFree` (an allocated run is no longer free; a freed page is pending, not free),
`ReqReleaseSafe` (a page pending while a reader that sees it is open stays unallocatable; once it is
gone, it is released), `ReqRollback` (a rolled-back transaction's frees are undone),
`ReqWriteReload` (the page `Write` leaves, read by `Reload`, gives back the free pages but the
pending), `ReqEstimate` (`Write` fits the estimated size).
-/
module

public import GeneratedProof.go_etcd_io.bbolt.internal.freelist
public import Spec.PkgInit.go_etcd_io.bbolt.internal.freelist
public import Spec.go_etcd_io.bbolt.internal.common.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Freelist

open Iris Iris.BI go_etcd_io.bbolt.internal.common BboltCommon

section model
variable [GooseExts]

/-- A pending page's transactions: the one that freed it, and the one that allocated it (`0`: not
known). -/
structure PendingPg where
  freer : Txid
  alloc : Txid

/-- **The freelist's state** but its readers (see the header). -/
structure FLState where
  free : GMap Pgid Unit
  pending : GMap Pgid PendingPg
  allocs : GMap Pgid Txid

/-- A new freelist (`NewArrayFreelist`, `NewHashMapFreelist`). -/
def FLState.empty : FLState := ⟨GMap.empty, GMap.empty, GMap.empty⟩

/-- The set of the ids `ids`. -/
def idSet (ids : List Pgid) : GMap Pgid Unit := GMap.ofList (ids.map fun x => (x, ()))

/-- **The free and pending ids, sorted** (`Copyall`, what `Write` stores). -/
def FLState.ids (F : FLState) : List Pgid := sortPgids (F.free.domList ++ F.pending.domList)

/-- **The number of free and pending ids** (`Count()`). -/
def FLState.count (F : FLState) : Nat := F.free.domList.length + F.pending.domList.length

/-- **The model's invariant**: no page both free and pending; the metas (0, 1) never in it. -/
def FLState.wf (F : FLState) : Prop :=
  (∀ p, p ∈ F.free → p ∉ F.pending) ∧ (∀ p, (p ∈ F.free ∨ p ∈ F.pending) → 2 ≤ p.toNat)

/-- The bound on the number of ids where the code counts or sorts them (see the header). -/
def flMaxIds : Nat := 2 ^ 59

/-- Strictly increasing ids, from 2 on (what `Init` and `NoSyncReload` take). -/
def idsOk (ids : List Pgid) : Prop :=
  ids.Pairwise (fun a b => a.toNat < b.toNat) ∧ ∀ x ∈ ids, 2 ≤ x.toNat

/-- `x` is one of the `n` ids from `r` on. -/
def inRun (r : Pgid) (n : Nat) (x : Pgid) : Bool := decide (r.toNat ≤ x.toNat ∧ x.toNat < r.toNat + n)

/-! ## The operations -/

/-- `Init(ids)`, `Read`: the free pages are `ids`. -/
def FLState.init (F : FLState) (ids : List Pgid) : FLState := { F with free := idSet ids }

/-- `NoSyncReload(ids)`, `Reload`: the free pages are `ids` but the pending ones. -/
def FLState.reload (F : FLState) (ids : List Pgid) : FLState :=
  { F with free := idSet (ids.filter fun x => decide (x ∉ F.pending)) }

/-- The `n` pages from `r` on are free (a run `Allocate` may return). -/
def FLState.canAlloc (F : FLState) (r : Pgid) (n : Nat) : Prop :=
  r ≠ W64 0 ∧ r.toNat + n ≤ 2 ^ 64 ∧ ∀ x : Pgid, inRun r n x = true → x ∈ F.free

/-- `Allocate(txid, n)` returned `r`: the run is no longer free, and is `txid`'s. -/
def FLState.alloc (F : FLState) (txid : Txid) (r : Pgid) (n : Nat) : FLState :=
  { F with free := F.free.filter (fun x _ => !inRun r n x), allocs := F.allocs.insert r txid }

/-- `Free(txid, p)` of a page of `n` slots from `id` does not panic: no meta, no wrap, none free
or pending, and (`Verify`'s check) not allocated by `txid`. -/
def FLState.canFree (F : FLState) (txid : Txid) (id : Pgid) (n : Nat) : Prop :=
  2 ≤ id.toNat ∧ id.toNat + n < 2 ^ 64 ∧
  (∀ x : Pgid, inRun id n x = true → x ∉ F.free ∧ x ∉ F.pending) ∧
  (F.allocs.lookup id).getD (W64 0) ≠ txid

/-- `Free(txid, p)`: the page's `n` slots are pending for `txid`, with `id`'s allocating
transaction (`0` if not known), which `allocs` forgets. -/
def FLState.freeRun (F : FLState) (txid : Txid) (id : Pgid) (n : Nat) : FLState :=
  let pp : PendingPg := ⟨txid, (F.allocs.lookup id).getD (W64 0)⟩
  { F with pending := (List.range n).foldl (fun m (k : Nat) => m.insert (id + W64 (k : Int)) pp) F.pending,
           allocs := F.allocs.delete id }

/-- `Rollback(txid)` does not panic: no page `txid` freed was allocated by `txid`. -/
def FLState.canRollback (F : FLState) (txid : Txid) : Prop :=
  ∀ p pp, F.pending.lookup p = some pp → pp.freer = txid → pp.alloc ≠ txid

/-- **`Rollback(txid)`**: nothing if `txid` freed nothing; else its pending pages are dropped
(neither free nor pending: bbolt reloads the freelist next), their allocating transactions
restored in `allocs`, and `txid`'s allocations forgotten. -/
def FLState.rollback (F : FLState) (txid : Txid) : FLState :=
  if ∃ p pp, F.pending.lookup p = some pp ∧ pp.freer = txid then
    let mine := F.pending.filter fun _ pp => decide (pp.freer = txid)
    let back := (mine.filter fun _ pp => decide (pp.alloc ≠ W64 0)).fmap PendingPg.alloc
    { F with pending := F.pending.filter (fun _ pp => decide (pp.freer ≠ txid)),
             allocs := (back ∪ F.allocs).filter fun _ t => decide (t ≠ txid) }
  else F

/-- Pending page `p` is **releasable** with the readers `R`: no reader's snapshot holds it (no
reader between its allocating and its freeing transaction). -/
def FLState.releasable (F : FLState) (R : List Txid) (p : Pgid) : Prop :=
  ∃ pp, F.pending.lookup p = some pp ∧
    ∀ r ∈ R, ¬ (pp.alloc.toNat ≤ r.toNat ∧ r.toNat < pp.freer.toNat)

/-- Pending page `p` **must be released** with the readers `R`: freed before every reader. -/
def FLState.mustRelease (F : FLState) (R : List Txid) (p : Pgid) : Prop :=
  ∃ pp, F.pending.lookup p = some pp ∧ pp.freer.toNat < 2 ^ 64 - 1 ∧
    ∀ r ∈ R, pp.freer.toNat < r.toNat

/-- The pages `S` released: free, no longer pending. -/
def FLState.release (F : FLState) (S : GMap Pgid Unit) : FLState :=
  { F with free := F.free ∪ S, pending := F.pending.filter fun p _ => decide (p ∉ S) }

/-- `ReleasePendingPages` does not misbehave: no reader is txid `0` or the largest (it computes
`tid - 1` and `tid + 1`, which would wrap and release pages a reader sees). -/
def readersOk (R : List Txid) : Prop := ∀ r ∈ R, 0 < r.toNat ∧ r.toNat < 2 ^ 64 - 1

/-- `EstimatedWritePageSize()`: the header and the ids, and a count `Pgid` from `0xFFFF` ids on. -/
def FLState.estimatedSize (F : FLState) : Nat :=
  pageHeaderSize + 8 * (F.count + if 0xFFFF ≤ F.count then 1 else 0)

end model

section call
variable [GooseExts] [GoGlobalContext]

/-- **A call of the freelist method `m` through the interface value `fl`**, as Goose emits it
(`MethodResolve` on the interface: the dynamic type's method; `nil` panics). -/
def flCall (fl : GoInterface) (m : GoString) : Expr :=
  App (Val (GoInstruction (MethodResolve go_etcd_io.bbolt.internal.freelist.Interface.ty m)))
    (Val #fl)

end call

section preds
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors}
  [hG : HeapGS HasLC.hasLC GF]

/-- **The freelist behind `fl`, but its readers, is in state `F`** (exclusive; see the header). -/
opaque flOwn (fl : GoInterface) (F : FLState) : IProp GF := iprop(True)

/-- **The open readers' txids recorded in the freelist behind `fl` are `R`**, as a multiset
(exclusive; see the header). -/
opaque flReaders (fl : GoInterface) (R : List Txid) : IProp GF := iprop(True)

/-- The model's invariant holds of every state the freelist is in. -/
def flOwn_wf.spec : Prop := ∀ fl F, flOwn (GF := GF) fl F ⊢ ⌜F.wf⌝

def flOwn_timeless.spec : Prop := ∀ fl F, Timeless (flOwn (GF := GF) fl F)
def flReaders_timeless.spec : Prop := ∀ fl R, Timeless (flReaders (GF := GF) fl R)

/-- The readers are a multiset: their order is not observable. -/
def flReaders_perm.spec : Prop := ∀ fl (R R' : List Txid),
  R.Perm R' → flReaders (GF := GF) fl R ⊢ flReaders fl R'

end preds

end Freelist
end EtcdGrove
end Perennial
