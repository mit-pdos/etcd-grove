/-
# mvcc's store: the pure model (batch 3e)

The meaning of mvcc's client-facing specs (`Api.lean`), transparent. **The store's history is W0's
`KVHist`** (`api/v3/Model.lean`: the events of revisions `2, 3, …`, revision `1` the empty store a
new store starts at, and the compaction revision, `0` for none): a member's store applies the
committed log, so the server's invariant (2d) ties `MvccState.kv` to the cluster's history at the
member's applied point by equality (`histAt γ k σ` with `σ.kv`), and the watch batch (3f) states
its events in the same terms as the client's watch model (1b). mvcc's own encoding differs only
where Go does: the compaction revision reads `-1` before any compaction (`compactMainRev`,
`MvccState.crev`), a key range has a `nil` end (`MRange`), a lease id is an `int64`.

## The state

`MvccState`: the committed history `kv` and the **pending** events: the revision the watchable
store has sent to its watchers and not yet made visible to reads (`watchableStoreTxnWrite.End`
notifies before `storeTxnWrite.End` bumps `currentRev`: the user's decision of 2026-11-02, round 8
of `notes/mvcc-api-candidate.md`). A commit is two steps of the state, `notify` then
`commitPending`; a store without watchers does both at its bump. Reads answer from `kv`, exactly;
the watch guarantee (3f) is stated over `notified` (`kv` with the pending revision).

## Transactions

`MTxn`: a read transaction at a state, or a write transaction begun at a state with the events it
has made so far (its pending revision, `pend`). A write transaction's reads see `pend`
(`MTxn.readHist`: the history with `pend` committed; revision `beginRev + 1` once it has a change,
`storeTxnWrite.Range`).

## Writes

A put of `k` at revision `R` writes `putRec R (s k) v l` over the key's record in the store `s` the
transaction sees (its create revision kept, its version incremented, as `storeTxnWrite.put` reads
them from the index); a delete of a range writes `.delete k` for each key present, in key order
(`deleteRange` reads the index at the transaction's revision). `EvsWf` is what a revision's events
can be; `MvccReachable` the states a store goes through.

## Ranges

`MRange` is `(key, end)` as mvcc takes it; `rangeResult s rg ro kvs count` what a range of the store
`s` returns for the options `ro` (limit, count-only, keys-only from the index with lease `0` and no
value, total count); `rangeOut h crev rg ro out` adds the revision checks (`ErrFutureRev`,
`ErrCompacted`) and the context's cancellation (a full read checks the context between keys).

## Leases

`storeItems s`: the store's key→lease map (`0`: none): what the lessor's item map must be while the
store's writers attach and detach keys (`Api.lean`, `leaseItems`).
-/
module

public import Spec.go_etcd_io.etcd.api.v3.Wire
public import GeneratedProof.go_etcd_io.etcd.server.v3.storage.mvcc

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Mvcc

open EtcdModel EtcdWire
open Classical

section model
variable [GooseExts]

/-! ## Ranges -/

/-- **mvcc's key range** `(key, end)`: `end` `nil` (`endNil`) names the key alone; an empty `end`
every key from `key` on; any other `end` the half-open range `[key, end)` (`treeIndex.unsafeVisit`:
an empty end bounds nothing). etcd's request layer maps a request's `"\x00"` end to the empty one
(`mkGteRange`). -/
structure MRange where
  key : Key
  endNil : Bool
  rangeEnd : Bytes

def MRange.mem (rg : MRange) (k : Key) : Prop :=
  if rg.endNil then k = rg.key
  else if rg.rangeEnd = [] then keyLe rg.key k
  else keyLe rg.key k ∧ keyLt k rg.rangeEnd

/-- The present keys of `s` in `rg`, in key order, as key-values. -/
def rangeKVs (s : EtcdModel.Store) (rg : MRange) (l : List KV) : Prop :=
  l.Pairwise (fun a b => keyLt a.key b.key) ∧
  ∀ kv, kv ∈ l ↔ (rg.mem kv.key ∧ s kv.key = some
    { createRev := kv.createRev, modRev := kv.modRev, version := kv.version, value := kv.value,
      lease := kv.lease })

/-- The present keys of `s` in `rg`, in key order. -/
def rangeKeys (s : EtcdModel.Store) (rg : MRange) (ks : List Key) : Prop :=
  ks.Pairwise keyLt ∧ ∀ k, k ∈ ks ↔ (rg.mem k ∧ (s k).isSome)

/-- A keys-only read's key-value (`FastKeysOnly`: from the index, no value, lease `0`). -/
def keysOnlyM (kv : KV) : KeyValueM :=
  { key := kv.key, createRevision := W64 kv.createRev, modRevision := W64 kv.modRev,
    version := W64 kv.version, value := [], lease := W64 0 }

/-- **A key-value safe to sort**: positive create and mod revisions and version, each an `int64`
(etcd's comparators subtract them, `txn/range.go`). -/
def kvSortOk (kv : KV) : Prop :=
  0 < kv.createRev ∧ kv.createRev < 2 ^ 63 ∧ 0 < kv.modRev ∧ kv.modRev < 2 ^ 63 ∧
  0 < kv.version ∧ kv.version < 2 ^ 63

/-- **The key-values a range found are safe to sort** (each `kvSortOk`, at most `2 ^ 62` of them:
the premise of Perennial's `sort` spec, its heapsort fallback's arithmetic). The size bound is a
temporary, local assumption of that limitation (`notes/perennial-changes.md`, "`sort.Sort`'s size
premise"), stated where a range's results are produced, not as a law of the store's state (the
user, round 15 of the mvcc API: "as local as possible"). -/
def kvsFit (l : List KV) : Prop := l.length ≤ 2 ^ 62 ∧ ∀ kv ∈ l, kvSortOk kv

/-- **What a range of the store `s` returns** for the options `ro`: the present keys of `rg`
(`all`), cut at `ro.Limit` when it is positive; with `CountOnly`, no key-value and the count of
`all`; with `FastKeysOnly`, the cut keys as `keysOnlyM`; else their whole records (read back from
the storage: `KeyValueM.ofKV`). The count is `all`'s with `WithTotalCount` (or `CountOnly`), else
the number returned (the index stops at the limit). -/
def rangeResult (s : EtcdModel.Store) (rg : MRange) (ro : go_etcd_io.etcd.server.v3.storage.mvcc.RangeOptions)
    (kvs : List KeyValueM) (count : Int) : Prop :=
  ∃ all : List KV, rangeKVs s rg all ∧ kvsFit all ∧
    if ro.CountOnly' then kvs = [] ∧ count = all.length
    else
      let lim := sint.Z ro.Limit'
      let out := if 0 < lim ∧ lim < all.length then all.take lim.toNat else all
      kvs = (if ro.FastKeysOnly' then out.map keysOnlyM else out.map KeyValueM.ofKV) ∧
      count = (if ro.WithTotalCount' then all.length else out.length)

/-- The revision a range reads in a history whose current revision is `cur`: the one asked, or the
current one for `ro.Rev ≤ 0`. -/
def readAt (cur : Nat) (ro : go_etcd_io.etcd.server.v3.storage.mvcc.RangeOptions) : Int :=
  if sint.Z ro.Rev' ≤ 0 then cur else sint.Z ro.Rev'

/-- A range's outcome, as the caller inspects it. -/
inductive RangeOut where
  /-- the key-values and count read, at the reader's revision `rev` (`RangeResult.Rev`) -/
  | ok (kvs : List KeyValueM) (count : Int) (rev : Nat)
  /-- `ErrFutureRev`: `RangeResult{Rev: cur, Count: -1}` -/
  | futureRev (cur : Nat)
  /-- `ErrCompacted`: `RangeResult{Rev: 0, Count: -1}` -/
  | compacted
  /-- the context was done during a full read: a `nil` result and a non-`nil` error -/
  | ctxErr

/-- **A range's outcome over the history `h`** (the reader's: its current revision is the
reader's, `h.rev`), its compaction revision `crev`: a revision above `h.rev` is `ErrFutureRev`; one
below `crev` is `ErrCompacted`; else the result at that revision (`rangeResult`), or, for a full
read (neither count-only nor keys-only), the context's error. -/
def rangeOut (h : KVHist) (crev : Int) (rg : MRange)
    (ro : go_etcd_io.etcd.server.v3.storage.mvcc.RangeOptions) : RangeOut → Prop
  | .futureRev cur => (h.rev : Int) < sint.Z ro.Rev' ∧ cur = h.rev
  | .compacted => sint.Z ro.Rev' ≤ (h.rev : Int) ∧ readAt h.rev ro < crev
  | .ok kvs count rev => sint.Z ro.Rev' ≤ (h.rev : Int) ∧ crev ≤ readAt h.rev ro ∧ rev = h.rev ∧
      rangeResult (h.storeAt (readAt h.rev ro).toNat) rg ro kvs count
  | .ctxErr => sint.Z ro.Rev' ≤ (h.rev : Int) ∧ crev ≤ readAt h.rev ro ∧
      ro.CountOnly' = false ∧ ro.FastKeysOnly' = false

/-! ## Writes -/

/-- **The record a put of `v` with lease `l` writes at revision `R`** over the key's record `prev`
(`storeTxnWrite.put`: the create revision kept, `R` for a new key; the version one more). -/
def putRec (R : Nat) (prev : Option KeyRec) (v : Bytes) (l : Int) : KeyRec :=
  { createRev := (prev.map (·.createRev)).getD R, modRev := R,
    version := (prev.map (·.version)).getD 0 + 1, value := v, lease := l }

/-- **The events a revision `R` may hold**, over the store `s` before them: puts whose records are
`putRec R` over the key's record so far, deletes of keys present so far. -/
def EvsWf (R : Nat) : EtcdModel.Store → List Event → Prop
  | _, [] => True
  | s, .put k r :: es => r = putRec R (s k) r.value r.lease ∧ EvsWf R (s.applyEvent (.put k r)) es
  | s, .delete k :: es => (s k).isSome ∧ EvsWf R (s.applyEvent (.delete k)) es

/-- The number of events of a history. -/
def evCount (h : KVHist) : Nat := (h.revs.map List.length).sum

/-! ## The state -/

/-- **The store's abstract state**: its committed history (with its compaction revision) and the
events of the revision being committed (sent to the watchers, not yet visible to reads; `[]` when
none). -/
structure MvccState where
  kv : KVHist
  pending : List Event

/-- The current revision (`currentRev`). -/
def MvccState.rev (σ : MvccState) : Nat := σ.kv.rev

/-- The compaction revision as mvcc reports it (`compactMainRev`, `FirstRev`): `-1` before any
compaction. -/
def MvccState.crev (σ : MvccState) : Int := if σ.kv.compacted = 0 then -1 else σ.kv.compacted

/-- The history the watchers were sent: the committed one with the pending revision. -/
def MvccState.notified (σ : MvccState) : KVHist := σ.kv.commit σ.pending

/-- **A commit's first step**: the events `pend` sent to the watchers. -/
def MvccState.notify (σ : MvccState) (pend : List Event) : MvccState := { σ with pending := pend }

/-- **A commit's second step**: the pending revision made visible to reads. -/
def MvccState.commitPending (σ : MvccState) : MvccState :=
  { kv := σ.kv.commit σ.pending, pending := [] }

/-- A compaction at `r`. -/
def MvccState.compactTo (σ : MvccState) (r : Nat) : MvccState :=
  { σ with kv := { σ.kv with compacted := r } }

/-- A new store's state: revision `1`, empty, never compacted, nothing pending. -/
def mvccStart : MvccState := ⟨{ revs := [], compacted := 0 }, []⟩

/-- **The states a store goes through**: from `mvccStart` (or a restored state, `Restore`'s
premise), a commit's two steps of well-formed events, compactions above the last and at most the
current revision. -/
inductive MvccReachable : MvccState → Prop
  | start : MvccReachable mvccStart
  | notify (σ : MvccState) (pend : List Event) :
      MvccReachable σ → σ.pending = [] → EvsWf (σ.kv.rev + 1) σ.kv.store pend →
      MvccReachable (σ.notify pend)
  | commit (σ : MvccState) : MvccReachable σ → MvccReachable σ.commitPending
  | compact (σ : MvccState) (r : Nat) :
      MvccReachable σ → σ.pending = [] → 1 ≤ r → σ.kv.compacted < r → r ≤ σ.kv.rev →
      MvccReachable (σ.compactTo r)

/-- **A transaction's view**: a read transaction at `σ`, or a write transaction begun at `σ` with
the events `pend` it has made. -/
inductive MTxn where
  | read (σ : MvccState)
  | write (σ : MvccState) (pend : List Event)

/-- The state the transaction began at. -/
def MTxn.state : MTxn → MvccState
  | .read σ => σ
  | .write σ _ => σ

/-- Its events (none for a read transaction). -/
def MTxn.pend : MTxn → List Event
  | .read _ => []
  | .write _ pend => pend

/-- The history its reads read: a write transaction's has its events committed (its revision
`beginRev + 1` once it has one). -/
def MTxn.readHist (k : MTxn) : KVHist := k.state.kv.commit k.pend

/-- The store a write transaction begun at `σ` sees after its events `pend`. -/
def txnStore (σ : MvccState) (pend : List Event) : EtcdModel.Store := σ.kv.store.applyEvents pend

/-- The event of a put in a write transaction begun at `σ`, after its events `pend` (`l`: the
lease id). -/
def putEv (σ : MvccState) (pend : List Event) (k : Key) (v : Bytes) (l : Int) : Event :=
  .put k (putRec (σ.kv.rev + 1) (txnStore σ pend k) v l)

/-! ## Leases -/

/-- **The store's key→lease map** (`0`: no lease, or no key). -/
def storeItems (s : EtcdModel.Store) (k : Key) : Int :=
  match s k with
  | some r => r.lease
  | none => 0

/-- The key→lease map a `Restore` leaves in the lessor: the store's, but the keys whose lease the
lessor does not have (`L`), which `restore`'s `Attach` fails for (the error is logged). -/
def itemsIn (L : List Int) (s : EtcdModel.Store) (k : Key) : Int :=
  if storeItems s k ∈ L then storeItems s k else 0

end model

end Mvcc
end EtcdGrove
end Perennial
