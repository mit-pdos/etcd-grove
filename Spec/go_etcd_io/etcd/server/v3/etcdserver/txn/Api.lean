/-
# etcd's server transactions (batch 3b): `server/v3/etcdserver/txn`, the vocabulary

`Range`, `Count`, `Put`, `DeleteRange` and `Txn` run one request over a member's mvcc store (and,
for a write, its lessor): the apply thread (3a's `applierV3backend`, every member, for a committed
request) and the request path (2c: `EtcdServer.Range`, `RangeStream`, a read-only `Txn`) call them.
This file is the vocabulary their specs share; the store's is 3e's (`storage/mvcc/{Model,Api}.lean`,
namespace `Mvcc`), the lessor's 3c's (`Lease`), the trace's 4b's (`TraceUtil`).

## The shape, in words

**The state a request acts on** is the store's `Mvcc.MvccState` (its history `σ.kv : KVHist`, W0's,
and a pending revision), in 3e's client-owned `Mvcc.mvccState γ σ`; for a write also the lessor's
state `ls` (3c's writer token `Lease.lessorState γl n ls`): its live leases (`ls.table`, W0's lease
table) decide a put's check, and mvcc's put and delete move its attachments (`evsLs`, 3e's steps).

* **A read** (`Range`, `Count`, a read-only `Txn`) takes the caller's atomic update over
  `mvccState`, the state unchanged, fired once when mvcc's read transaction begins; the answer is
  computed from `σ.kv`. Concurrent writers are allowed.
* **A write** (`Put`, `DeleteRange`, a `Txn` that is not read-only) takes the caller's update
  **pinned at `σ₀`** (nothing pending) and **nested as 3e's commit**: notify with the request's
  events, then the bump. 3e's `Txn.End` asks the state to still be the one its transaction began at,
  which only the store's sole writer (the apply thread) can assert; a writing `Txn` also reads, checks,
  then writes in two mvcc transactions (`txn.go:60-63`). An error after the write transaction began
  commits nothing and gives the update back; one before it (a dead lease, a failed check) too.
* The caller lends its context's trace (4b's `ctxTraceIs`, `ctxTraceOwn`: `EnsureTrace` keeps a
  context's non-empty trace) and gets back the trace returned (`traceBack`); a write lends the
  storage's share and `txnWriter` (3e's `Write` premises: the post-lock hook's run, the way back to
  the batch lock's invariant `Pk` and the caller's `Post`).

**The answers are functions of the state** (`putAns`, `rangeOut`, `run`): `goSort` names the
permutation Go's `sort.Sort` (pdqsort, deterministic) produces, so a range's answer is unique
although W0's `RangeReq.answers` allows any order among ties. The laws `rangeOut_answers`,
`run_txnRun` relate them to W0's relations (`RangeReq.answers`, `TxnRun`).

**Range ends** are W0's `KeyRange` of the request predicates, which read the end slice as mvcc does
(W0's unfold laws, round 1 of 3b's review: `nil` the key alone, a non-`nil` empty slice `"\x00"`,
every key from the key on); `Count` reads its raw slice the same way (`endOf`).

**Errors** are the values of the sentinels' package variables (`errIs err e`: mvcc's
`ErrCompacted`/`ErrFutureRev`, lease's `ErrLeaseNotFound`, etcdserver/errors' `ErrKeyNotFound`), and a
context's error inside mvcc's range (`ctxErr err`, only once the context is done).

## Vocabulary

Pure (transparent): `targetOk`, `endOf`, `countReq`, `rangeLimitZ`, `sortOut`, `assemble`,
`rangeOut`, `rangeAll`, `kvFits`, `hdrAt`, `ignores`, `needsPrev`, `putEvents`, `putPrev`, `putAns`,
`putHist`, `delEvents`, `leasesLive`, `attached`, `evsLs`, `cmpsHold`, `opCheck`/`opsCheck`,
`execOp`/`execOps`, `opPath`/`opsPath`, `txnPathOf`, `run`, `runEvs`, `runRev`,
`opIgnTaken`/`opsIgnTaken`, `opIgnKeys`/`opsIgnKeys`, `opDelRanges`/`opsDelRanges`,
`opSafe`/`opsSafe`, `txnSafe`, `txnK`, `viewRev`, `viewStore`, `viewErr` (over 3e's `MTxn`). Pure
(opaque): `goSort` (Go's sort; law `goSort_sorted`).

Resources: `errIs err e` (transparent: the sentinel's global), `ctxErr err` (opaque, persistent);
`txnWriter B Pk Post`, `ctxTraceOwn o`, `traceBack o tr` (transparent, over 3e's and 4b's); the
reply predicates `rangeOk`, `putOk`, `delOk`, `txnOk` (transparent, over W0's `Wire.lean`), `rrOwn`
(mvcc's `*RangeResult`, owned), `msgOpt` (a message the warnings may size); `roTxnResp` (opaque: a
read-only transaction's partly filled response) and `respSkel` (opaque, internal: the response
tree `newTxnResp` allocates).

**Provisional**, 3h's: `stringerOk s` (persistent: a `fmt.Stringer` whose `String()` returns).

## Intended realization

txn allocates no ghost state and keeps no invariant: each entry point passes the caller's update to
mvcc's transaction contracts (3e: `Read`'s update fired at the begin, `Write`'s a peek, `End`'s two
steps at the commit), reads the lessor through `Lookup` (3c, at the writer's token), and builds the
reply. `goSort` is realized by a functional model of Go's `sort.Sort` (a Perennial change: its spec
today gives a sorted permutation, not which one; `notes/specs-only/batch-3b.md`). `ctxErr` by
`fmt.Errorf`'s fresh value (3e's context outcome, asked to say it is none of the sentinels),
`roTxnResp` and `respSkel` by the response trees as `newTxnResp` builds them.

**Not yet provable from the callees as they are** (integration I5, 2026-11-09; recorded in
`notes/specs-only/integration-I5.md`): `ctxErr_not_errIs` (3e's `rangeResOwn` `.ctxErr` gives only
`err ≠ nil`: `req/..._storage_mvcc.md`, "from 3b", item 1); `rrOwn`'s `kvFits` on a range's result
(a record's lease an `int64`: item 2); `errIs_agree` and `errIs_ne_nil` at `.keyNotFound` (each
owner's initialization law gives its own sentinels distinct, none relates them across packages and
`etcdserver/errors` has none: wanted, each sentinel's variable holding 2c's `EtcdServer.srvErrVal e`,
with `srvErrOf_fun`).

## Laws

`goSort_sorted`, `rangeAll_eq`, `rangeOut_answers`, `run_txnRun`, `runEvs_readonly`,
`attached_evsLs`, `errIs_ne_nil`, `errIs_agree`, `ctxErr_persistent`, `ctxErr_ne_nil`,
`ctxErr_not_errIs`, `stringerOk_persistent`.

## Requirement snippets

`examples/specreq/txn/`: `read.go` (a limited range's count and `More`, a pinned revision and its
compaction error, `RangeStream`'s paging with `Count`, a count-only range, a sorted keys-only
filtered range, a read-only `Txn`), `write.go` (the apply thread as the sole writer: a put then a
range sees it, `IgnoreValue`, the lease check, a range delete, a delete with `PrevKv`, a CAS `Txn`, a
`Txn` with `skipRangeExecution`, a `Txn` whose check fails), `helpers.go` (`IsTxnReadonly`,
`IsTxnSerializable`, `IsDefaultOrdering`, `HasRevisionFilters` as 2a and 2c use them), `warn.go`
(the warnings as the request path and the uber applier call them).
-/
module

public import Spec.go_etcd_io.etcd.api.v3.Wire
public import Spec.context.Api
public import Spec.go_uber_org.zap.Api
public import Spec.google_golang_org.protobuf.proto.Api
public import Spec.go_etcd_io.etcd.server.v3.lease.Api
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Api
public import Spec.PkgInit.go_etcd_io.etcd.server.v3.etcdserver.errors
public import Spec.PkgInit.go_etcd_io.etcd.server.v3.etcdserver.txn
public import GeneratedProof.go_etcd_io.etcd.server.v3.etcdserver.txn
public import GeneratedProof.go_etcd_io.etcd.server.v3.storage.mvcc

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Txn

open Iris Iris.BI EtcdModel EtcdWire
open Classical

/-! ## Ranges -/

/-- **The sort target is one the server knows** (`KEY` … `VALUE`): `sortRangeResults` panics
(`lg.Panic`) on another, whatever the order. -/
def targetOk (r : RangeReq) : Prop := targetKey ≤ r.sortTarget ∧ r.sortTarget ≤ targetValue

/-- `rangeLimit(r)`: the limit mvcc is asked (`int64`): `0` with a non-default order or a revision
filter, else the request's, plus one when positive and below `MaxInt64`. -/
def rangeLimitZ (r : RangeReq) : Int :=
  let l : Int := if ¬ isDefaultOrdering r.sortTarget r.sortOrder ∨ r.hasRevFilters then 0 else r.limit
  if 0 < l ∧ l < 2 ^ 63 - 1 then l + 1 else l

/-- **Go's `sort.Sort` of the key-values `l`** by the sort target's order (`kvSortBy*.Less`),
ascending, or descending (`desc`: `sort.Reverse`). Opaque: pdqsort is deterministic, but which
permutation of equal elements it yields is its algorithm's. -/
opaque goSort (target : Int) (desc : Bool) (l : List KV) : List KV

/-- `goSort` sorts: a permutation, no element before a smaller one. -/
def goSort_sorted.spec : Prop := ∀ (target : Int) (desc : Bool) (l : List KV),
  (goSort target desc l).Perm l ∧
  (if desc then (goSort target desc l).Pairwise (fun a b => ¬ targetLt target a b)
   else (goSort target desc l).Pairwise (fun a b => ¬ targetLt target b a))

/-- **`sortRangeResults`**: a target other than the key with no order sorts ascending; the default
ordering (and an unknown order: no `case` of the switch) leaves the list alone. -/
def sortOut (r : RangeReq) (l : List KV) : List KV :=
  let order := if r.sortTarget ≠ targetKey ∧ r.sortOrder = sortNone then sortAscend else r.sortOrder
  if isDefaultOrdering r.sortTarget order then l
  else if order = sortAscend then goSort r.sortTarget false l
  else if order = sortDescend then goSort r.sortTarget true l
  else l

/-- **`asembleRangeResponse`**'s key-values and `More`: cut at the request's positive limit, values
dropped for keys-only. -/
def assemble (r : RangeReq) (l : List KV) : List KV × Bool :=
  let cut := decide (0 < r.limit ∧ r.limit < l.length)
  let out := if cut then l.take r.limit.toNat else l
  (if r.keysOnly then out.map (fun kv => { kv with value := [] }) else out, cut)

/-- **`executeRange`'s answer** from `all`, the present keys of the range at the revision read, in
key order: mvcc's limited fetch (`rangeLimit`; keys-only from the index, lease `0`), the revision
filters, the sort, the response's cut. `Count` is every key of the range (`withTotalCount`, or no
pushed-down limit, or count-only), else at most the pushed-down limit (`treeIndex.Revisions` stops
counting there). The fast keys-only path's key-values come from the index: no value and lease `0`
(mvcc's `keysOnlyM`), sorted as such. -/
def rangeOut (r : RangeReq) (wtc : Bool) (all : List KV) : RangeAns :=
  if r.countOnly then { kvs := [], more := false, count := all.length }
  else
    let L := r.pushdownLimit
    let fetched := if L = 0 then all else all.take L
    let fetched := if r.fastKeysOnly then fetched.map (fun kv => { kv with value := [], lease := 0 })
      else fetched
    let a := assemble r (sortOut r (fetched.filter r.keeps))
    { kvs := a.1, more := a.2,
      count := if wtc ∨ L = 0 then all.length else min all.length L }

/-- **The range end a slice names**: W0's `EtcdWire.endOf` (as mvcc reads the slice: `nil` the key
alone, a non-`nil` empty slice every key from the key on, `"\x00"`'s reading; else the bytes), which
the request predicates' unfold laws use. -/
abbrev endOf (sl : GoSlice) (e : Bytes) : Bytes := EtcdWire.endOf sl e

/-- `Count`'s request: a count-only range of `[key, rangeEnd)` at revision `rev`. -/
def countReq (key rangeEnd : Key) (rev : Int) : RangeReq :=
  { key := key, rangeEnd := rangeEnd, limit := 0, revision := rev, sortOrder := 0, sortTarget := 0,
    serializable := false, keysOnly := false, countOnly := true, minModRevision := 0,
    maxModRevision := 0, minCreateRevision := 0, maxCreateRevision := 0 }

/-- The present keys of `s` in `rg`, in key order (the unique such list; every store of a `KVHist`
has finite support, so it exists). -/
def rangeAll (s : EtcdModel.Store) (rg : KeyRange) : List KV :=
  if h : ∃ l, s.rangeKVs rg l then Classical.choose h else []

def rangeAll_eq.spec : Prop := ∀ (s : EtcdModel.Store) (rg : KeyRange) (l : List KV),
  s.rangeKVs rg l → rangeAll s rg = l

/-- **The answer is one W0's model allows** (with the total count, for a valid sort). -/
def rangeOut_answers.spec : Prop := ∀ (r : RangeReq) (s : EtcdModel.Store) (all : List KV),
  r.validSort → s.rangeKVs r.range all → r.answers s (rangeOut r true all)

/-- A key-value's numbers fit their `int64` fields. -/
def kvFits (kv : KV) : Prop :=
  kv.createRev < 2 ^ 63 ∧ kv.modRev < 2 ^ 63 ∧ kv.version < 2 ^ 63 ∧
    -2 ^ 63 ≤ kv.lease ∧ kv.lease < 2 ^ 63

/-! ## Writes -/

/-- A response header the txn package builds: only the revision set (the gRPC layer fills the
rest). -/
def hdrAt (rev : Nat) : HeaderM :=
  { clusterId := 0, memberId := 0, revision := W64 rev, raftTerm := 0, leaderId := 0 }

/-- A put with an ignore flag (it needs the key's previous record). -/
def ignores (p : PutReq) : Bool := or p.ignoreValue p.ignoreLease

/-- A put that reads the key's previous record (`getPrevKV`). -/
def needsPrev (p : PutReq) : Bool := or (or p.ignoreValue p.ignoreLease) p.prevKv

/-- A put's event at the history `h`. -/
def putEvents (p : PutReq) (h : KVHist) : List Event :=
  [.put p.key (p.record (h.rev + 1) (h.store p.key))]

/-- A put's previous key-value, as `PrevKv` reports it. -/
def putPrev (p : PutReq) (h : KVHist) : Option KV :=
  if p.prevKv then (h.store p.key).map (KV.ofRec p.key) else none

/-- **`Put`'s answer** at the history `h` and the live leases `ls` (W0's `kvStep` after the gRPC
validation and the permission check). -/
def putAns (p : PutReq) (h : KVHist) (ls : Int → Option LeaseRec) : Resp :=
  match p.check h.store ls with
  | some e => .err e
  | none => .ok (.put (h.rev + 1) (putPrev p h))

/-- **`Put`'s next history.** -/
def putHist (p : PutReq) (h : KVHist) (ls : Int → Option LeaseRec) : KVHist :=
  match p.check h.store ls with
  | some _ => h
  | none => h.commit (putEvents p h)

/-- A range delete's events: the present keys `l` deleted, in key order. -/
def delEvents (l : List KV) : List Event := l.map (fun kv => .delete kv.key)

section lessor
variable [GooseExts]

/-- **Every key of the store `s` holds a live lease of `ls`, or none**: what a put with
`IgnoreLease` needs (mvcc's `Attach` of a dead lease panics: the code's own need). True of every
reached state (a revocation deletes the lease's keys, a put checks its lease). -/
def leasesLive (s : EtcdModel.Store) (ls : Lease.LessorState) : Prop :=
  ∀ (k : Key) (r : KeyRec), s k = some r → r.lease = 0 ∨ ls.leases r.lease ≠ none

/-- **The store `s` and the lessor's state `ls` agree** (3c's attachment invariant, which the
store's caller keeps: `req/go_etcd_io_etcd_server_v3_storage_mvcc.md`, "from 3c"): every key's
lease is live (or `0`) and is its `itemMap` entry (3e's `storeItems`), and each live lease's item
set is exactly its keys (`0` never live). Not a premise of txn's specs (they take `leasesLive`):
the law `attached_evsLs` says txn's writes keep it. -/
def attached (s : EtcdModel.Store) (ls : Lease.LessorState) : Prop :=
  (∀ k, ls.items k = Mvcc.storeItems s k) ∧ leasesLive s ls ∧
  (∀ (id : Int) (e : Lease.LeaseEnt), ls.leases id = some e →
    id ≠ 0 ∧ ∀ k, (ls.keys e.obj k ↔ ls.items k = id))

/-- **The lessor's state after a request's events `evs` over the store `s`**: mvcc's steps (3e's
`putLs` for each put, `delLs` for each delete), in order. -/
def evsLs : Lease.LessorState → EtcdModel.Store → List Event → Lease.LessorState
  | ls, _, [] => ls
  | ls, s, .put k r :: es => evsLs (Mvcc.putLs ls (s k).isSome k r.lease) (s.applyEvent (.put k r)) es
  | ls, s, .delete k :: es => evsLs (Mvcc.delLs ls k) (s.applyEvent (.delete k)) es

/-- **txn's writes keep the attachment invariant** (each put's lease live, as `PutReq.check`
ensures). -/
def attached_evsLs.spec : Prop := ∀ (s : EtcdModel.Store) (ls : Lease.LessorState) (evs : List Event),
  attached s ls → (∀ k r, Event.put k r ∈ evs → r.lease = 0 ∨ ls.leases r.lease ≠ none) →
  attached (s.applyEvents evs) (evsLs ls s evs)

end lessor

/-! ## Transactions -/

/-- `applyCompares` at the store `s`. -/
def cmpsHold (cmps : List EtcdModel.Compare) (s : EtcdModel.Store) : Bool := decide (∀ c ∈ cmps, c.holds s)

mutual
/-- **`checkTxn`'s verdict on one operation of the taken path**, at the read view `h` and the live
leases `ls` (a nested transaction: its branch by its comparisons at `h`). -/
def opCheck (h : KVHist) (ls : Int → Option LeaseRec) : RequestOp → Option EtcdErr
  | .range r => r.txnRevErr h
  | .put p => p.check h.store ls
  | .txn cmps succ fail =>
      if cmpsHold cmps h.store then opsCheck h ls succ else opsCheck h ls fail
  | _ => none
def opsCheck (h : KVHist) (ls : Int → Option LeaseRec) : List RequestOp → Option EtcdErr
  | [] => none
  | op :: ops =>
      match opCheck h ls op with
      | some e => some e
      | none => opsCheck h ls ops
end

mutual
/-- **`executeTxn` on one operation**, from the in-transaction store and events `st`: a range at
the transaction's current revision (`skip`: not executed, its header only), a put over the key's
in-transaction record, a delete of the range's present keys, a nested transaction's branch. -/
def execOp (h : KVHist) (skip : Bool) (st : EtcdModel.Store × List Event) :
    RequestOp → (EtcdModel.Store × List Event) × OpResp
  | .empty => (st, .empty)
  | .range r =>
      (st, .range (if st.2 = [] then h.rev else h.rev + 1)
        (if skip then { kvs := [], more := false, count := 0 }
         else rangeOut r true
           (rangeAll (if r.revision ≤ 0 then st.1 else h.storeAt r.revision.toNat) r.range)))
  | .put p =>
      let e : Event := .put p.key (p.record (h.rev + 1) (st.1 p.key))
      ((st.1.applyEvent e, st.2 ++ [e]),
        .put (if p.prevKv then (st.1 p.key).map (KV.ofRec p.key) else none))
  | .deleteRange d =>
      let l := rangeAll st.1 d.range
      ((st.1.applyEvents (delEvents l), st.2 ++ delEvents l),
        .deleteRange l.length (if d.prevKv then l else []))
  | .txn cmps succ fail =>
      let ok := cmpsHold cmps h.store
      let x := if ok then execOps h skip st succ else execOps h skip st fail
      (x.1, .txn ok x.2)
def execOps (h : KVHist) (skip : Bool) (st : EtcdModel.Store × List Event) :
    List RequestOp → (EtcdModel.Store × List Event) × List OpResp
  | [] => (st, [])
  | op :: ops =>
      let x := execOp h skip st op
      let y := execOps h skip x.1 ops
      (y.1, x.2 :: y.2)
end

mutual
/-- The comparisons' verdicts of `op`'s nested transactions at the store `s`, in `compareToPath`'s
order (each nested transaction's own, then its taken branch's). -/
def opPath (s : EtcdModel.Store) : RequestOp → List Bool
  | .txn cmps succ fail =>
      if cmpsHold cmps s then true :: opsPath s succ else false :: opsPath s fail
  | _ => []
def opsPath (s : EtcdModel.Store) : List RequestOp → List Bool
  | [] => []
  | op :: ops => opPath s op ++ opsPath s ops
end

/-- **`compareToPath(rv, t)`** at the store `s`: the transaction's verdict, then its taken branch's
nested verdicts. -/
def txnPathOf (t : TxnReq) (s : EtcdModel.Store) : List Bool :=
  opPath s (.txn t.compare t.success t.failure)

/-- **`Txn`'s run** at the history `h` (the read view; for a write, also where the writes start)
and the live leases `ls`: the comparisons, `checkTxn`'s first error on the taken path, or the
events written, the verdict and the responses. -/
def run (t : TxnReq) (h : KVHist) (ls : Int → Option LeaseRec) (skip : Bool) :
    Except EtcdErr (List Event × Bool × List OpResp) :=
  let ok := cmpsHold t.compare h.store
  let ops := if ok then t.success else t.failure
  match opsCheck h ls ops with
  | some e => .error e
  | none =>
      let x := execOps h skip (h.store, []) ops
      .ok (x.1.2, ok, x.2)

/-- **`Txn`'s events** (a failed check writes none). -/
def runEvs (t : TxnReq) (h : KVHist) (ls : Int → Option LeaseRec) : List Event :=
  match run t h ls false with
  | .ok x => x.1
  | .error _ => []

/-- The response header's revision of a run that wrote `evs`. -/
def runRev (h : KVHist) (evs : List Event) : Nat := if evs = [] then h.rev else h.rev + 1

/-- **The run is W0's `TxnRun`** (for a valid transaction: the gRPC layer's checks), so `Txn`'s
answer is `kvStep`'s; and the events do not depend on `skip`. -/
def run_txnRun.spec : Prop := ∀ (t : TxnReq) (h : KVHist) (ls : Int → Option LeaseRec),
  t.valid →
  let ops := if cmpsHold t.compare h.store then t.success else t.failure
  (∀ e, run t h ls false = .error e →
      TxnRun h h.store ls (h.rev + 1) ops (h.store, []) (.error e)) ∧
  (∀ evs ok rs, run t h ls false = .ok (evs, ok, rs) →
      ok = cmpsHold t.compare h.store ∧
      ∃ s', TxnRun h h.store ls (h.rev + 1) ops (h.store, []) (.ok (s', evs, rs))) ∧
  (∀ skip, (run t h ls skip).map (fun x => x.1) = (run t h ls false).map (fun x => x.1))

/-- A read-only transaction writes nothing. -/
def runEvs_readonly.spec : Prop := ∀ (t : TxnReq) (h : KVHist) (ls : Int → Option LeaseRec),
  t.readonly → runEvs t h ls = [] ∧ ∀ skip x, run t h ls skip = .ok x → x.1 = []

mutual
/-- The keys of the puts with an ignore flag on the path taken at the read store `s` (each nested
transaction's branch by its verdict at `s`). -/
def opIgnTaken (s : EtcdModel.Store) : RequestOp → List Key
  | .put p => if ignores p then [p.key] else []
  | .txn cmps succ fail => if cmpsHold cmps s then opsIgnTaken s succ else opsIgnTaken s fail
  | _ => []
def opsIgnTaken (s : EtcdModel.Store) : List RequestOp → List Key
  | [] => []
  | op :: ops => opIgnTaken s op ++ opsIgnTaken s ops
end

mutual
/-- The keys of the puts with an ignore flag of `op` (both branches, nested ones included). -/
def opIgnKeys : RequestOp → List Key
  | .put p => if ignores p then [p.key] else []
  | .txn _ succ fail => opsIgnKeys succ ++ opsIgnKeys fail
  | _ => []
def opsIgnKeys : List RequestOp → List Key
  | [] => []
  | op :: ops => opIgnKeys op ++ opsIgnKeys ops
end

mutual
/-- The ranges the deletes of `op` may delete (both branches, nested ones included). -/
def opDelRanges : RequestOp → List KeyRange
  | .deleteRange d => [d.range]
  | .txn _ succ fail => opsDelRanges succ ++ opsDelRanges fail
  | _ => []
def opsDelRanges : List RequestOp → List KeyRange
  | [] => []
  | op :: ops => opDelRanges op ++ opsDelRanges ops
end

mutual
/-- **`op` runs without a panic**: no empty operation (`newTxnResp` leaves its response `nil`,
`executeTxn` dereferences it), a known sort target, and no put with an ignore flag after a delete
that may cover its key (`issues/etcd-txn-delete-then-ignore-put.md`: `put` reads `KVs[0]` of an
empty result), at any depth, in both branches. -/
def opSafe : RequestOp → Prop
  | .empty => False
  | .range r => targetOk r
  | .put _ => True
  | .deleteRange _ => True
  | .txn _ succ fail => opsSafe succ ∧ opsSafe fail
def opsSafe : List RequestOp → Prop
  | [] => True
  | op :: ops => opSafe op ∧ opsSafe ops ∧
      ∀ rg ∈ opDelRanges op, ∀ k ∈ opsIgnKeys ops, ¬ rg.mem k
end

/-- **A state-free sufficient condition for `Txn` to run without a panic** (both branches
`opsSafe`): stricter than the code's need, which is about the taken path at the read state only
(no empty operation and a known sort target on it, each ignore-put's key present in the
in-transaction store when it runs: `executeTxn.spec`'s premise, the margin). The gRPC layer's
checks give it (2a's law: `checkTxnRequest` and `checkIntervals`, with the fork's fix of
`issues/etcd-txn-delete-then-ignore-put.md`). -/
def txnSafe (t : TxnReq) : Prop := opsSafe t.success ∧ opsSafe t.failure

/-! ## An open mvcc transaction's view (over 3e's `MTxn`) -/

/-- The transaction `txn` works on: a write one begun at `σ` with the events `pend`, or a read one
(`.read σ`: also the read-only wrapper, 3e's `mvccTxn_readOnly`). -/
def txnK (w : Bool) (σ : Mvcc.MvccState) (pend : List Event) : Mvcc.MTxn :=
  if w then .write σ pend else .read σ

/-- A transaction's current revision (`RangeResult.Rev`): one more once it wrote. -/
def viewRev (k : Mvcc.MTxn) : Nat := k.readHist.rev

/-- The store a transaction's range at revision `rev` reads (the current one at `rev ≤ 0`). -/
def viewStore (k : Mvcc.MTxn) (rev : Int) : EtcdModel.Store :=
  k.readHist.storeAt (if rev ≤ 0 then k.readHist.rev else rev.toNat)

/-- The error of a transaction's range at revision `rev` (3e's `rangeOut`: above the current
revision `ErrFutureRev`, below the store's compaction `ErrCompacted`). -/
def viewErr (k : Mvcc.MTxn) (rev : Int) : Option EtcdErr :=
  if (k.readHist.rev : Int) < rev then some .futureRev
  else if (if rev ≤ 0 then (k.readHist.rev : Int) else rev) < k.state.crev then some .compacted
  else none

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-! ## Errors and traces -/

/-- **`err` is the Go value the package returns for W0's error `e`**: the value of the sentinel's
package variable (mvcc's `ErrCompacted`/`ErrFutureRev`, lease's `ErrLeaseNotFound`,
etcdserver/errors' `ErrKeyNotFound`; read-only after the packages' initialization), so a caller's
`err == mvcc.ErrCompacted` or `errors.Is` evaluates; `False` for any other error. -/
def errIs (err : GoInterface) : EtcdErr → IProp GF
  | .compacted => iprop(globalAddr go_etcd_io.etcd.server.v3.storage.mvcc.ErrCompacted ↦□ err)
  | .futureRev => iprop(globalAddr go_etcd_io.etcd.server.v3.storage.mvcc.ErrFutureRev ↦□ err)
  | .leaseNotFound => iprop(globalAddr go_etcd_io.etcd.server.v3.lease.ErrLeaseNotFound ↦□ err)
  | .keyNotFound => iprop(globalAddr go_etcd_io.etcd.server.v3.etcdserver.errors.ErrKeyNotFound ↦□ err)
  | _ => iprop(False)

/-- **`err` is mvcc's range error after its context was done** (`fmt.Errorf("rangeKeys: context
cancelled: %w", …)`, wrapped again by `executeTxn`): persistent. -/
opaque ctxErr [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (err : GoInterface) : IProp GF := iprop(True)

/-- (provisional, 3h's) **`s` is a `fmt.Stringer` whose `String()` returns** (persistent): a request
message (protobuf's `String`), `pb.NewLoggableTxnRequest`'s, `*pb.InternalRaftStringer` of a request. -/
opaque stringerOk [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (s : GoInterface) : IProp GF := iprop(True)

/-- With the packages initialized, the sentinels are non-`nil` and distinct (each an `errors.New`
pointer with its own message: the owners' `init` laws, 3e's `Mvcc.init`). -/
def errIs_ne_nil.spec : Prop := ∀ err e,
  isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ errIs err e ⊢
    ⌜err ≠ GoInterface.nil⌝
/-- One value, one error. -/
def errIs_agree.spec : Prop := ∀ err e e',
  isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ errIs err e ∗
    errIs err e' ⊢ ⌜e = e'⌝
def ctxErr_persistent.spec : Prop := ∀ err, Persistent (ctxErr (GF := GF) err)
def ctxErr_ne_nil.spec : Prop := ∀ err, ctxErr (GF := GF) err ⊢ ⌜err ≠ GoInterface.nil⌝
/-- A context's error is none of the sentinels (a fresh value). -/
def ctxErr_not_errIs.spec : Prop := ∀ err e,
  isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ ctxErr err ∗
    errIs err e ⊢ False
def stringerOk_persistent.spec : Prop := ∀ s, Persistent (stringerOk (GF := GF) s)

/-- **The response tree `newTxnResp` allocates** for the operations `ops` of a transaction whose
verdict is `ok` (nested transactions' branches by their verdicts at `s`): a `*TxnResponse` with an
empty header, `Succeeded` `ok`, one `ResponseOp` per operation whose `Response` oneof has the
operation's kind and an unset (`nil`) message, a nested transaction's its own tree (owned).
Internal to the package (`newTxnResp` makes it, `executeTxn` fills it). -/
opaque respSkel [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (resp : Loc) (s : EtcdModel.Store) (ok : Bool) (ops : List RequestOp) : IProp GF :=
  iprop(True)

/-- **A read-only transaction's response, possibly partly filled** (owned): a `*TxnResponse` whose
`Responses` are range responses, each `nil` or a range reply (`executeTxn` stopped at a context's
error). What `WarnOfExpensiveReadOnlyTxnRequest` reads. -/
opaque roTxnResp [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (resp : Loc) : IProp GF := iprop(True)

/-- **A `proto.Message` value `msg` the warning functions may size**: `nil` (or a typed `nil`
pointer), or a message holding `c` at the fraction `dq` (`o = some (dq, c)`), nested less than
protobuf's limit. -/
def msgOpt (msg : GoInterface) : Option (DFrac × Proto.Content) → IProp GF
  | none => iprop(⌜msg = GoInterface.nil ∨ ∃ t : go.GoType, msg = Proto.msgVal t null⌝)
  | some (dq, c) => iprop(∃ (t : go.GoType) (p : Loc), ⌜msg = Proto.msgVal t p ∧ Proto.depth c < Proto.depthMax⌝ ∗
      Proto.msgAt t p dq c)

/-! ## The writer's resources and the request's trace (over 3e's and 4b's vocabulary) -/

/-- **What a write transaction needs of its caller beside the storage's share** (3e's `KV.Write`):
the storage's post-lock hook `f` (the server's: it sets the consistent index), run once under the
batch lock from `Pre` to `Q'`, and the caller's way from `Q'` back to the lock's invariant `Pk` and
its own `Post`. The caller gets `Post` once the write transaction ended; this, unused, when the
request failed before opening one. -/
def txnWriter (B : Mvcc.MvccStorage) (Pk Post : IProp GF) : IProp GF :=
  iprop(∃ (Pre Q' : IProp GF) (f : GoFunc), Mvcc.hookIs B f ∗ Pre ∗ Mvcc.hookRun B Pk f Pre Q' ∗
    (Q' ={⊤}=∗ Pk ∗ Post))

/-- **The caller's part of its context's trace** (4b's `ctxTraceIs ctx o`): with a non-empty trace
`t0` in the context (which `EnsureTrace` keeps), its ownership. -/
def ctxTraceOwn (o : Option Loc) : IProp GF :=
  match o with
  | some t0 => iprop(∃ e : Bool, TraceUtil.traceEmpty t0 e ∗ if e then iprop(True) else TraceUtil.traceOwn t0)
  | none => iprop(True)

/-- **The trace a request returns, the caller's**: the context's (non-empty) one, or a fresh one. -/
def traceBack (o : Option Loc) (tr : Loc) : IProp GF :=
  iprop(TraceUtil.traceOwn tr ∗
    match o with
    | some t0 => iprop(⌜tr = t0⌝ ∨ TraceUtil.traceEmpty t0 true)
    | none => iprop(True))

/-! ## The replies (over W0's `Wire.lean`) -/

/-- **A range's reply** at header revision `rev` answering `a` (owned, the header's other fields
`0`). -/
def rangeOk (resp : Loc) (rev : Nat) (a : RangeAns) : IProp GF :=
  iprop(∃ m : RangeRespM, rangeRespOwn resp (DFrac.own 1) m ∗
    ⌜m.hdr = some (hdrAt rev) ∧ m.ofAns a⌝)

/-- **A put's reply** at header revision `rev`, previous key-value `prev`. -/
def putOk (resp : Loc) (rev : Nat) (prev : Option KV) : IProp GF :=
  putRespOwn resp (DFrac.own 1) { hdr := hdrAt rev, prevKv := prev.map KeyValueM.ofKV }

/-- **A delete's reply** at header revision `rev`: `n` deleted, the previous key-values `l`. -/
def delOk (resp : Loc) (rev : Nat) (n : Nat) (l : List KV) : IProp GF :=
  deleteRespOwn resp (DFrac.own 1)
    { hdr := hdrAt rev, deleted := W64 n, prevKvs := l.map KeyValueM.ofKV }

/-- **A transaction's reply** at header revision `rev`, verdict `ok`, responses `rs`. -/
def txnOk (resp : Loc) (rev : Nat) (ok : Bool) (rs : List OpResp) : IProp GF :=
  iprop(∃ m : TxnRespM, txnRespOwn resp (DFrac.own 1) m ∗ ⌜m.hdr = hdrAt rev ∧ m.ofResps ok rs⌝)

/-- **mvcc's `*RangeResult` at `rr`**, owned: its key-values `kvs` (each owned, its numbers fitting),
its `Rev` and `Count`. -/
def rrOwn (rr : Loc) (kvs : List KV) (rev : Nat) (count : Nat) : IProp GF :=
  iprop(∃ sl : GoSlice,
    rr.[go_etcd_io.etcd.server.v3.storage.mvcc.RangeResult, go!"KVs"] ↦ sl ∗
    msgsOwn keyValueOwn sl (DFrac.own 1) (kvs.map KeyValueM.ofKV) ∗
    rr.[go_etcd_io.etcd.server.v3.storage.mvcc.RangeResult, go!"Rev"] ↦ W64 rev ∗
    rr.[go_etcd_io.etcd.server.v3.storage.mvcc.RangeResult, go!"Count"] ↦ W64 count ∗
    ⌜∀ kv ∈ kvs, kvFits kv⌝)

end res

end Txn
end EtcdGrove
end Perennial
