/-
# etcd's server transactions (batch 3b): `server/v3/etcdserver/txn`, the vocabulary

`Range`, `Count`, `Put`, `DeleteRange` and `Txn` run one request over a member's mvcc store (and,
for a put, its lessor): the apply thread (3a's `applierV3backend`, every member, for a committed
write) and the request path (2c: `EtcdServer.Range`, `RangeStream`, a read-only `Txn`) call them.
This file is the vocabulary their specs share.

## The shape, in words

**The state a request acts on** is the member store's **history** `h : KVHist` (W0's: the events of
every revision and the compaction revision), held in mvcc's client-owned `mvccState γ h` (3e's), and
for a write that puts, the live leases `ls` of the store's lessor (pinned by the caller,
`leasesPin γ ls`, 3c's).

* **A read** (`Range`, `Count`, a read-only `Txn`) takes the caller's atomic update over
  `mvccState`, the state unchanged, fired once when mvcc's read transaction begins (`kv.Read`: the
  store's revision and compaction are fixed for the transaction); the answer is computed from that
  state. Concurrent writers are allowed (the request path's reads run beside the apply thread).
* **A write** (`Put`, `DeleteRange`, a `Txn` that is not read-only) is the store's **sole writer**:
  its update is **pinned** at the history `h` it begins at (`AU <{ mvccState γ h }> …`: the caller
  asserts the state is `h` whenever the update is opened, which the apply thread can, being the only
  writer; `Txn` reads the store, checks, then writes in two mvcc transactions and relies on no write
  in between, `txn.go:60-63`). It fires once, at the write transaction's `End` (or at the check that
  fails), moving `h` to the model's next history.

**The answers are functions of the state** (`putAns`, `rangeOut`, `run`): `Txn.goSort` names the
permutation Go's `sort.Sort` (pdqsort, deterministic: its pivot "randomness" is seeded by the
length) produces, so a range's answer is unique although the model's `RangeReq.answers` allows any
order among ties. This is what 2d's commit-time answers (`applyStep_fun`) and 2c's read registry
need. The laws `rangeOut_answers`, `run_txnRun` relate each to W0's relations (`RangeReq.answers`,
`TxnRun`), so 2c/3a reach W0's `kvStep` without unfolding.

**Errors** are the Go values the package returns: `errIs err e` (mvcc's `ErrCompacted` and
`ErrFutureRev`, lease's `ErrLeaseNotFound`, etcdserver/errors' `ErrKeyNotFound`, for W0's `e`), and a
context's error inside mvcc's range (`ctxErr err`, only when the context is done).

## Vocabulary

Pure (transparent): `targetOk`, `rangeLimitZ`, `sortOut`, `assemble`, `rangeOut`, `rangeAll`,
`hdrAt`, `putEvents`, `putPrev`, `putAns`, `putHist`, `delEvents`, `cmpsHold`, `opCheck`/`opsCheck`,
`execOp`/`execOps`, `run`, `runHist`, `runRev`, `opSafe`/`opsSafe`, `txnSafe`, `leasesLive`,
`kvFits`, `viewRev`, `viewStore`, `viewErr`, `TxKind`. Pure (opaque): `goSort` (Go's sort, law
`goSort_sorted`).

Resources (opaque): `errIs err e`, `ctxErr err` (persistent); `traceAt tr` (persistent, 4b's,
provisional). The reply predicates `rangeOk`, `putOk`, `delOk`, `txnOk` (transparent, over W0's
`Wire.lean` ownership) and `rrOwn` (mvcc's `*RangeResult`, owned, transparent).

**Provisional, the callees' slots** (to be replaced by their names at integration;
`notes/specs-only/req/go_etcd_io_etcd_server_v3_storage_mvcc.md`, `..._lease.md`, "from 3b"):

* 3e: `MvccName`, `mvccN`; `mvccKV kv γ` (persistent: `kv` is a store, an `mvcc.KV` interface value:
  `*store` or `*watchableStore`); `mvccState γ h` (the store's history, client-owned, exclusive);
  `mvccWriter γ` (exclusive: what mvcc's `Write` needs of its caller and gives back at `End`: the
  backend's share, the post-lock hook's contract that sets the consistent index); `mvccTxn tx γ k h
  evs` (exclusive: an open transaction of kind `k` begun at `h`, its pending events `evs`).
* 3c: `lessorAt le γ` (persistent: `le` is the `lease.Lessor` the store `γ` attaches keys to);
  `leasesPin γ ls` (exclusive: the lessor's live leases are `ls` while held).
* 3h: `stringerOk s` (persistent: a `fmt.Stringer` whose `String()` returns).

## Intended realization

txn allocates no ghost state and keeps no invariant: each entry point passes the caller's update to
mvcc's transaction contracts (3e: `Read`'s update fired at the begin, `End`'s at the commit), reads
the lessor through `Lookup` (3c, at the pin), and builds the reply. `goSort` is realized by a
functional model of Go's `sort.Sort` (a Perennial change: its spec today gives a sorted
permutation, not which one; `batch-3b.md`). `errIs` by the owners' package initializations (each
sentinel is an `errors.New` value, a distinct pointer), `ctxErr` by `fmt.Errorf`'s fresh value.

## Laws

`goSort_sorted`, `rangeAll_eq`, `rangeOut_answers`, `run_txnRun`, `runHist_readonly`,
`errIs_persistent`, `errIs_ne_nil`, `errIs_agree`, `ctxErr_persistent`, `ctxErr_ne_nil`,
`ctxErr_not_errIs`, `traceAt_persistent`, `mvccKV_persistent`, `lessorAt_persistent`,
`mvccState_excl`.

## Requirement snippets

`examples/specreq/txn/`: `read.go` (a range at the store's revision, a pinned revision and its
compaction error, a count, the paging of `RangeStream`, a read-only txn), `write.go` (the apply's
put, delete and write txn as one sole writer: a put then a range sees it, a CAS txn, the
`IgnoreValue` put, the lease check, the response's header revision), `helpers.go`
(`IsTxnReadonly`, `IsTxnSerializable`, `IsDefaultOrdering`, `HasRevisionFilters` as 2a and 2c use
them).
-/
module

public import Spec.go_etcd_io.etcd.api.v3.Wire
public import Spec.context.Api
public import Spec.go_uber_org.zap.Api
public import Spec.google_golang_org.protobuf.proto.Api
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
counting there). -/
def rangeOut (r : RangeReq) (wtc : Bool) (all : List KV) : RangeAns :=
  if r.countOnly then { kvs := [], more := false, count := all.length }
  else
    let L := r.pushdownLimit
    let fetched := if L = 0 then all else all.take L
    let fetched := if r.fastKeysOnly then fetched.map (fun kv => { kv with lease := 0 }) else fetched
    let a := assemble r (sortOut r (fetched.filter r.keeps))
    { kvs := a.1, more := a.2,
      count := if wtc ∨ L = 0 then all.length else min all.length L }

/-- `Count`'s request: a count-only range of `[key, rangeEnd)` at revision `rev`. -/
def countReq (key rangeEnd : Key) (rev : Int) : RangeReq :=
  { key := key, rangeEnd := rangeEnd, limit := 0, revision := rev, sortOrder := 0, sortTarget := 0,
    serializable := false, keysOnly := false, countOnly := true, minModRevision := 0,
    maxModRevision := 0, minCreateRevision := 0, maxCreateRevision := 0 }

/-- The present keys of `s` in `rg`, in key order (the unique such list; `[]` if none exists, which
no store of a reached history is). -/
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

/-- **Every key of the store holds a live lease, or none** (`0`): what a put with `IgnoreLease`
needs (mvcc's `Attach` of a dead lease panics). True of every reached state (a revocation deletes
the lease's keys, a put checks its lease). -/
def leasesLive (s : EtcdModel.Store) (ls : Int → Option LeaseRec) : Prop :=
  ∀ (k : Key) (r : KeyRec), s k = some r → r.lease = 0 ∨ ls r.lease ≠ none

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

/-- **`Txn`'s next history** (a failed check writes nothing). -/
def runHist (t : TxnReq) (h : KVHist) (ls : Int → Option LeaseRec) : KVHist :=
  match run t h ls false with
  | .ok x => h.commit x.1
  | .error _ => h

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
def runHist_readonly.spec : Prop := ∀ (t : TxnReq) (h : KVHist) (ls : Int → Option LeaseRec),
  t.readonly → runHist t h ls = h ∧ ∀ skip x, run t h ls skip = .ok x → x.1 = []

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

/-- **A transaction `Txn` runs without a panic** at every state (both branches `opsSafe`). The gRPC
layer's checks give it (2a's law: `checkTxnRequest` and `checkIntervals`, with the fork's fix of
`issues/etcd-txn-delete-then-ignore-put.md`). -/
def txnSafe (t : TxnReq) : Prop := opsSafe t.success ∧ opsSafe t.failure

/-! ## An open mvcc transaction's view (3e's, provisional) -/

/-- An mvcc transaction's kind: a read transaction (`kv.Read`), the read-only wrapper over one
(`NewReadOnlyTxnWrite`: a `TxnWrite` whose `Put`/`DeleteRange` panic), a write transaction
(`kv.Write`). -/
inductive TxKind where
  | read
  | roWrite
  | write

/-- A transaction's current revision (`Range`'s `Rev`): one more once it wrote. -/
def viewRev (h : KVHist) (evs : List Event) : Nat := if evs = [] then h.rev else h.rev + 1

/-- The store a transaction's range at revision `rev` reads: its pending store at `rev ≤ 0` or
above the begin revision, else the history's. -/
def viewStore (h : KVHist) (evs : List Event) (rev : Int) : EtcdModel.Store :=
  if rev ≤ 0 ∨ (h.rev : Int) < rev then h.store.applyEvents evs else h.storeAt rev.toNat

/-- The error of a transaction's range at revision `rev` (mvcc's `rangeKeys`). -/
def viewErr (h : KVHist) (evs : List Event) (rev : Int) : Option EtcdErr :=
  if (viewRev h evs : Int) < rev then some .futureRev
  else if 0 < rev ∧ rev < (h.compacted : Int) then some .compacted
  else none

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-! ## Errors and traces -/

/-- **`err` is the Go value the package returns for W0's error `e`** (persistent): mvcc's
`ErrCompacted`/`ErrFutureRev`, lease's `ErrLeaseNotFound`, etcdserver/errors' `ErrKeyNotFound`. -/
opaque errIs (err : GoInterface) (e : EtcdErr) : IProp GF := iprop(True)

/-- **`err` is mvcc's range error after its context was done** (`fmt.Errorf("rangeKeys: context
cancelled: %w", …)`, wrapped again by `executeTxn`): persistent. -/
opaque ctxErr (err : GoInterface) : IProp GF := iprop(True)

/-- (provisional, 4b's; `EtcdServer.traceAt`) **`tr` is a trace** (`*traceutil.Trace`, possibly
`nil`): its methods are safe to call. -/
opaque traceAt (tr : Loc) : IProp GF := iprop(True)

/-- (provisional, 3h's) **`s` is a `fmt.Stringer` whose `String()` returns** (persistent): a request
message (protobuf's `String`), `pb.NewLoggableTxnRequest`'s, `*pb.InternalRaftStringer` of a request. -/
opaque stringerOk (s : GoInterface) : IProp GF := iprop(True)

def errIs_persistent.spec : Prop := ∀ err e, Persistent (errIs (GF := GF) err e)
def errIs_ne_nil.spec : Prop := ∀ err e, errIs (GF := GF) err e ⊢ ⌜err ≠ GoInterface.nil⌝
/-- One value, one error (distinct sentinels are distinct `errors.New` pointers). -/
def errIs_agree.spec : Prop := ∀ err e e', errIs (GF := GF) err e ∗ errIs err e' ⊢ ⌜e = e'⌝
def ctxErr_persistent.spec : Prop := ∀ err, Persistent (ctxErr (GF := GF) err)
def ctxErr_ne_nil.spec : Prop := ∀ err, ctxErr (GF := GF) err ⊢ ⌜err ≠ GoInterface.nil⌝
/-- A context's error is none of the sentinels (a fresh value). -/
def ctxErr_not_errIs.spec : Prop := ∀ err e, ctxErr (GF := GF) err ∗ errIs err e ⊢ False
def traceAt_persistent.spec : Prop := ∀ tr, Persistent (traceAt (GF := GF) tr)
def stringerOk_persistent.spec : Prop := ∀ s, Persistent (stringerOk (GF := GF) s)

/-- **The response tree `newTxnResp` allocates** for the operations `ops` of a transaction whose
verdict is `ok` (nested transactions' branches by their verdicts at `s`): a `*TxnResponse` with an
empty header, `Succeeded` `ok`, one `ResponseOp` per operation whose `Response` oneof has the
operation's kind and an unset (`nil`) message, a nested transaction's its own tree (owned).
Internal to the package (`newTxnResp` makes it, `executeTxn` fills it). -/
opaque respSkel (resp : Loc) (s : EtcdModel.Store) (ok : Bool) (ops : List RequestOp) : IProp GF :=
  iprop(True)

/-- **A read-only transaction's response, possibly partly filled** (owned): a `*TxnResponse` whose
`Responses` are range responses, each `nil` or a range reply (`executeTxn` stopped at a context's
error). What `WarnOfExpensiveReadOnlyTxnRequest` reads. -/
opaque roTxnResp (resp : Loc) : IProp GF := iprop(True)

/-- **A `proto.Message` value `msg` the warning functions may size**: `nil` (or a typed `nil`
pointer), or a message holding `c` at the fraction `dq` (`o = some (dq, c)`), nested less than
protobuf's limit. -/
def msgOpt (msg : GoInterface) : Option (DFrac × Proto.Content) → IProp GF
  | none => iprop(⌜msg = GoInterface.nil ∨ ∃ t : go.GoType, msg = Proto.msgVal t null⌝)
  | some (dq, c) => iprop(∃ (t : go.GoType) (p : Loc), ⌜msg = Proto.msgVal t p ∧ Proto.depth c < Proto.depthMax⌝ ∗
      Proto.msgAt t p dq c)

/-! ## The callees' slots (3e's and 3c's, provisional) -/

/-- (provisional, 3e's) A store's ghost names. -/
opaque MvccName : Type := Unit

/-- (provisional, 3e's) The namespace of mvcc's invariants (the masks of the updates it takes). -/
def mvccN : Namespace := nroot .@ "mvcc"

/-- (provisional, 3e's) **`kv` is the store `γ`** (an `mvcc.KV` interface value; persistent). -/
opaque mvccKV (kv : GoInterface) (γ : MvccName) : IProp GF := iprop(True)

/-- (provisional, 3e's) **The store `γ`'s history is `h`** (client-owned, exclusive). -/
opaque mvccState (γ : MvccName) (h : KVHist) : IProp GF := iprop(True)

/-- (provisional, 3e's) **The right to open a write transaction on `γ`** (exclusive; what `Write`
takes and `End` gives back: the backend's share, the post-lock hook's contract). -/
opaque mvccWriter (γ : MvccName) : IProp GF := iprop(True)

/-- (provisional, 3e's) **An open transaction `tx` on `γ`** of kind `k`, begun at the history `h`,
with the pending events `evs` (`[]` but for a write). Exclusive; `End` consumes it. -/
opaque mvccTxn (tx : GoInterface) (γ : MvccName) (k : TxKind) (h : KVHist) (evs : List Event) :
  IProp GF := iprop(True)

/-- (provisional, 3c's) **`le` is the lessor the store `γ` attaches keys to** (a `lease.Lessor`
interface value; persistent). -/
opaque lessorAt (le : GoInterface) (γ : MvccName) : IProp GF := iprop(True)

/-- (provisional, 3c's) **The live leases of `γ`'s lessor are `ls`**, and stay so while this is held
(exclusive: the apply thread's pin; grants and revocations are its own). -/
opaque leasesPin (γ : MvccName) (ls : Int → Option LeaseRec) : IProp GF := iprop(True)

def mvccKV_persistent.spec : Prop := ∀ kv γ, Persistent (mvccKV (GF := GF) kv γ)
def lessorAt_persistent.spec : Prop := ∀ le γ, Persistent (lessorAt (GF := GF) le γ)
def mvccState_excl.spec : Prop := ∀ γ h h', mvccState (GF := GF) γ h ∗ mvccState γ h' ⊢ False

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
