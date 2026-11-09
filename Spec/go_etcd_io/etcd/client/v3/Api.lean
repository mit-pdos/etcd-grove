/-
# etcd's Go client: the vocabulary (batch W0, the anchor)

What a program using `go.etcd.io/etcd/client/v3` holds, and the contracts the client's KV methods
meet, over the cluster's abstract state (`api/v3/State.lean`'s `etcdState γ σ`, `Model.lean`'s
`State` and `Step`). The specs of this package's functions are in the files next to this one; the
watch (1b), lease, auth, cluster and maintenance (1c) batches spec theirs against the slots below.

## The shape of every KV spec

A call to the cluster `γ` by a client whose own credentials name `who` (its default principal)
(a read also takes `authLb γ lo`, the auth state's index at its start, and its step is
`Step p rq σ σ' res lo`: its permission is checked at an auth state from `lo` on),
with a context `ctx` under which the server authenticates the request as `p` (`ctxPrin who ctx p`:
the principal is per call), sending the request `rq` (`Model.lean`'s `Req`), takes the caller's
atomic update (with `Step p rq ...`)

    AU <{ ∃∃ σ, etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
       <{ ∀∀ σ' res, ⌜Step p rq σ σ' res⌝ ∗ etcdState γ σ', COMM Q σ σ' res }>

**persistent** (`□`) for a read (`Req.isRead`: a range, a read-only transaction: the cluster may
fire it at every committed state from the read's registration on, and answers with the `Q` of the
firing at the state the member read; a read may be retried) and **exclusive** otherwise (a write
takes effect at most once: the retry interceptor resends a mutable RPC only after an attempt that
was never sent, was refused before the handler (a learner's `ErrGRPCNotSupportedForLearner`), or
was refused without effect (a stale or invalid token); the cluster applies an entry once), and
returns either

* `Q σ σ' res` with the reply that `res` is (`getReply`, `putReply`, ...: a message whose model is
  the answer, or `err = errVal e` for an answer `.err e`), the request **linearized** at `σ` with
  the answer `res` (a refusal is such an answer: the request will never take effect); or
* nothing but `indefCall err` (persistent: `callErr err k` of an indefinite kind; `indefCall_pure`
  gives `indefErr err`: not a definite etcd error): an error that settles nothing (a timeout, the
  leader lost, the context done, a transport error). The request may take effect later, the update
  fired then.


There is no other case: in particular a definite error (`ErrCompacted`, `ErrLeaseNotFound`,
`ErrPermissionDenied`, `ErrTooManyRequests`, ...) is always a linearized answer. Which errors are
which is `EtcdErr.indefinite` (`Model.lean`).

## Handles (all persistent)

* `connOk conn γ who` (**slot, 1c**): `conn` is the `*grpc.ClientConn` an etcd client dialed to
  members of the cluster `γ`, with the client's interceptors (the retry interceptor, the auth token
  of `who`). Realized by 1c (`Client.dial`, the interceptors) over grpc's boundary (2a).
* `callOptsOk sl rep` (**slot, 1c**): `sl` is a read-only slice of gRPC call options that write no
  caller memory: the client's (`Client.callOpts`: wait-for-ready, message size limits) and, if
  `rep`, the retry interceptor's repeatable policy (`withRepeatablePolicy()`). A mutable RPC is
  sent with `rep = false` only.
* `clientConnOk c γ who` (**slot, 1c**): the `*Client` `c` under construction has its `conn`
  (`connOk`) and `callOpts` (`callOptsOk _ false`) set, read-only: what `NewKV(c)` and the other
  member constructors read.
* `isClient c γ who`: the client `c` (`clientv3.New`'s result, frozen): `clientConnOk`, and its
  `KV` field holds a `kvAt` value for good, its `Watcher`, `Lease`, `Auth`, `Cluster`,
  `Maintenance` fields values meeting their slots (`watcherAt` 1b, `leaseAt`, `authAt`, `clusterAt`,
  `maintAt` 1c). `clientMut c γ who` (exclusive) is the same with the six interface fields
  writable (a caller that wraps `c.KV`, as Kubernetes' storage factory does), `clientMut_freeze`
  makes it `isClient`.
* `kvAt v γ who`: the `KV` interface value `v` meets the KV contract (`KV.*Triple`): a bundle of
  its methods' triples (PRINCIPLES, "an interface value gets a bundle"). Realized for `*kv` by
  `kvHandle_kvAt`; a wrapper (Kubernetes' latency tracker) proves it for itself. Leasing's KV
  does not meet it (its cached reads answer with a stale header): it has a contract of its own (1e).
* `kvHandle kv γ who`: a `*kv` (`NewKV`'s): its `remote` a `remoteKVAt` value, its `callOpts`
  the client's.
* `remoteKVAt v γ who` (**the gRPC boundary**): the `etcdserverpb.KVClient` value `v` meets the
  wire-level contract (`RemoteKV.*Triple`): the same atomic updates, over request and reply
  messages (`api/v3/Wire.lean`), and the errors as gRPC returns them (`callErr`). What grpc, the
  generated stub and the server's handlers must give together (`req/google_golang_org_grpc.md`,
  `req/go_etcd_io_etcd_server_v3_etcdserver_api_v3rpc.md`). Realized for `*retryKVClient` by
  `retryKVHandle_remoteKVAt`.
* `txnAt iv γ who ctx st` (exclusive): the `Txn` interface value `iv`, built over the context `ctx`,
  holds the transaction under construction `st` (`TxnSt`); `If`, `Then`, `Else`, `Commit`
  (`Txn.*Triple`). Intended realization: an existential bundle (a state predicate over `TxnSt`
  with the four triples over it), so that every `Txn` implementation shares it.

## Values (persistent)

* `opAt op o`: the `Op` struct value `op` is modelled by `o : OpM` (its fields; its byte slices, sort
  option, comparisons and nested operations read-only). `cmpAt c m`: the `Cmp` value `c` is the
  comparison `m` (`none`: a zero `Cmp`). `cmpsAt`, `opsAt`: slices of them.
* `optAt f g` (exclusive, given back by every call that runs it): the `OpOption` closure `f`
  changes an `Op` modelled by `o` into one modelled by `g o` (`WithSort`'s writes a variable it
  captured, so a closure is not shared between goroutines); `optsAt sl gs`: a read-only slice of
  them. `compactOptAt`, `leaseOptAt` the same for `CompactOption` and `LeaseOption`.
* `streamAt ch γ who r Q ms fin` (exclusive): the consumer of `GetStream`'s channel, the chunks
  received so far (`streamAt_recv`; its end gives the caller's `Q` and `streamMatches`).
  `wireStreamAt sc ...` (**slot, 2a**): the same of the gRPC stream (`wireStreamAt_recv`).
* `callErr err k` (**slot, 2a**): `err` is what a gRPC call to an etcd member returned, of kind
  `k`: `.etcd e` (a status whose message is etcd's error `e`, any of rpctypes' errors, or `errVal e`
  itself: what `rpctypes.Error` turns into `errVal e`; `ErrGRPCCanceled` and
  `ErrGRPCDeadlineExceeded` are `.etcd` of indefinite kinds), `.notSent` (status `Unavailable` with
  grpc's "there is no address available"/"there is no connection available": the request never
  left the client), or
  `.other` (any other error: not `.etcd e` for any `e`, not `nil`).

## Laws

Persistence of the handles and values; `isClient_conn`, `isClient_KV`, `clientMut_KV`,
`clientMut_freeze`; the bundles' laws (`kvAt_Put`, ..., `remoteKVAt_Range`, ..., `txnAt_If`, ...);
`kvHandle_kvAt`, `retryKVHandle_remoteKVAt`; `callErr_errVal`; the package's initial globals
(`init.spec`: `noPrefixEnd` holds `[0]`, read-only).

## Requirement snippets

`examples/specreq/clientv3kv/`: `put_get.go` (read-your-writes, a get at the reply's revision,
compaction errors), `txn.go` (compare-and-swap, the branch taken, nested transactions, the empty
read-only transaction), `ops.go` (`Op`s built with options, `Do`, the getters leasing reads),
`errors.go` (which errors settle what), `history.go` (revisions carried between calls; a revision
reached is the cluster's), `stream.go` (`GetStream`'s chunks, Kubernetes' streamed lists).
-/
module

public import GeneratedProof.go_etcd_io.etcd.client.v3
public import Spec.PkgInit.go_etcd_io.etcd.client.v3
public import Spec.go_etcd_io.etcd.api.v3.State
public import Spec.go_etcd_io.etcd.api.v3.Wire
public import Spec.context.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ClientV3

open Iris Iris.BI EtcdModel EtcdWire
open Classical

/-! ## The client's `Op` model -/

/-- `opType`'s values. -/
def tRange : w64 := W64 1
def tPut : w64 := W64 2
def tDeleteRange : w64 := W64 3
def tTxn : w64 := W64 4

/-- `SortTarget`, `SortOrder` (Go `int`s). -/
def SortByKey : w64 := W64 0
def SortByVersion : w64 := W64 1
def SortByCreateRevision : w64 := W64 2
def SortByModRevision : w64 := W64 3
def SortByValue : w64 := W64 4
def SortNone : w64 := W64 0
def SortAscend : w64 := W64 1
def SortDescend : w64 := W64 2

/-- **A `clientv3.Op`**, field by field. `rangeEnd` is `end` (`none`: `nil`); `sort` is the sort
option (`none`: `nil`) as (`Target`, `Order`); `cmps` the comparisons (`none`: a zero `Cmp`). -/
structure OpM where
  t : w64
  key : GoString
  rangeEnd : Option GoString
  limit : w64
  sort : Option (w64 × w64)
  serializable : Bool
  keysOnly : Bool
  countOnly : Bool
  minModRev : w64
  maxModRev : w64
  minCreateRev : w64
  maxCreateRev : w64
  rev : w64
  prevKV : Bool
  fragment : Bool
  watchBufLog : Bool
  ignoreValue : Bool
  ignoreLease : Bool
  progressNotify : Bool
  createdNotify : Bool
  filterPut : Bool
  filterDelete : Bool
  val : GoString
  leaseID : w64
  cmps : List (Option EtcdModel.Compare)
  thenOps : List OpM
  elseOps : List OpM
  isOptsWithFromKey : Bool
  isOptsWithPrefix : Bool

/-- The zero `Op{}`. -/
def OpM.zero : OpM :=
  { t := W64 0, key := [], rangeEnd := none, limit := W64 0, sort := none, serializable := false,
    keysOnly := false, countOnly := false, minModRev := W64 0, maxModRev := W64 0,
    minCreateRev := W64 0, maxCreateRev := W64 0, rev := W64 0, prevKV := false,
    fragment := false, watchBufLog := false, ignoreValue := false, ignoreLease := false,
    progressNotify := false, createdNotify := false, filterPut := false, filterDelete := false,
    val := [], leaseID := W64 0, cmps := [], thenOps := [], elseOps := [],
    isOptsWithFromKey := false, isOptsWithPrefix := false }

/-- `NewOp()`'s `Op` (`&Op{key: []byte("")}`): the zero one. -/
def OpM.newOp : OpM := OpM.zero

/-- `getPrefix(key)`: the first key after every key with prefix `key` (the last byte below `0xff`
incremented, the rest dropped); `"\x00"` (`noPrefixEnd`: every key) if there is none. -/
def prefixEnd (key : GoString) : GoString :=
  match key.reverse.dropWhile (fun b => b = W8 255) with
  | [] => [W8 0]
  | b :: rest => rest.reverse ++ [b + W8 1]

/-! ### The options' models -/

def withLimitM (n : w64) (o : OpM) : OpM := { o with limit := n }
def withRevM (r : w64) (o : OpM) : OpM := { o with rev := r }
/-- `WithSort`: a sort by key in ascending order is no sort (`SortNone`). -/
def withSortM (target order : w64) (o : OpM) : OpM :=
  { o with sort := some (target, if target = SortByKey ∧ order = SortAscend then SortNone else order) }
def withPrefixM (o : OpM) : OpM :=
  if o.key = [] then { o with key := [W8 0], rangeEnd := some [W8 0], isOptsWithPrefix := true }
  else { o with rangeEnd := some (prefixEnd o.key), isOptsWithPrefix := true }
def withRangeM (e : GoString) (o : OpM) : OpM := { o with rangeEnd := some e }
def withFromKeyM (o : OpM) : OpM :=
  { o with key := (if o.key = [] then [W8 0] else o.key), rangeEnd := some [W8 0],
           isOptsWithFromKey := true }
def withSerializableM (o : OpM) : OpM := { o with serializable := true }
def withKeysOnlyM (o : OpM) : OpM := { o with keysOnly := true }
def withCountOnlyM (o : OpM) : OpM := { o with countOnly := true }
def withMinModRevM (r : w64) (o : OpM) : OpM := { o with minModRev := r }
def withMaxModRevM (r : w64) (o : OpM) : OpM := { o with maxModRev := r }
def withMinCreateRevM (r : w64) (o : OpM) : OpM := { o with minCreateRev := r }
def withMaxCreateRevM (r : w64) (o : OpM) : OpM := { o with maxCreateRev := r }
def withProgressNotifyM (o : OpM) : OpM := { o with progressNotify := true }
def withCreatedNotifyM (o : OpM) : OpM := { o with createdNotify := true }
def withFilterPutM (o : OpM) : OpM := { o with filterPut := true }
def withFilterDeleteM (o : OpM) : OpM := { o with filterDelete := true }
def withPrevKVM (o : OpM) : OpM := { o with prevKV := true }
def withFragmentM (o : OpM) : OpM := { o with fragment := true }
def withWatchBufLogM (o : OpM) : OpM := { o with watchBufLog := true }
def withIgnoreValueM (o : OpM) : OpM := { o with ignoreValue := true }
def withIgnoreLeaseM (o : OpM) : OpM := { o with ignoreLease := true }
def withLeaseM (id : w64) (o : OpM) : OpM := { o with leaseID := id }
/-- `withTop(target, order)`: `WithPrefix(), WithSort(target, order), WithLimit(1)`. -/
def withTopM (target order : w64) : List (OpM → OpM) :=
  [withPrefixM, withSortM target order, withLimitM (W64 1)]

/-- The options applied in order (`applyOpts`). -/
def applyOptsM (gs : List (OpM → OpM)) (o : OpM) : OpM := gs.foldl (fun o g => g o) o

/-- `IsOptsWithPrefix(opts)`, `IsOptsWithFromKey(opts)`: the options applied to `NewOp()`. -/
def optsWithPrefix (gs : List (OpM → OpM)) : Bool := (applyOptsM gs OpM.newOp).isOptsWithPrefix
def optsWithFromKey (gs : List (OpM → OpM)) : Bool := (applyOptsM gs OpM.newOp).isOptsWithFromKey

/-! ### The `Op` constructors -/

def opGetM (key : GoString) (gs : List (OpM → OpM)) : OpM :=
  applyOptsM gs { OpM.zero with t := tRange, key := key }
def opDeleteM (key : GoString) (gs : List (OpM → OpM)) : OpM :=
  applyOptsM gs { OpM.zero with t := tDeleteRange, key := key }
def opPutM (key val : GoString) (gs : List (OpM → OpM)) : OpM :=
  applyOptsM gs { OpM.zero with t := tPut, key := key, val := val }
def opWatchM (key : GoString) (gs : List (OpM → OpM)) : OpM :=
  applyOptsM gs { OpM.zero with t := tRange, key := key }
def opTxnM (cmps : List (Option EtcdModel.Compare)) (thenOps elseOps : List OpM) : OpM :=
  { OpM.zero with t := tTxn, cmps := cmps, thenOps := thenOps, elseOps := elseOps }

/-- `OpGet` and `OpDelete` panic: `WithPrefix` and `WithFromKey` together. -/
def prefixAndFromKey (gs : List (OpM → OpM)) : Prop :=
  optsWithPrefix gs = true ∧ optsWithFromKey gs = true

/-- The fields `OpDelete`, `OpPut` and `OpWatch` reject (their `switch`). -/
def OpM.hasRangeOpts (o : OpM) : Prop :=
  o.limit ≠ W64 0 ∨ o.sort ≠ none ∨ o.serializable = true ∨ o.countOnly = true ∨
  o.minModRev ≠ W64 0 ∨ o.maxModRev ≠ W64 0 ∨ o.minCreateRev ≠ W64 0 ∨ o.maxCreateRev ≠ W64 0

/-- `OpDelete`'s `switch` panics. -/
def OpM.deletePanics (o : OpM) : Prop :=
  o.leaseID ≠ W64 0 ∨ o.hasRangeOpts ∨ o.rev ≠ W64 0 ∨ o.filterDelete = true ∨
  o.filterPut = true ∨ o.createdNotify = true

/-- `OpPut`'s `switch` may panic: also any range end set (`end != nil`; the model of a range end
does not say whether an empty one is `nil`, so every one is ruled out). -/
def OpM.putPanics (o : OpM) : Prop :=
  o.rangeEnd ≠ none ∨ o.hasRangeOpts ∨ o.rev ≠ W64 0 ∨ o.filterDelete = true ∨
  o.filterPut = true ∨ o.createdNotify = true

/-- `OpWatch`'s `switch` panics. -/
def OpM.watchPanics (o : OpM) : Prop := o.leaseID ≠ W64 0 ∨ o.hasRangeOpts

/-! ### The requests an `Op` sends -/

/-- A Go `int` (`SortOption`'s fields) converted to the `int32` of a protobuf enum. -/
def toEnum32 (x : w64) : Int := sint.Z (W32 (sint.Z x))

/-- `toRangeRequest`. -/
def OpM.rangeReq (o : OpM) : RangeReq :=
  { key := o.key, rangeEnd := o.rangeEnd.getD [], limit := sint.Z o.limit,
    revision := sint.Z o.rev,
    sortOrder := (o.sort.map (fun s => toEnum32 s.2)).getD 0,
    sortTarget := (o.sort.map (fun s => toEnum32 s.1)).getD 0,
    serializable := o.serializable, keysOnly := o.keysOnly, countOnly := o.countOnly,
    minModRevision := sint.Z o.minModRev, maxModRevision := sint.Z o.maxModRev,
    minCreateRevision := sint.Z o.minCreateRev, maxCreateRevision := sint.Z o.maxCreateRev }

/-- The `PutRequest` `Do` and `toRequestOp` build. -/
def OpM.putReq (o : OpM) : PutReq :=
  { key := o.key, value := o.val, lease := sint.Z o.leaseID, prevKv := o.prevKV,
    ignoreValue := o.ignoreValue, ignoreLease := o.ignoreLease }

/-- The `DeleteRangeRequest` `Do` and `toRequestOp` build. -/
def OpM.deleteReq (o : OpM) : DeleteReq :=
  { key := o.key, rangeEnd := o.rangeEnd.getD [], prevKv := o.prevKV }

/-- A zero `Compare` (what `GetCompare` makes of a zero `Cmp`). -/
def Compare.zero : EtcdModel.Compare :=
  { result := 0, target := 0, key := [], rangeEnd := [], targetUnion := .none }

mutual
/-- `toRequestOp` (`none`: it panics, `Unknown Op`, on an `Op` of no type, at any depth). -/
def OpM.toReqOp : OpM → Option RequestOp
  | o@{ thenOps, elseOps, .. } =>
    if o.t = tRange then some (.range o.rangeReq)
    else if o.t = tPut then some (.put o.putReq)
    else if o.t = tDeleteRange then some (.deleteRange o.deleteReq)
    else if o.t = tTxn then
      match OpM.toReqOps thenOps, OpM.toReqOps elseOps with
      | some s, some f => some (.txn (o.cmps.map (fun c => c.getD Compare.zero)) s f)
      | _, _ => none
    else none
def OpM.toReqOps : List OpM → Option (List RequestOp)
  | [] => some []
  | o :: os =>
    match OpM.toReqOp o, OpM.toReqOps os with
    | some r, some rs => some (r :: rs)
    | _, _ => none
end

/-- **The request an `Op` sends** through `Do` (`none`: `Do` panics). -/
def OpM.toReq (o : OpM) : Option Req :=
  match OpM.toReqOp o with
  | some (.range r) => some (.range r)
  | some (.put p) => some (.put p)
  | some (.deleteRange d) => some (.deleteRange d)
  | some (.txn c s f) => some (.txn { compare := c, success := s, failure := f })
  | _ => none

mutual
/-- `isWrite`: not a range (a transaction: one of its operations is a write). -/
def OpM.isWrite : OpM → Bool
  | { t, thenOps, elseOps, .. } =>
    if t = tTxn then OpM.anyWrite thenOps || OpM.anyWrite elseOps else !(decide (t = tRange))
def OpM.anyWrite : List OpM → Bool
  | [] => false
  | o :: os => OpM.isWrite o || OpM.anyWrite os
end

/-! ### Comparisons -/

/-- The value a `Compare` call compares with, as the `any` it is passed: a `string`, an `int64`,
an `int`, a `LeaseID` (`mustInt64`, `mustInt64orLeaseID`). -/
inductive CmpArg where
  | str (s : GoString)
  | i64 (n : w64)
  | int (n : w64)
  | leaseID (n : w64)

section iface
variable [GooseExts] [go_gctx : GoGlobalContext]
def CmpArg.toIface : CmpArg → GoInterface
  | .str s => interface.mkOk go.string #s
  | .i64 n => interface.mkOk go.int64 #n
  | .int n => interface.mkOk go.int #n
  | .leaseID n => interface.mkOk go_etcd_io.etcd.client.v3.LeaseID.ty #n
end iface

/-- The comparison's result string (`"="`, `"!="`, `">"`, `"<"`) as `Compare_CompareResult`. -/
def cmpResultOf (r : GoString) : Option Int :=
  if r = go!"=" then some cmpEqual
  else if r = go!"!=" then some cmpNotEqual
  else if r = go!">" then some cmpGreater
  else if r = go!"<" then some cmpLess
  else none

/-- `Compare(cmp, result, v)`'s comparison (`none`: it panics: an unknown result, a value of the
wrong type for the target, an unknown target). -/
def compareM (m : Option EtcdModel.Compare) (result : GoString) (a : CmpArg) :
    Option EtcdModel.Compare :=
  let c := m.getD Compare.zero
  match cmpResultOf result with
  | none => none
  | some r =>
    let tu : Option CmpVal :=
      if c.target = cmpTValue then (match a with | .str s => some (.value s) | _ => none)
      else
        let n : Option Int := match a with
          | .i64 n => some (sint.Z n) | .int n => some (sint.Z n)
          | .leaseID n => if c.target = cmpTLease then some (sint.Z n) else none
          | .str _ => none
        if c.target = cmpTVersion then n.map .version
        else if c.target = cmpTCreate then n.map .createRevision
        else if c.target = cmpTMod then n.map .modRevision
        else if c.target = cmpTLease then n.map .lease
        else none
    tu.map (fun tu => { c with result := r, targetUnion := tu })

/-- `Value(key)`, `Version(key)`, ... : a comparison of the target with nothing set yet. -/
def cmpOfTarget (target : Int) (key : GoString) : EtcdModel.Compare :=
  { result := 0, target := target, key := key, rangeEnd := [], targetUnion := .none }

/-! ### Transactions under construction -/

/-- **A `Txn` under construction**: which of `If`, `Then`, `Else` were called, and the comparisons
and operations so far. -/
structure TxnSt where
  cif : Bool
  cthen : Bool
  celse : Bool
  cmps : List EtcdModel.Compare
  sus : List RequestOp
  fas : List RequestOp

def TxnSt.empty : TxnSt :=
  { cif := false, cthen := false, celse := false, cmps := [], sus := [], fas := [] }

def TxnSt.req (st : TxnSt) : TxnReq := { compare := st.cmps, success := st.sus, failure := st.fas }

/-- `CompactOp`: the revision and `physical`. -/
structure CompactOpM where
  revision : w64
  physical : Bool

/-- `CallErr`: what kind of error a gRPC call to an etcd member returned (`callErr`). -/
inductive CallErr where
  | etcd (e : EtcdErr)
  | notSent
  | other

/-- An error kind that settles nothing. -/
def CallErr.indefinite : CallErr → Bool
  | .etcd e => e.indefinite
  | .notSent => true
  | .other => true

/-- **A streamed range's chunks against its answer** (`EtcdServer.RangeStream`: the chunks are
pages read at one pinned revision): only the last chunk carries a header (the answer's revision),
`More` and `Count`; every earlier chunk has key-values; at the default ordering and with no
revision filter the chunks' key-values, in order, are the answer's, and the last chunk's `More` and
`Count` are its (the server adds the count of the keys not streamed). The server refuses a custom
order or a revision filter (`Unimplemented`, an `.other` error), except a non-key target with no
order (`issues/etcd-rangestream-sort-none.md`): those contents are not modelled. -/
def streamMatches (r : RangeReq) (ms : List RangeRespM) (rev : Nat) (a : RangeAns) : Prop :=
  ∃ last, ms.getLast? = some last ∧ last.hdr.map (·.revision) = some (W64 rev) ∧
    (∀ m ∈ ms.dropLast, m.hdr = none ∧ m.more = false ∧ m.count = W64 0 ∧ m.kvs ≠ []) ∧
    (isDefaultOrdering r.sortTarget r.sortOrder ∧ ¬ r.hasRevFilters →
      (ms.map (·.kvs)).flatten = a.kvs.map KeyValueM.ofKV ∧ last.more = a.more ∧
      last.count = W64 a.count)

/-! ## Resources -/

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- **Slot (1c)**: `conn` is the client's connection to the cluster `γ` as `who`. -/
opaque connOk (conn : Loc) (γ : Cluster) (who : Principal) : IProp GF := iprop(True)
/-- **Slot (1c)**: `sl` holds gRPC call options a client may pass (`rep`: with the repeatable
policy). -/
opaque callOptsOk (sl : GoSlice) (rep : Bool) : IProp GF := iprop(True)
/-- **Slot (1c)**: the client `c` under construction has its connection and call options. -/
opaque clientConnOk (c : Loc) (γ : Cluster) (who : Principal) : IProp GF := iprop(True)

/-- **Slots (1b, 1c)**: the `Watcher`, `Lease`, `Auth`, `Cluster`, `Maintenance` interface values
of a client of `γ` as `who` meet their contracts (bundles of their methods' triples, written by
those batches). -/
opaque watcherAt (v : GoInterface) (γ : Cluster) (who : Principal) : IProp GF := iprop(True)
opaque leaseAt (v : GoInterface) (γ : Cluster) (who : Principal) : IProp GF := iprop(True)
opaque authAt (v : GoInterface) (γ : Cluster) (who : Principal) : IProp GF := iprop(True)
opaque clusterAt (v : GoInterface) (γ : Cluster) (who : Principal) : IProp GF := iprop(True)
opaque maintAt (v : GoInterface) (γ : Cluster) (who : Principal) : IProp GF := iprop(True)

/-- **The `KV` interface value `v` meets the KV contract** (`KV.*Triple`). -/
opaque kvAt (v : GoInterface) (γ : Cluster) (who : Principal) : IProp GF := iprop(True)
/-- A `*kv` of the cluster `γ` as `who`. -/
opaque kvHandle (kv : Loc) (γ : Cluster) (who : Principal) : IProp GF := iprop(True)
/-- **The `etcdserverpb.KVClient` value `v` meets the wire-level contract** (`RemoteKV.*Triple`). -/
opaque remoteKVAt (v : GoInterface) (γ : Cluster) (who : Principal) : IProp GF := iprop(True)
/-- A `*retryKVClient` of `γ` as `who`. -/
opaque retryKVHandle (rkv : Loc) (γ : Cluster) (who : Principal) : IProp GF := iprop(True)

/-- **The client `c`** of the cluster `γ` as `who` (persistent). -/
opaque isClient (c : Loc) (γ : Cluster) (who : Principal) : IProp GF := iprop(True)
/-- The client `c` with its interface fields writable (exclusive). -/
opaque clientMut (c : Loc) (γ : Cluster) (who : Principal) : IProp GF := iprop(True)
/-- The rest of a `clientMut`: everything but the `KV` field. -/
opaque clientMutRest (c : Loc) (γ : Cluster) (who : Principal) : IProp GF := iprop(True)
/-- **Everything of the client `c` but its `KV` field, for good** (persistent): its connection, call
options, context and logger, and its other interface fields (as `isClient_fields`). What a caller
holds that replaced `c.KV` by a value meeting another contract (leasing's `lkvAt`, 1e: the gRPC
proxy's `client.KV, _, _ = leasing.NewKV(client, pfx)`), and what `leasing.NewKV` reads while the
`KV` field is still writable. -/
opaque clientRest (c : Loc) (γ : Cluster) (who : Principal) : IProp GF := iprop(True)

/-- **A `Txn` under construction** (exclusive). -/
opaque txnAt (iv : GoInterface) (γ : Cluster) (who : Principal) (ctx : GoInterface) (st : TxnSt) :
  IProp GF := iprop(True)

/-- **The `Op` value `op` is modelled by `o`** (persistent). -/
opaque opAt (op : go_etcd_io.etcd.client.v3.Op) (o : OpM) : IProp GF := iprop(True)
/-- **The `Cmp` value `c` is the comparison `m`** (persistent; `none`: a zero `Cmp`). -/
opaque cmpAt (c : go_etcd_io.etcd.client.v3.Cmp) (m : Option EtcdModel.Compare) : IProp GF :=
  iprop(True)
/-- **The `OpOption` closure `f` acts as `g`** (exclusive; given back by every call running it). -/
opaque optAt (f : GoFunc) (g : OpM → OpM) : IProp GF := iprop(True)
/-- The `CompactOption` closure `f` acts as `g`. -/
opaque compactOptAt (f : GoFunc) (g : CompactOpM → CompactOpM) : IProp GF := iprop(True)
/-- The `LeaseOption` closure `f` sets `attachedKeys` as `g` does. -/
opaque leaseOptAt (f : GoFunc) (g : Bool → Bool) : IProp GF := iprop(True)

/-- **Slot (2a)**: `err` is what a gRPC call to an etcd member returned, of kind `k`. -/
opaque callErr (err : GoInterface) (k : CallErr) : IProp GF := iprop(True)

/-- **The consumer of a streamed range** (`GetStream`'s channel `ch`, exclusive): the chunks `ms`
received so far, the range `r` linearized by the caller's update with result `Q`; `fin` once the
terminal error chunk is received. Intended realization: Perennial's single-producer
single-consumer channel (`isSpsc`, `spscConsumer`) whose producer is `GetStream`'s goroutine. -/
opaque streamAt (ch : Loc) (γ : Cluster) (who : Principal) (r : RangeReq)
  (Q : State → State → Resp → IProp GF) (ms : List RangeRespM) (fin : Bool) : IProp GF := iprop(True)

/-- **The wire-level stream of a range** (`KV_RangeStreamClient` value `sc`, exclusive): the chunks
`ms` received so far (**slot, 2a**: grpc's client stream, the server's `RangeStream`). -/
opaque wireStreamAt (sc : GoInterface) (γ : Cluster) (who : Principal) (r : RangeReq)
  (Q : State → State → Resp → IProp GF) (ms : List RangeRespM) : IProp GF := iprop(True)

/-- **Slot (2a, 1b, 1c)**: the context `ctx` carries the require-leader metadata
(`WithRequireLeader`): a member with no leader refuses its requests (`ErrNoLeader`, indefinite)
and closes its watch streams. -/
opaque ctxRequireLeader (ctx : GoInterface) : IProp GF := iprop(True)

/-- **The principal of a call** (persistent): a request sent with `ctx` by a client whose own
credentials name `dflt` (`isClient c γ dflt`: its username, or none) is authenticated by the server
as `p`, or refused (an invalid or expired token: a refusal, any principal). The server takes the
principal from the request's metadata (`auth/store.go`, `AuthInfoFromCtx`: `token`, else
`authorization`, the first value); a client's own token (a per-RPC credential) comes before the
context's (grpc puts the credentials' headers first). So the principal is per call: the client's
own for a context with no token metadata (`ctxPrin_of_noMeta`), the token's user for a client
without credentials whose context forwards a token (`ctxPrin_token`: the gRPC proxy, the
in-process `v3client`, a per-request principal), the client's own when the context's token is of
the same user (`ctxPrin_tokenSame`). `p` is the principal the server uses **with auth on** (the
token's user, else the client certificate's common name); with auth off the server may use the
certificate's name (`AuthInfoFromTLS`), but no check of `Step` depends on the principal then, so a
context carrying both a token and a certificate is covered by the token's user.
Introduced for contexts with no gRPC outgoing metadata (`ctxPrin_of_noMeta` from
`Context.ctxNoMeta`, which a root context's owner discharges; `ctxPrin_background`,
`ctxPrin_todo`), kept by children (`ctxPrin_child`), by a `WithValue` at another key
(`ctxPrin_value`), by `WithRequireLeader` and `withVersion` (their specs); a context a caller builds
with grpc metadata of its own needs an introduction from grpc's `metadata` (2a). -/
opaque ctxPrin (dflt : Principal) (ctx : GoInterface) (p : Principal) : IProp GF := iprop(True)

/-- **Slot (2a)**: `ctx` carries the outgoing metadata `token: tok` (grpc's `metadata`: the gRPC
proxy's and the in-process client's forwarded tokens, `examples/etcd/auth`'s contexts). -/
opaque ctxTokenMd (ctx : GoInterface) (tok : GoString) : IProp GF := iprop(True)

/-- **An error of a call that settles nothing**: a gRPC error of an indefinite kind (a context's
error is one, `callErr_ctxErr`). -/
def indefCall (err : GoInterface) : IProp GF :=
  iprop(∃ k : CallErr, callErr err k ∗ ⌜k.indefinite = true⌝)

/-- A read-only slice of `Op`s modelled by `os`. -/
def opsAt (sl : GoSlice) (os : List OpM) : IProp GF :=
  iprop(∃ vs : List go_etcd_io.etcd.client.v3.Op, sl ↦*□ vs ∗ [∗list] v; o ∈ vs; os, opAt v o)
/-- A read-only slice of `Cmp`s. -/
def cmpsAt (sl : GoSlice) (ms : List (Option EtcdModel.Compare)) : IProp GF :=
  iprop(∃ vs : List go_etcd_io.etcd.client.v3.Cmp, sl ↦*□ vs ∗ [∗list] v; m ∈ vs; ms, cmpAt v m)
/-- A read-only slice of `OpOption`s acting as `gs`, in order. -/
def optsAt (sl : GoSlice) (gs : List (OpM → OpM)) : IProp GF :=
  iprop(∃ fs : List GoFunc, sl ↦*□ fs ∗ [∗list] f; g ∈ fs; gs, optAt f g)
def compactOptsAt (sl : GoSlice) (gs : List (CompactOpM → CompactOpM)) : IProp GF :=
  iprop(∃ fs : List GoFunc, sl ↦*□ fs ∗ [∗list] f; g ∈ fs; gs, compactOptAt f g)
def leaseOptsAt (sl : GoSlice) (gs : List (Bool → Bool)) : IProp GF :=
  iprop(∃ fs : List GoFunc, sl ↦*□ fs ∗ [∗list] f; g ∈ fs; gs, leaseOptAt f g)

/-! ### Replies -/

/-- What a `Get` returns for the answer `res`. -/
def getReply (res : Resp) (resp : Loc) (err : GoInterface) : IProp GF :=
  match res with
  | .ok (.range rev a) => iprop(⌜err = GoInterface.nil⌝ ∗ ∃ m, rangeRespOwn resp (DFrac.own 1) m ∗
      ⌜m.hdr.map (·.revision) = some (W64 rev) ∧ m.ofAns a⌝)
  | .err e => iprop(⌜err = errVal e ∧ resp = null⌝)
  | _ => iprop(False)

/-- What a `Put` returns for the answer `res`. -/
def putReply (res : Resp) (resp : Loc) (err : GoInterface) : IProp GF :=
  match res with
  | .ok (.put rev prev) => iprop(⌜err = GoInterface.nil⌝ ∗ ∃ m, putRespOwn resp (DFrac.own 1) m ∗
      ⌜m.hdr.revision = W64 rev ∧ m.prevKv = prev.map KeyValueM.ofKV⌝)
  | .err e => iprop(⌜err = errVal e ∧ resp = null⌝)
  | _ => iprop(False)

/-- What a `Delete` returns for the answer `res`. -/
def deleteReply (res : Resp) (resp : Loc) (err : GoInterface) : IProp GF :=
  match res with
  | .ok (.deleteRange rev n l) => iprop(⌜err = GoInterface.nil⌝ ∗ ∃ m,
      deleteRespOwn resp (DFrac.own 1) m ∗
      ⌜m.hdr.revision = W64 rev ∧ m.deleted = W64 n ∧ m.prevKvs = l.map KeyValueM.ofKV⌝)
  | .err e => iprop(⌜err = errVal e ∧ resp = null⌝)
  | _ => iprop(False)

/-- What a transaction's `Commit` returns for the answer `res`. -/
def txnReply (res : Resp) (resp : Loc) (err : GoInterface) : IProp GF :=
  match res with
  | .ok (.txn rev ok rs) => iprop(⌜err = GoInterface.nil⌝ ∗ ∃ m, txnRespOwn resp (DFrac.own 1) m ∗
      ⌜m.hdr.revision = W64 rev ∧ m.ofResps ok rs⌝)
  | .err e => iprop(⌜err = errVal e ∧ resp = null⌝)
  | _ => iprop(False)

/-- What a `Compact` returns for the answer `res` (its header is not modelled). -/
def compactReply (res : Resp) (resp : Loc) (err : GoInterface) : IProp GF :=
  match res with
  | .ok .compact => iprop(⌜err = GoInterface.nil⌝ ∗ ∃ m, compactRespOwn resp (DFrac.own 1) m)
  | .err e => iprop(⌜err = errVal e ∧ resp = null⌝)
  | _ => iprop(False)

/-- What `Do` returns for the answer `res`: an `OpResponse` with the one reply of its kind. -/
def doReply (res : Resp) (r : go_etcd_io.etcd.client.v3.OpResponse) (err : GoInterface) :
    IProp GF :=
  match res with
  | .ok (.range _ _) => iprop(⌜r.put' = null ∧ r.del' = null ∧ r.txn' = null⌝ ∗ getReply res r.get' err)
  | .ok (.put _ _) => iprop(⌜r.get' = null ∧ r.del' = null ∧ r.txn' = null⌝ ∗ putReply res r.put' err)
  | .ok (.deleteRange _ _ _) =>
      iprop(⌜r.put' = null ∧ r.get' = null ∧ r.txn' = null⌝ ∗ deleteReply res r.del' err)
  | .ok (.txn _ _ _) => iprop(⌜r.put' = null ∧ r.get' = null ∧ r.del' = null⌝ ∗ txnReply res r.txn' err)
  | .err e => iprop(⌜err = errVal e ∧ r.put' = null ∧ r.get' = null ∧ r.del' = null ∧ r.txn' = null⌝)
  | _ => iprop(False)

/-- What a wire-level call returns for the answer `res` (`reply` the client-level reply's
success case, the error as gRPC returns it). -/
def wireReply (reply : Resp → Loc → GoInterface → IProp GF) (res : Resp) (resp : Loc)
    (err : GoInterface) : IProp GF :=
  match res with
  | .err e => iprop(⌜resp = null⌝ ∗ callErr err (.etcd e))
  | .ok _ => reply res resp err

/-- An error of a wire-level call that settles nothing. -/
def wireIndef (resp : Loc) (err : GoInterface) : IProp GF :=
  iprop(⌜resp = null⌝ ∗ indefCall err)

/-! ## The KV contract, once (`KV.*Triple`)

Each takes the method value `f` (a concrete method, an interface method, a promoted one) and the
receiver's handle `P`. -/

/-- **`Put(ctx, key, val, opts...)`**: the put `OpPut(key, val, opts...)` builds, linearized by the
caller's update (exclusive), or an indefinite error. The options are given back. `OpPut` must not
panic (`putPanics`: no range, limit, revision, sort, filter, ... option). -/
def KV.PutTriple (f : val) (P : IProp GF) (γ : Cluster) (who : Principal) : Prop :=
  ∀ (ctx : GoInterface) (p : Principal) (key v : GoString) (opts : GoSlice) (gs : List (OpM → OpM))
    (Q : State → State → Resp → IProp GF),
  {{ P ∗ Context.ctxOk ctx ∗ ctxPrin who ctx p ∗ optsAt opts gs ∗ ⌜¬ (opPutM key v gs).putPanics⌝ ∗
      AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
        <{ ∀∀ (σ' : State) (res : Resp),
             ⌜Step p (.put (opPutM key v gs).putReq) σ σ' res⌝ ∗ etcdState γ σ',
           COMM Q σ σ' res }> }}
    (App (App (App (App (Val f) (Val #ctx)) (Val #key)) (Val #v)) (Val #opts))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); optsAt opts gs ∗
      ((∃ σ σ' res, Q σ σ' res ∗ putReply res resp err) ∨ (⌜resp = null⌝ ∗ indefCall err)) }}

/-- **`Get(ctx, key, opts...)`**: the range `OpGet(key, opts...)` builds (linearizable, or
serializable: answered at a member's possibly stale view, `Step`), the caller's update persistent. -/
def KV.GetTriple (f : val) (P : IProp GF) (γ : Cluster) (who : Principal) : Prop :=
  ∀ (ctx : GoInterface) (p : Principal) (lo : Nat) (key : GoString) (opts : GoSlice) (gs : List (OpM → OpM))
    (Q : State → State → Resp → IProp GF),
  {{ P ∗ Context.ctxOk ctx ∗ authLb γ lo ∗ ctxPrin who ctx p ∗ optsAt opts gs ∗ ⌜¬ prefixAndFromKey gs⌝ ∗
      □ AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
        <{ ∀∀ (σ' : State) (res : Resp),
             ⌜Step p (.range (opGetM key gs).rangeReq) σ σ' res lo⌝ ∗ etcdState γ σ',
           COMM Q σ σ' res }> }}
    (App (App (App (Val f) (Val #ctx)) (Val #key)) (Val #opts))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); optsAt opts gs ∗
      ((∃ σ σ' res, Q σ σ' res ∗ getReply res resp err) ∨ (⌜resp = null⌝ ∗ indefCall err)) }}

/-- **`Delete(ctx, key, opts...)`**: the delete `OpDelete(key, opts...)` builds. -/
def KV.DeleteTriple (f : val) (P : IProp GF) (γ : Cluster) (who : Principal) : Prop :=
  ∀ (ctx : GoInterface) (p : Principal) (key : GoString) (opts : GoSlice) (gs : List (OpM → OpM))
    (Q : State → State → Resp → IProp GF),
  {{ P ∗ Context.ctxOk ctx ∗ ctxPrin who ctx p ∗ optsAt opts gs ∗
      ⌜¬ prefixAndFromKey gs ∧ ¬ (opDeleteM key gs).deletePanics⌝ ∗
      AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
        <{ ∀∀ (σ' : State) (res : Resp),
             ⌜Step p (.deleteRange (opDeleteM key gs).deleteReq) σ σ' res⌝ ∗ etcdState γ σ',
           COMM Q σ σ' res }> }}
    (App (App (App (Val f) (Val #ctx)) (Val #key)) (Val #opts))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); optsAt opts gs ∗
      ((∃ σ σ' res, Q σ σ' res ∗ deleteReply res resp err) ∨ (⌜resp = null⌝ ∗ indefCall err)) }}

/-- **`Compact(ctx, rev, opts...)`**: a compaction at `rev`. `rev ≠ 0`: a scope restriction
(`issues/etcd-restore-scheduled-compact-zero.md`: a member that crashes during a compaction at
`0` comes back with another compaction revision than the others, which no model of one cluster
state describes; no etcd compactor issues `Compact(0)`). -/
def KV.CompactTriple (f : val) (P : IProp GF) (γ : Cluster) (who : Principal) : Prop :=
  ∀ (ctx : GoInterface) (p : Principal) (rev : w64) (opts : GoSlice) (gs : List (CompactOpM → CompactOpM))
    (Q : State → State → Resp → IProp GF),
  {{ P ∗ Context.ctxOk ctx ∗ ctxPrin who ctx p ∗ compactOptsAt opts gs ∗ ⌜rev ≠ W64 0⌝ ∗
      AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
        <{ ∀∀ (σ' : State) (res : Resp),
             ⌜Step p (.compact (sint.Z rev)
                ((gs.foldl (fun (o : CompactOpM) (g : CompactOpM → CompactOpM) => g o)
                  { revision := rev, physical := false }).physical))
               σ σ' res⌝ ∗ etcdState γ σ',
           COMM Q σ σ' res }> }}
    (App (App (App (Val f) (Val #ctx)) (Val #rev)) (Val #opts))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); compactOptsAt opts gs ∗
      ((∃ σ σ' res, Q σ σ' res ∗ compactReply res resp err) ∨ (⌜resp = null⌝ ∗ indefCall err)) }}

/-- **`Do(ctx, op)`**: the request of `op` (a read's update persistent). `op` must be of a type at
every depth (`toReq`; `Do` and `toRequestOp` panic on a zero `Op`). -/
def KV.DoTriple (f : val) (P : IProp GF) (γ : Cluster) (who : Principal) : Prop :=
  ∀ (ctx : GoInterface) (p : Principal) (lo : Nat) (op : go_etcd_io.etcd.client.v3.Op) (o : OpM) (rq : Req)
    (Q : State → State → Resp → IProp GF),
  {{ P ∗ Context.ctxOk ctx ∗ authLb γ lo ∗ ctxPrin who ctx p ∗ opAt op o ∗ ⌜o.toReq = some rq⌝ ∗
      □?(rq.isRead) AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
        <{ ∀∀ (σ' : State) (res : Resp), ⌜Step p rq σ σ' res lo⌝ ∗ etcdState γ σ',
           COMM Q σ σ' res }> }}
    (App (App (Val f) (Val #ctx)) (Val #op))
  {{ (r : go_etcd_io.etcd.client.v3.OpResponse) (err : GoInterface), RET (PairV #r #err);
      (∃ σ σ' res, Q σ σ' res ∗ doReply res r err) ∨
      (⌜r.put' = null ∧ r.get' = null ∧ r.del' = null ∧ r.txn' = null⌝ ∗ indefCall err) }}

/-- **`GetStream(ctx, key, opts...)`**: the range `OpGet(key, opts...)` builds, answered in chunks
on a channel (`streamAt`), read by a goroutine (the caller's thread token); the caller's update
persistent. An error opening the stream is indefinite, or a refusal that fired nothing (the stream
interceptor re-authenticates at every open: `ErrAuthFailed`, ...). The revision asked is not
negative (`nonissues/etcd-rangestream-negative-revision-unpinned.md`: such a stream is read at a
new revision on every page). -/
def KV.GetStreamTriple (f : val) (P : IProp GF) (γ : Cluster) (who : Principal) : Prop :=
  ∀ (ctx : GoInterface) (p : Principal) (lo : Nat) (key : GoString) (opts : GoSlice) (gs : List (OpM → OpM))
    (Q : State → State → Resp → IProp GF),
  {{ P ∗ Context.ctxOk ctx ∗ authLb γ lo ∗ ctxPrin who ctx p ∗ optsAt opts gs ∗ ⌜¬ prefixAndFromKey gs⌝ ∗ threadTok ∗
      ⌜0 ≤ sint.Z (opGetM key gs).rev⌝ ∗
      □ AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
        <{ ∀∀ (σ' : State) (res : Resp),
             ⌜Step p (.range (opGetM key gs).rangeReq) σ σ' res lo⌝ ∗ etcdState γ σ',
           COMM Q σ σ' res }> }}
    (App (App (App (Val f) (Val #ctx)) (Val #key)) (Val #opts))
  {{ (ch : Loc) (err : GoInterface), RET (PairV #ch #err); optsAt opts gs ∗
      ((⌜err = GoInterface.nil⌝ ∗ streamAt ch γ p (opGetM key gs).rangeReq Q [] false) ∨
       (⌜ch = null⌝ ∗ threadTok ∗
         (indefCall err ∨ ⌜∃ e : EtcdErr, e.refusal = true ∧ err = errVal e⌝))) }}

/-- **`Txn(ctx)`**: a new transaction over `ctx`, nothing set. -/
def KV.TxnTriple (f : val) (P : IProp GF) (γ : Cluster) (who : Principal) : Prop :=
  ∀ (ctx : GoInterface) (p : Principal),
  {{ P ∗ Context.ctxOk ctx ∗ ctxPrin who ctx p }}
    (App (Val f) (Val #ctx))
  {{ (iv : GoInterface), RET #iv; txnAt iv γ p ctx TxnSt.empty }}

/-- **`If(cs...)`** (the first of the three; it panics otherwise): the comparisons appended (a
zero `Cmp` as a zero `Compare`). The transaction is the value returned (`*txn` returns itself; a
wrapper may return the `Txn` it wraps, as Kubernetes' latency tracker does). -/
def Txn.IfTriple (f : val) (iv : GoInterface) (γ : Cluster) (who : Principal) (ctx : GoInterface) :
    Prop :=
  ∀ (st : TxnSt) (cs : GoSlice) (ms : List (Option EtcdModel.Compare)),
  {{ txnAt (GF := GF) iv γ who ctx st ∗ cmpsAt cs ms ∗
      ⌜st.cif = false ∧ st.cthen = false ∧ st.celse = false⌝ }}
    (App (Val f) (Val #cs))
  {{ (r : GoInterface), RET #r; txnAt r γ who ctx { st with cif := true, cmps := st.cmps ++ ms.map (fun c => c.getD Compare.zero) } }}

/-- **`Then(ops...)`** (before `Else`, once): the operations' requests appended. -/
def Txn.ThenTriple (f : val) (iv : GoInterface) (γ : Cluster) (who : Principal)
    (ctx : GoInterface) : Prop :=
  ∀ (st : TxnSt) (ops : GoSlice) (os : List OpM) (rs : List RequestOp),
  {{ txnAt (GF := GF) iv γ who ctx st ∗ opsAt ops os ∗ ⌜OpM.toReqOps os = some rs⌝ ∗
      ⌜st.cthen = false ∧ st.celse = false⌝ }}
    (App (Val f) (Val #ops))
  {{ (r : GoInterface), RET #r; txnAt r γ who ctx { st with cthen := true, sus := st.sus ++ rs } }}

/-- **`Else(ops...)`** (once). -/
def Txn.ElseTriple (f : val) (iv : GoInterface) (γ : Cluster) (who : Principal)
    (ctx : GoInterface) : Prop :=
  ∀ (st : TxnSt) (ops : GoSlice) (os : List OpM) (rs : List RequestOp),
  {{ txnAt (GF := GF) iv γ who ctx st ∗ opsAt ops os ∗ ⌜OpM.toReqOps os = some rs⌝ ∗ ⌜st.celse = false⌝ }}
    (App (Val f) (Val #ops))
  {{ (r : GoInterface), RET #r; txnAt r γ who ctx { st with celse := true, fas := st.fas ++ rs } }}

/-- **`Commit()`**: the transaction so far, over the context it was built with (a read-only one's
update persistent); the transaction is given back (a second `Commit` sends it again). -/
def Txn.CommitTriple (f : val) (iv : GoInterface) (γ : Cluster) (who : Principal)
    (ctx : GoInterface) : Prop :=
  ∀ (st : TxnSt) (lo : Nat) (Q : State → State → Resp → IProp GF),
  {{ txnAt (GF := GF) iv γ who ctx st ∗ authLb γ lo ∗
      □?((Req.txn st.req).isRead) AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
        <{ ∀∀ (σ' : State) (res : Resp), ⌜Step who (.txn st.req) σ σ' res lo⌝ ∗ etcdState γ σ',
           COMM Q σ σ' res }> }}
    (App (Val f) (Val #()))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); txnAt iv γ who ctx st ∗
      ((∃ σ σ' res, Q σ σ' res ∗ txnReply res resp err) ∨ (⌜resp = null⌝ ∗ indefCall err)) }}

/-! ## The wire-level contract (`RemoteKV.*Triple`): the gRPC boundary

The same updates over the request messages (`api/v3/Wire.lean`, any fraction, given back), with
gRPC's errors (`callErr`); the call options `callOptsOk` (a mutable RPC's not repeatable). -/

def RemoteKV.RangeTriple (f : val) (P : IProp GF) (γ : Cluster) (who : Principal) : Prop :=
  ∀ (ctx : GoInterface) (p : Principal) (lo : Nat) (req : Loc) (dq : DFrac) (r : RangeReq) (opts : GoSlice) (rep : Bool)
    (Q : State → State → Resp → IProp GF),
  {{ P ∗ Context.ctxOk ctx ∗ authLb γ lo ∗ ctxPrin who ctx p ∗ rangeReqOwn req dq r ∗ callOptsOk opts rep ∗
      □ AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
        <{ ∀∀ (σ' : State) (res : Resp), ⌜Step p (.range r) σ σ' res lo⌝ ∗ etcdState γ σ',
           COMM Q σ σ' res }> }}
    (App (App (App (Val f) (Val #ctx)) (Val #req)) (Val #opts))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); rangeReqOwn req dq r ∗
      ((∃ σ σ' res, Q σ σ' res ∗ wireReply getReply res resp err) ∨ wireIndef resp err) }}

def RemoteKV.RangeStreamTriple (f : val) (P : IProp GF) (γ : Cluster) (who : Principal) : Prop :=
  ∀ (ctx : GoInterface) (p : Principal) (lo : Nat) (req : Loc) (dq : DFrac) (r : RangeReq) (opts : GoSlice) (rep : Bool)
    (Q : State → State → Resp → IProp GF),
  {{ P ∗ Context.ctxOk ctx ∗ authLb γ lo ∗ ctxPrin who ctx p ∗ rangeReqOwn req dq r ∗ callOptsOk opts rep ∗
      ⌜0 ≤ r.revision⌝ ∗
      □ AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
        <{ ∀∀ (σ' : State) (res : Resp), ⌜Step p (.range r) σ σ' res lo⌝ ∗ etcdState γ σ',
           COMM Q σ σ' res }> }}
    (App (App (App (Val f) (Val #ctx)) (Val #req)) (Val #opts))
  {{ (sc : GoInterface) (err : GoInterface), RET (PairV #sc #err); rangeReqOwn req dq r ∗
      ((⌜err = GoInterface.nil⌝ ∗ wireStreamAt sc γ p r Q []) ∨
       (⌜sc = GoInterface.nil⌝ ∗
         (indefCall err ∨ ∃ e : EtcdErr, ⌜e.refusal = true⌝ ∗ callErr err (.etcd e)))) }}

def RemoteKV.PutTriple (f : val) (P : IProp GF) (γ : Cluster) (who : Principal) : Prop :=
  ∀ (ctx : GoInterface) (p : Principal) (req : Loc) (dq : DFrac) (r : PutReq) (opts : GoSlice)
    (Q : State → State → Resp → IProp GF),
  {{ P ∗ Context.ctxOk ctx ∗ ctxPrin who ctx p ∗ putReqOwn req dq r ∗ callOptsOk opts false ∗
      AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
        <{ ∀∀ (σ' : State) (res : Resp), ⌜Step p (.put r) σ σ' res⌝ ∗ etcdState γ σ',
           COMM Q σ σ' res }> }}
    (App (App (App (Val f) (Val #ctx)) (Val #req)) (Val #opts))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); putReqOwn req dq r ∗
      ((∃ σ σ' res, Q σ σ' res ∗ wireReply putReply res resp err) ∨ wireIndef resp err) }}

def RemoteKV.DeleteRangeTriple (f : val) (P : IProp GF) (γ : Cluster) (who : Principal) : Prop :=
  ∀ (ctx : GoInterface) (p : Principal) (req : Loc) (dq : DFrac) (r : DeleteReq) (opts : GoSlice)
    (Q : State → State → Resp → IProp GF),
  {{ P ∗ Context.ctxOk ctx ∗ ctxPrin who ctx p ∗ deleteReqOwn req dq r ∗ callOptsOk opts false ∗
      AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
        <{ ∀∀ (σ' : State) (res : Resp), ⌜Step p (.deleteRange r) σ σ' res⌝ ∗ etcdState γ σ',
           COMM Q σ σ' res }> }}
    (App (App (App (Val f) (Val #ctx)) (Val #req)) (Val #opts))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); deleteReqOwn req dq r ∗
      ((∃ σ σ' res, Q σ σ' res ∗ wireReply deleteReply res resp err) ∨ wireIndef resp err) }}

def RemoteKV.TxnTriple (f : val) (P : IProp GF) (γ : Cluster) (who : Principal) : Prop :=
  ∀ (ctx : GoInterface) (p : Principal) (lo : Nat) (req : Loc) (dq : DFrac) (t : TxnReq) (opts : GoSlice)
    (Q : State → State → Resp → IProp GF),
  {{ P ∗ Context.ctxOk ctx ∗ authLb γ lo ∗ ctxPrin who ctx p ∗ txnReqOwn req dq t ∗ callOptsOk opts false ∗
      □?((Req.txn t).isRead) AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
        <{ ∀∀ (σ' : State) (res : Resp), ⌜Step p (.txn t) σ σ' res lo⌝ ∗ etcdState γ σ',
           COMM Q σ σ' res }> }}
    (App (App (App (Val f) (Val #ctx)) (Val #req)) (Val #opts))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); txnReqOwn req dq t ∗
      ((∃ σ σ' res, Q σ σ' res ∗ wireReply txnReply res resp err) ∨ wireIndef resp err) }}

def RemoteKV.CompactTriple (f : val) (P : IProp GF) (γ : Cluster) (who : Principal) : Prop :=
  ∀ (ctx : GoInterface) (p : Principal) (req : Loc) (dq : DFrac) (rev : Int) (phys : Bool) (opts : GoSlice)
    (Q : State → State → Resp → IProp GF),
  {{ P ∗ Context.ctxOk ctx ∗ ctxPrin who ctx p ∗ compactReqOwn req dq rev phys ∗ callOptsOk opts false ∗ ⌜rev ≠ 0⌝ ∗
      AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
        <{ ∀∀ (σ' : State) (res : Resp), ⌜Step p (.compact rev phys) σ σ' res⌝ ∗ etcdState γ σ',
           COMM Q σ σ' res }> }}
    (App (App (App (Val f) (Val #ctx)) (Val #req)) (Val #opts))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); compactReqOwn req dq rev phys ∗
      ((∃ σ σ' res, Q σ σ' res ∗ wireReply compactReply res resp err) ∨ wireIndef resp err) }}

/-! ## Laws -/

def handles_persistent.spec : Prop :=
  (∀ ctx tok, Persistent (ctxTokenMd (GF := GF) ctx tok)) ∧
  (∀ conn γ who, Persistent (connOk (GF := GF) conn γ who)) ∧
  (∀ sl rep, Persistent (callOptsOk (GF := GF) sl rep)) ∧
  (∀ c γ who, Persistent (clientConnOk (GF := GF) c γ who)) ∧
  (∀ c γ who, Persistent (isClient (GF := GF) c γ who)) ∧
  (∀ v γ who, Persistent (kvAt (GF := GF) v γ who)) ∧
  (∀ kv γ who, Persistent (kvHandle (GF := GF) kv γ who)) ∧
  (∀ v γ who, Persistent (remoteKVAt (GF := GF) v γ who)) ∧
  (∀ rkv γ who, Persistent (retryKVHandle (GF := GF) rkv γ who)) ∧
  (∀ v γ who, Persistent (watcherAt (GF := GF) v γ who)) ∧
  (∀ v γ who, Persistent (leaseAt (GF := GF) v γ who)) ∧
  (∀ v γ who, Persistent (authAt (GF := GF) v γ who)) ∧
  (∀ v γ who, Persistent (clusterAt (GF := GF) v γ who)) ∧
  (∀ v γ who, Persistent (maintAt (GF := GF) v γ who)) ∧
  (∀ op o, Persistent (opAt (GF := GF) op o)) ∧
  (∀ c m, Persistent (cmpAt (GF := GF) c m)) ∧
  (∀ err k, Persistent (callErr (GF := GF) err k)) ∧
  (∀ dflt ctx p, Persistent (ctxPrin (GF := GF) dflt ctx p)) ∧
  (∀ c γ who, Persistent (clientRest (GF := GF) c γ who))

/-- **What `opAt` means**: the `Op` struct's fields (its byte slices, sort option, comparisons
and nested operations read-only; `end` `nil` exactly when no range end is set). -/
def opAt_unfold.spec : Prop := ∀ (op : go_etcd_io.etcd.client.v3.Op) (o : OpM),
  opAt (GF := GF) op o ⊣⊢
    ⌜op.t' = o.t ∧ op.limit' = o.limit ∧ op.serializable' = o.serializable ∧
      op.keysOnly' = o.keysOnly ∧ op.countOnly' = o.countOnly ∧ op.minModRev' = o.minModRev ∧
      op.maxModRev' = o.maxModRev ∧ op.minCreateRev' = o.minCreateRev ∧
      op.maxCreateRev' = o.maxCreateRev ∧ op.rev' = o.rev ∧ op.prevKV' = o.prevKV ∧
      op.fragment' = o.fragment ∧ op.watchBufLogEnabled' = o.watchBufLog ∧
      op.ignoreValue' = o.ignoreValue ∧ op.ignoreLease' = o.ignoreLease ∧
      op.progressNotify' = o.progressNotify ∧ op.createdNotify' = o.createdNotify ∧
      op.filterPut' = o.filterPut ∧ op.filterDelete' = o.filterDelete ∧ op.leaseID' = o.leaseID ∧
      op.isOptsWithFromKey' = o.isOptsWithFromKey ∧ op.isOptsWithPrefix' = o.isOptsWithPrefix⌝ ∗
    op.key' ↦*□ o.key ∗
    (match o.rangeEnd with
     | none => iprop(⌜op.end' = slice.nil⌝)
     | some e => iprop(op.end' ↦*□ e)) ∗
    (match o.sort with
     | none => iprop(⌜op.sort' = null⌝)
     | some (tg, od) => iprop(op.sort' ↦□
         ({ Target' := tg, Order' := od } : go_etcd_io.etcd.client.v3.SortOption))) ∗
    op.val' ↦*□ o.val ∗ cmpsAt op.cmps' o.cmps ∗ opsAt op.thenOps' o.thenOps ∗
    opsAt op.elseOps' o.elseOps

/-- **What `cmpAt` means**: a zero `Cmp` (nil message), or one whose message, read-only, is the
comparison. -/
def cmpAt_unfold.spec : Prop := ∀ (c : go_etcd_io.etcd.client.v3.Cmp) (m : Option EtcdModel.Compare),
  cmpAt (GF := GF) c m ⊣⊢ optOwn compareOwn c.c' DFrac.discard m

/-- **What `optAt` means**: calling the closure on a pointer to an `Op` modelled by `o` leaves one
modelled by `g o`, and the closure for another call. -/
def optAt_call.spec : Prop := ∀ (f : GoFunc) (g : OpM → OpM) (p : Loc)
    (op : go_etcd_io.etcd.client.v3.Op) (o : OpM),
  {{ optAt (GF := GF) f g ∗ p ↦ op ∗ opAt op o }}
    (App (Val #f) (Val #p))
  {{ RET #(); optAt f g ∗ ∃ op' : go_etcd_io.etcd.client.v3.Op, p ↦ op' ∗ opAt op' (g o) }}

/-- An option never changes an `Op`'s type nor its branches (no `OpOption` can: those fields are
unexported, and the package's options set others): `OpPut(...)` stays a put whatever its options. -/
def optAt_type.spec : Prop := ∀ (f : GoFunc) (g : OpM → OpM),
  optAt (GF := GF) f g ⊢
    ⌜∀ o, (g o).t = o.t ∧ (g o).cmps = o.cmps ∧ (g o).thenOps = o.thenOps ∧ (g o).elseOps = o.elseOps⌝

def compactOptAt_call.spec : Prop := ∀ (f : GoFunc) (g : CompactOpM → CompactOpM) (p : Loc)
    (op : go_etcd_io.etcd.client.v3.CompactOp),
  {{ compactOptAt (GF := GF) f g ∗ p ↦ op }}
    (App (Val #f) (Val #p))
  {{ RET #(); compactOptAt f g ∗ ∃ op' : go_etcd_io.etcd.client.v3.CompactOp, p ↦ op' ∗
      ⌜(op'.revision', op'.physical') =
        (let m := g { revision := op.revision', physical := op.physical' }; (m.revision, m.physical))⌝ }}

def leaseOptAt_call.spec : Prop := ∀ (f : GoFunc) (g : Bool → Bool) (p : Loc)
    (op : go_etcd_io.etcd.client.v3.LeaseOp),
  {{ leaseOptAt (GF := GF) f g ∗ p ↦ op }}
    (App (Val #f) (Val #p))
  {{ RET #(); leaseOptAt f g ∗ ∃ op' : go_etcd_io.etcd.client.v3.LeaseOp, p ↦ op' ∗
      ⌜op'.id' = op.id' ∧ op'.attachedKeys' = g op.attachedKeys'⌝ }}

/-- A client's connection and call options. -/
def isClient_conn.spec : Prop := ∀ c γ who, isClient (GF := GF) c γ who ⊢ clientConnOk c γ who

/-- A client's `KV` field, for good. -/
def isClient_KV.spec : Prop := ∀ c γ who,
  isClient (GF := GF) c γ who ⊢
    ∃ v : GoInterface, c.[go_etcd_io.etcd.client.v3.Client, go!"KV"] ↦□ v ∗ kvAt v γ who

/-- A client's other interface fields, for good (what 1b and 1c's promoted methods read). -/
def isClient_fields.spec : Prop := ∀ c γ who,
  isClient (GF := GF) c γ who ⊢
    (∃ v : GoInterface, c.[go_etcd_io.etcd.client.v3.Client, go!"Watcher"] ↦□ v ∗ watcherAt v γ who) ∗
    (∃ v : GoInterface, c.[go_etcd_io.etcd.client.v3.Client, go!"Lease"] ↦□ v ∗ leaseAt v γ who) ∗
    (∃ v : GoInterface, c.[go_etcd_io.etcd.client.v3.Client, go!"Auth"] ↦□ v ∗ authAt v γ who) ∗
    (∃ v : GoInterface, c.[go_etcd_io.etcd.client.v3.Client, go!"Cluster"] ↦□ v ∗ clusterAt v γ who) ∗
    (∃ v : GoInterface, c.[go_etcd_io.etcd.client.v3.Client, go!"Maintenance"] ↦□ v ∗ maintAt v γ who)

/-- A writable client's `KV` field: any value meeting the KV contract may be written. -/
def clientMut_KV.spec : Prop := ∀ c γ who,
  clientMut (GF := GF) c γ who ⊣⊢
    ∃ v : GoInterface, c.[go_etcd_io.etcd.client.v3.Client, go!"KV"] ↦ v ∗ kvAt v γ who ∗
      clientMutRest c γ who

def clientMut_conn.spec : Prop := ∀ c γ who, clientMut (GF := GF) c γ who ⊢ clientConnOk c γ who

def clientMut_freeze.spec : Prop := ∀ c γ who, clientMut (GF := GF) c γ who ⊢ |==> isClient c γ who

/-- **Freeze all but the `KV` field**: the field stays the caller's (writable, any value), the rest
for good. -/
def clientMut_split.spec : Prop := ∀ c γ who,
  clientMut (GF := GF) c γ who ⊢ |==> ∃ v : GoInterface,
    c.[go_etcd_io.etcd.client.v3.Client, go!"KV"] ↦ v ∗ kvAt v γ who ∗ clientRest c γ who

def clientRest_persistent.spec : Prop := ∀ c γ who, Persistent (clientRest (GF := GF) c γ who)

def isClient_rest.spec : Prop := ∀ c γ who, isClient (GF := GF) c γ who ⊢ clientRest c γ who

def clientRest_conn.spec : Prop := ∀ c γ who, clientRest (GF := GF) c γ who ⊢ clientConnOk c γ who

def clientRest_fields.spec : Prop := ∀ c γ who,
  clientRest (GF := GF) c γ who ⊢
    (∃ v : GoInterface, c.[go_etcd_io.etcd.client.v3.Client, go!"Watcher"] ↦□ v ∗ watcherAt v γ who) ∗
    (∃ v : GoInterface, c.[go_etcd_io.etcd.client.v3.Client, go!"Lease"] ↦□ v ∗ leaseAt v γ who) ∗
    (∃ v : GoInterface, c.[go_etcd_io.etcd.client.v3.Client, go!"Auth"] ↦□ v ∗ authAt v γ who) ∗
    (∃ v : GoInterface, c.[go_etcd_io.etcd.client.v3.Client, go!"Cluster"] ↦□ v ∗ clusterAt v γ who) ∗
    (∃ v : GoInterface, c.[go_etcd_io.etcd.client.v3.Client, go!"Maintenance"] ↦□ v ∗ maintAt v γ who)

/-- The bundle's triples. -/
def kvAt_methods.spec : Prop := ∀ (v : GoInterface) (γ : Cluster) (who : Principal),
  KV.PutTriple (v @!! go_etcd_io.etcd.client.v3.KV.ty @!! go!"Put") (kvAt (GF := GF) v γ who) γ who ∧
  KV.GetTriple (v @!! go_etcd_io.etcd.client.v3.KV.ty @!! go!"Get") (kvAt (GF := GF) v γ who) γ who ∧
  KV.DeleteTriple (v @!! go_etcd_io.etcd.client.v3.KV.ty @!! go!"Delete") (kvAt (GF := GF) v γ who) γ who ∧
  KV.CompactTriple (v @!! go_etcd_io.etcd.client.v3.KV.ty @!! go!"Compact") (kvAt (GF := GF) v γ who) γ who ∧
  KV.DoTriple (v @!! go_etcd_io.etcd.client.v3.KV.ty @!! go!"Do") (kvAt (GF := GF) v γ who) γ who ∧
  KV.TxnTriple (v @!! go_etcd_io.etcd.client.v3.KV.ty @!! go!"Txn") (kvAt (GF := GF) v γ who) γ who ∧
  KV.GetStreamTriple (v @!! go_etcd_io.etcd.client.v3.KV.ty @!! go!"GetStream") (kvAt (GF := GF) v γ who) γ who

/-- A `*kv` meets the KV contract (its methods' specs, `kv__*.lean`). -/
def kvHandle_kvAt.spec : Prop := ∀ kv γ who,
  kvHandle (GF := GF) kv γ who ⊢
    kvAt (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty) #kv) γ who

/-- A `Txn` value's triples. -/
def txnAt_methods.spec : Prop := ∀ (iv : GoInterface) (γ : Cluster) (who : Principal)
    (ctx : GoInterface),
  Txn.IfTriple (GF := GF) (iv @!! go_etcd_io.etcd.client.v3.Txn.ty @!! go!"If") iv γ who ctx ∧
  Txn.ThenTriple (GF := GF) (iv @!! go_etcd_io.etcd.client.v3.Txn.ty @!! go!"Then") iv γ who ctx ∧
  Txn.ElseTriple (GF := GF) (iv @!! go_etcd_io.etcd.client.v3.Txn.ty @!! go!"Else") iv γ who ctx ∧
  Txn.CommitTriple (GF := GF) (iv @!! go_etcd_io.etcd.client.v3.Txn.ty @!! go!"Commit") iv γ who ctx

/-- The wire-level bundle's triples. -/
def remoteKVAt_methods.spec : Prop := ∀ (v : GoInterface) (γ : Cluster) (who : Principal),
  RemoteKV.RangeTriple (v @!! go_etcd_io.etcd.api.v3.etcdserverpb.KVClient.ty @!! go!"Range")
    (remoteKVAt (GF := GF) v γ who) γ who ∧
  RemoteKV.PutTriple (v @!! go_etcd_io.etcd.api.v3.etcdserverpb.KVClient.ty @!! go!"Put")
    (remoteKVAt (GF := GF) v γ who) γ who ∧
  RemoteKV.DeleteRangeTriple (v @!! go_etcd_io.etcd.api.v3.etcdserverpb.KVClient.ty @!! go!"DeleteRange")
    (remoteKVAt (GF := GF) v γ who) γ who ∧
  RemoteKV.TxnTriple (v @!! go_etcd_io.etcd.api.v3.etcdserverpb.KVClient.ty @!! go!"Txn")
    (remoteKVAt (GF := GF) v γ who) γ who ∧
  RemoteKV.CompactTriple (v @!! go_etcd_io.etcd.api.v3.etcdserverpb.KVClient.ty @!! go!"Compact")
    (remoteKVAt (GF := GF) v γ who) γ who ∧
  RemoteKV.RangeStreamTriple (v @!! go_etcd_io.etcd.api.v3.etcdserverpb.KVClient.ty @!! go!"RangeStream")
    (remoteKVAt (GF := GF) v γ who) γ who

/-- A `*retryKVClient` meets the wire-level contract (its methods' specs, `retryKVClient__*.lean`). -/
def retryKVHandle_remoteKVAt.spec : Prop := ∀ rkv γ who,
  retryKVHandle (GF := GF) rkv γ who ⊢
    remoteKVAt (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.retryKVClient.ty) #rkv)
      γ who

/-- **Receiving from `GetStream`'s channel**: a chunk (its message owned), or the terminal error
chunk (a linearized error; `ErrCompacted` with no `Q`, when the revision the server pinned at the
first page was compacted before a later read, possibly before any chunk: the caller relists; or
one that settles nothing), or, the channel closed after the last chunk, the caller's `Q` with the answer the chunks
make (`streamMatches`). After the terminal error the channel is closed: nothing more. If the
consumer stops receiving with two or more chunks still to come (the channel holds one), the
reading goroutine blocks for good and keeps its thread token
(`nonissues/etcd-client-getstream-abandoned-leak.md`). -/
def streamAt_recv.spec : Prop := ∀ (ch : Loc) (γ : Cluster) (who : Principal) (r : RangeReq)
    (Q : State → State → Resp → IProp GF) (ms : List RangeRespM) (fin : Bool),
  {{ streamAt (GF := GF) ch γ who r Q ms fin }}
    (App (Val (chan.receive go_etcd_io.etcd.client.v3.RangeStreamResponse.ty)) (Val #ch))
  {{ (v : go_etcd_io.etcd.client.v3.RangeStreamResponse) (ok : Bool), RET (PairV #v #ok);
      if fin then ⌜ok = false⌝ else
      if ok then
        (⌜v.closeErr' = GoInterface.nil⌝ ∗ ∃ m : RangeRespM,
            rangeRespOwn v.RangeResponse' (DFrac.own 1) m ∗ streamAt ch γ who r Q (ms ++ [m]) false) ∨
        (⌜v.RangeResponse' = null⌝ ∗ streamAt ch γ who r Q ms true ∗
          ((∃ (σ σ' : State) (e : EtcdErr), Q σ σ' (.err e) ∗ ⌜v.closeErr' = errVal e⌝) ∨
           -- the revision the server pinned at the first page was compacted before a later read
           -- (a later page, or the count of the rest before the first chunk is sent)
           ⌜v.closeErr' = errVal .compacted⌝ ∨
           indefCall v.closeErr'))
      else ∃ (σ σ' : State) (rev : Nat) (a : RangeAns),
        Q σ σ' (.ok (.range rev a)) ∗ ⌜streamMatches r ms rev a⌝ }}

/-- **Receiving from the wire stream** (`sc.Recv()`, 2a): a chunk, the end (`io.EOF`, the caller's
`Q` with the answer the chunks make), or an error (linearized, or settling nothing). -/
def wireStreamAt_recv.spec : Prop := ∀ (sc : GoInterface) (γ : Cluster) (who : Principal)
    (r : RangeReq) (Q : State → State → Resp → IProp GF) (ms : List RangeRespM),
  {{ wireStreamAt (GF := GF) sc γ who r Q ms }}
    (App (Val (sc @!! go_etcd_io.etcd.api.v3.etcdserverpb.KV_RangeStreamClient.ty @!! go!"Recv"))
      (Val #()))
  {{ (p : Loc) (err : GoInterface), RET (PairV #p #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ (rr : Loc) (m : RangeRespM),
         protoRest go_etcd_io.etcd.api.v3.etcdserverpb.RangeStreamResponse p (DFrac.own 1) ∗
         p.[go_etcd_io.etcd.api.v3.etcdserverpb.RangeStreamResponse, go!"RangeResponse"] ↦ rr ∗
         rangeRespOwn rr (DFrac.own 1) m ∗ wireStreamAt sc γ who r Q (ms ++ [m])) ∨
      (⌜p = null⌝ ∗ globalAddr io.EOF ↦□ err ∗
         ∃ (σ σ' : State) (rev : Nat) (a : RangeAns),
           Q σ σ' (.ok (.range rev a)) ∗ ⌜streamMatches r ms rev a⌝) ∨
      (⌜p = null⌝ ∗ ((∃ (σ σ' : State) (e : EtcdErr), Q σ σ' (.err e) ∗ callErr err (.etcd e)) ∨
         callErr err (.etcd .compacted) ∨
         indefCall err)) }}

def ctxPrin_persistent.spec : Prop := ∀ dflt ctx p, Persistent (ctxPrin (GF := GF) dflt ctx p)

/-- A context with no gRPC outgoing metadata (`Context.ctxNoMeta`, dischargeable by whoever owns
a root context) carries no token: its requests are the client's. -/
def ctxPrin_of_noMeta.spec : Prop := ∀ ctx dflt,
  Context.ctxNoMeta (GF := GF) ctx ⊢ ctxPrin dflt ctx dflt

/-- **A forwarded token**: a client without credentials sends a context's token: its user's
requests (the gRPC proxy, the in-process client). -/
def ctxPrin_token.spec : Prop := ∀ (γ : Cluster) (ctx : GoInterface) (tok u : GoString),
  ctxTokenMd (GF := GF) ctx tok ∗ tokenUser γ tok u ⊢ ctxPrin none ctx (some u)

/-- A client with credentials of `u`, its context carrying a token of `u` too. -/
def ctxPrin_tokenSame.spec : Prop := ∀ (γ : Cluster) (ctx : GoInterface) (tok u : GoString),
  ctxTokenMd (GF := GF) ctx tok ∗ tokenUser γ tok u ⊢ ctxPrin (some u) ctx (some u)

/-- A `WithValue` at a key that is not grpc's outgoing-metadata key keeps it. -/
def ctxPrin_value.spec : Prop := ∀ (ctx ctx' : GoInterface) (ki : GoInterfaceOk) (dflt p : Principal),
  ctxPrin (GF := GF) dflt ctx p ∗ Context.ctxValueAt ctx ctx' (GoInterface.ok ki) ∗
    ⌜ki.ty ≠ google_golang_org.grpc.metadata.mdOutgoingKey.ty⌝ ⊢ ctxPrin dflt ctx' p

/-- **A client call's error is no package's own `errors.New` value** (1d's `ErrLocked`, the
recipes' sentinels): of the `*errors.errorString` errors, a call returns only `context.Canceled`'s
(2a: gRPC's errors are statuses, etcd's `EtcdError`s, a deadline `deadlineExceededError`). A
caller tells its sentinel `x.[errorString, "s"] ↦□ msg` apart by its message. -/
def callErr_errorsNew.spec : Prop := ∀ (err : GoInterface) (k : CallErr) (x : Loc),
  callErr (GF := GF) err k ∗
    ⌜err = interface.mkOk (go.GoType.PointerType errors.errorString.ty) #x⌝ ⊢
  globalAddr context.Canceled ↦□ err

def ctxPrin_background.spec : Prop := ∀ dflt,
  ⊢ ctxPrin (GF := GF) dflt (GoInterface.ok context.backgroundCtxVal) dflt

/-- `TODO()`'s context carries no metadata. -/
def ctxPrin_todo.spec : Prop :=
  ∀ (dflt : Principal),
  {{ isPkgInit (PROP := IProp GF) pkg_id.context }}
    (App (Val (@! context.TODO)) (Val #()))
  {{ (ctx : GoInterface), RET #ctx; ctxPrin dflt ctx dflt }}

/-- A child (`WithCancel`, `WithTimeout`, ...) carries its parent's metadata. -/
def ctxPrin_child.spec : Prop := ∀ ctx ctx' dflt p,
  ctxPrin (GF := GF) dflt ctx p ∗ Context.ctxChild ctx ctx' ⊢ ctxPrin dflt ctx' p

/-- One error, one kind. -/
def callErr_agree.spec : Prop := ∀ err k k',
  callErr (GF := GF) err k ∗ callErr err k' ⊢ ⌜k = k'⌝

/-- **`errors.Is(err, target)`** of a call's error and one of etcd's errors (Kubernetes' and the
cache's style): true exactly for that error (2a: a gRPC status's `Is` is false against an
`EtcdError`; a context's error has none). -/
def errorsIs_errVal.spec : Prop :=
  ∀ (err : GoInterface) (e : EtcdErr),
  {{ isPkgInit (PROP := IProp GF) pkg_id.errors ∗ (⌜∃ e', err = errVal e'⌝ ∨ indefCall err) }}
    (App (App (Val (@! errors.Is)) (Val #err)) (Val #(errVal e)))
  {{ (b : Bool), RET #b; ⌜b = true ↔ err = errVal e⌝ }}

/-- An indefinite call error is no definite etcd error (`indefErr`). -/
def indefCall_pure.spec : Prop := ∀ err, indefCall (GF := GF) err ⊢ ⌜indefErr err⌝

/-- A context's error is an `.other` call error (`rpctypes.Error` keeps it, it is no gRPC status:
2a). -/
def callErr_ctxErr.spec : Prop := ∀ err, context.isCtxErr (GF := GF) err ⊢ callErr err .other

/-- `errVal e` is itself an etcd error a call may return (2a: `rpctypes.Error` keeps it). -/
def callErr_errVal.spec : Prop := ∀ e, ⊢ callErr (GF := GF) (errVal e) (.etcd e)

/-- The client package's globals after initialization: `noPrefixEnd` holds `[0]`, read-only. -/
def init.spec : Prop :=
  isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ⊢
    ∃ sl : GoSlice, globalAddr go_etcd_io.etcd.client.v3.noPrefixEnd ↦□ sl ∗ sl ↦*□ [W8 0]

end res

end ClientV3
end EtcdGrove
end Perennial
