/-
# etcd's key-value store as a state machine

This file is meant to be read and checked by people who know etcd. It defines, as plain
functions with no program logic, what etcd's key-value API does: the state an etcd server's
key-value store is in, and what each request (`Put`, `Range`, `DeleteRange`, `Txn`) does to it
and answers. The proofs of the server state their results in these terms only: a top-level spec
says that a request takes effect atomically on the whole state, as `next` below steps it, and
that its response is the one this file gives for the state it took effect on
(`etcdserver/KVSpecs.lean`). That the server's own model of its store agrees with these
definitions is proved separately (`etcdserver/StateMachineRefinement.lean`), so nothing here
is taken on trust except that it says what etcd is meant to do.

What etcd does is stated here as the server of the verified revision does it (the fork
`upamanyus/etcd`, branch `goose-lean`; `server/etcdserver/txn/{put,range,delete,txn}.go` over
`server/storage/mvcc`). Where that differs from etcd's API documentation
(`api/etcdserverpb/rpc.proto`, the website's API reference), the definition says so in a
**Deviation** paragraph, and the issue file under `issues/` records it.

**The state** (`State`). etcd keeps every revision of its key-value map (multi-version
concurrency control): revision `r` is the map after the `r`-th write. The state is the list of
these maps, `revs[0], ..., revs[rev]`, the last the current one. A new cluster's store is at
revision 1 with no key (`State.init`; mvcc's `NewStore` starts at revision 1). A write that
changes something makes one new revision, whatever the number of keys it changes (a delete of
several keys, a transaction); a write that changes nothing makes none.

**What is left out.**
* *Compaction.* etcd can discard the revisions below a compaction revision (`Compact`); the
  verified server runs with compaction off, so every revision is kept and no request fails with
  `ErrCompacted`.
* *Leases.* A key-value records the id of the lease it is attached to (`lease`), and a put
  with a lease fails unless the lease exists (`ErrLeaseNotFound`); leases themselves (granting,
  expiry, revocation) are not modelled, and the specs cover the puts with no lease only.
* *The response header's cluster, member, term and leader fields* (filled by the gRPC layer,
  not by the store); a response here has the header's `revision` only.
* *The requests the gRPC layer rejects before they reach the store* (an empty key, a value with
  `ignore_value`, too many operations in a transaction, ...): the specs are of the server's
  methods (`EtcdServer.Put`, ...), below that layer.

**Conventions.** Keys and values are byte strings (`GoString`), ordered as Go's `bytes.Compare`
orders them (bytewise, lexicographically: `go.GoStringLt`). Revisions, versions, limits and
lease ids are protobuf `int64`s (`w64`, read as signed integers by `sint.Z`); the state's
revision numbers are natural numbers. A key-value (`EtcdKv`, `mvccpb.KeyValue`) has the fields
`key`, `createRev` (`create_revision`), `modRev` (`mod_revision`), `version`, `value` and
`lease`.
-/
module

public import Proof.go_etcd_io.etcd.api.v3.mvccpb.KeyValue

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace EtcdSM

/-! ## Ranges of keys -/

/-- **The key `k` is in the range `[key, rangeEnd)`** a request names (`key`, `range_end`):
* `rangeEnd` empty: the single key `key`;
* `rangeEnd` the one byte `"\x00"`: every key from `key` on;
* otherwise: the keys `k` with `key ≤ k < rangeEnd`.

(A prefix `p` is the range from `p` to `p` with its last byte incremented, as clients compute
it; this file does not need the notion.) -/
def inRange (key rangeEnd k : GoString) : Bool :=
  if rangeEnd = [] then decide (k = key)
  else if rangeEnd = [W8 0] then !decide (go.GoStringLt k key)
  else !decide (go.GoStringLt k key) && decide (go.GoStringLt k rangeEnd)

/-! ## A revision's key-value map -/

/-- **A revision's key-value map**: its key-values, at most one per key, in increasing key
order. (The definitions below keep the order: `store` inserts at the key's position.) -/
abbrev KVMap := List EtcdKv

namespace KVMap

/-- The key-value of the key `k`, if the map has it. -/
def get (m : KVMap) (k : GoString) : Option EtcdKv := m.find? (fun v => decide (v.key = k))

/-- `m` with the key-value `v` stored at its key: it replaces the key's old key-value, or is
inserted at its position in key order. -/
def store (v : EtcdKv) : KVMap → KVMap
  | [] => [v]
  | w :: ws =>
    if go.GoStringLt w.key v.key then w :: store v ws
    else if go.GoStringLt v.key w.key then v :: w :: ws
    else v :: ws

/-- The key-values of the keys in the range `[key, rangeEnd)`, in key order. -/
def range (m : KVMap) (key rangeEnd : GoString) : List EtcdKv :=
  m.filter (fun v => inRange key rangeEnd v.key)

/-- **A put of the key `k` with `value` and `lease`, at revision `r`**: a key not in the map gets
create and mod revision `r` and version 1; a key in it keeps its create revision and gets mod
revision `r` and its version plus one. -/
def put (r : w64) (k value : GoString) (lease : w64) (m : KVMap) : KVMap :=
  m.store (match m.get k with
    | some v => { v with modRev := r, version := v.version + W64 1, value := value, lease := lease }
    | none =>
      { key := k, createRev := r, modRev := r, version := W64 1, value := value, lease := lease })

/-- `m` without the keys in the range `[key, rangeEnd)`. -/
def deleteRange (m : KVMap) (key rangeEnd : GoString) : KVMap :=
  m.filter (fun v => !inRange key rangeEnd v.key)

end KVMap

/-! ## The state -/

/-- **The state of etcd's key-value store**: the map at every revision, from revision 0 to the
current one (`revs[r]` is the map at revision `r`). -/
structure State where
  revs : List KVMap

namespace State

/-- The current revision. -/
def rev (σ : State) : Nat := σ.revs.length - 1

/-- The current map (at the current revision). -/
def kvs (σ : State) : KVMap := σ.revs.getLastD []

/-- The map at revision `r` (for `r` at most the current revision). -/
def atRev (σ : State) (r : Nat) : KVMap := σ.revs.getD r []

/-- **A new cluster's store**: revision 1, no key (mvcc's `NewStore` starts at revision 1; the
revision 0 before it is empty too). -/
def init : State := ⟨[[], []]⟩

/-- The state with one more revision, whose map is `m`. -/
def newRevision (σ : State) (m : KVMap) : State := ⟨σ.revs ++ [m]⟩

end State

/-- Why a request fails, when the store itself rejects it. -/
inductive Error where
  /-- `ErrKeyNotFound` (`rpctypes.ErrKeyNotFound`): a put with `ignore_value` or `ignore_lease`
  of a key that does not exist (in a transaction: of any such put on the path taken). -/
  | keyNotFound
  /-- `ErrFutureRev` (`mvcc.ErrFutureRev`): a range at a revision above the current one. -/
  | futureRev

/-! ## Put -/

/-- **A put request** (`etcdserverpb.PutRequest`). -/
structure PutRequest where
  key : GoString
  value : GoString
  /-- the lease to attach the key to (`0`: none) -/
  lease : w64
  /-- answer the key's key-value before the put -/
  prevKv : Bool
  /-- keep the key's current value (the request's `value` is not used) -/
  ignoreValue : Bool
  /-- keep the key's current lease (the request's `lease` is not used) -/
  ignoreLease : Bool

/-- **A put's response** (`etcdserverpb.PutResponse`): the revision of the store after the put
(the header's `revision`), and the key's key-value before it if the request asked for it. -/
structure PutResponse where
  revision : Nat
  prevKv : Option EtcdKv

/-- **A put** on the state `σ`: the key's key-value written at the next revision, its value and
lease the request's or, with `ignore_value`/`ignore_lease`, the key's current ones; which fails
with `ErrKeyNotFound` (and changes nothing) if the key does not exist and the request keeps its
value or lease. A put always makes a new revision, even of an unchanged value (the version and
mod revision change). -/
def put (req : PutRequest) (σ : State) : Except Error (State × PutResponse) :=
  let old := σ.kvs.get req.key
  if (req.ignoreValue || req.ignoreLease) && old.isNone then .error .keyNotFound
  else
    let r := σ.rev + 1
    let value := if req.ignoreValue then (old.map EtcdKv.value).getD [] else req.value
    let lease := if req.ignoreLease then (old.map EtcdKv.lease).getD (W64 0) else req.lease
    .ok (σ.newRevision (σ.kvs.put (W64 (r : Int)) req.key value lease),
      { revision := r, prevKv := if req.prevKv then old else none })

/-- The state after a put: the new one, or `σ` itself if the put fails. -/
def putNext (req : PutRequest) (σ : State) : State :=
  match put req σ with
  | .ok p => p.1
  | .error _ => σ

/-! ## DeleteRange -/

/-- **A delete request** (`etcdserverpb.DeleteRangeRequest`): the keys of the range
`[key, range_end)` (`inRange`). -/
structure DeleteRangeRequest where
  key : GoString
  rangeEnd : GoString
  /-- answer the deleted key-values -/
  prevKv : Bool

/-- **A delete's response** (`etcdserverpb.DeleteRangeResponse`): the store's revision after
the delete, the number of keys deleted, and the deleted key-values (in key order) if the
request asked for them. -/
structure DeleteRangeResponse where
  revision : Nat
  deleted : Nat
  prevKvs : List EtcdKv

/-- **A delete** on the state `σ`: the keys of the range removed, in one new revision; no new
revision if the range has no key. -/
def deleteRange (req : DeleteRangeRequest) (σ : State) : State × DeleteRangeResponse :=
  let ks := σ.kvs.range req.key req.rangeEnd
  let σ' := if ks = [] then σ else σ.newRevision (σ.kvs.deleteRange req.key req.rangeEnd)
  (σ', { revision := σ'.rev, deleted := ks.length, prevKvs := if req.prevKv then ks else [] })

/-- The state after a delete. -/
def deleteRangeNext (req : DeleteRangeRequest) (σ : State) : State := (deleteRange req σ).1

/-! ## Range -/

/-- `RangeRequest.SortOrder`: `NONE` (0), `ASCEND` (1), `DESCEND` (2). -/
def sortNone : w64 := W64 0
def sortAscend : w64 := W64 1
def sortDescend : w64 := W64 2

/-- `RangeRequest.SortTarget`: `KEY` (0), `VERSION` (1), `CREATE` (2), `MOD` (3), `VALUE` (4). -/
def targetKey : w64 := W64 0
def targetVersion : w64 := W64 1
def targetCreate : w64 := W64 2
def targetMod : w64 := W64 3
def targetValue : w64 := W64 4

/-- **A range request** (`etcdserverpb.RangeRequest`). The two enumerations are their protobuf
numbers, sign-extended from `int32`. -/
structure RangeRequest where
  key : GoString
  rangeEnd : GoString
  /-- at most this many key-values (`0` or negative: no limit) -/
  limit : w64
  /-- the revision to read at (`0` or negative: the current one) -/
  revision : w64
  sortOrder : w64
  sortTarget : w64
  /-- a serializable read: answered from the member's own store, without going through raft -/
  serializable : Bool
  /-- answer keys only (no values) -/
  keysOnly : Bool
  /-- answer the count only (no key-values) -/
  countOnly : Bool
  /-- keep only the key-values with a mod/create revision at least/at most these (`0`: no
  bound) -/
  minModRevision : w64
  maxModRevision : w64
  minCreateRevision : w64
  maxCreateRevision : w64

/-- **A range's response** (`etcdserverpb.RangeResponse`): the store's current revision (not the
revision read at), the key-values, whether the limit left some out (`more`), and the number of
keys in the range at the revision read (`count`). -/
structure RangeResponse where
  revision : Nat
  kvs : List EtcdKv
  more : Bool
  count : Nat

/-- **The revision a range reads at**: the request's, or the current one if it is `0` or
negative; `ErrFutureRev` if it is above the current one. -/
def readRevision (req : RangeRequest) (σ : State) : Except Error Nat :=
  if (σ.rev : Int) < sint.Z req.revision then .error .futureRev
  else if sint.Z req.revision ≤ 0 then .ok σ.rev
  else .ok (sint.Z req.revision).toNat

/-- The key-value passes the request's revision filters (a bound of `0` is no bound). -/
def revFiltersOk (req : RangeRequest) (v : EtcdKv) : Bool :=
  (decide (req.minModRevision = W64 0) || decide (sint.Z req.minModRevision ≤ sint.Z v.modRev)) &&
  (decide (req.maxModRevision = W64 0) || decide (sint.Z v.modRev ≤ sint.Z req.maxModRevision)) &&
  (decide (req.minCreateRevision = W64 0) ||
    decide (sint.Z req.minCreateRevision ≤ sint.Z v.createRev)) &&
  (decide (req.maxCreateRevision = W64 0) ||
    decide (sint.Z v.createRev ≤ sint.Z req.maxCreateRevision))

/-- **The order the key-values are sorted in**: the request's, except that a target other than
the key with no order is sorted ascending, and ascending by key is no sort (the map is in key
order already). An order other than `ASCEND` and `DESCEND` is no sort. -/
def effectiveSortOrder (req : RangeRequest) : w64 :=
  if req.sortTarget ≠ targetKey ∧ req.sortOrder = sortNone then sortAscend
  else if req.sortTarget = targetKey ∧ req.sortOrder = sortAscend then sortNone
  else req.sortOrder

/-- `a` sorts no later than `b` by the target (an unknown target sorts by key). -/
def sortsBefore (target : w64) (a b : EtcdKv) : Prop :=
  if target = targetVersion then sint.Z a.version ≤ sint.Z b.version
  else if target = targetCreate then sint.Z a.createRev ≤ sint.Z b.createRev
  else if target = targetMod then sint.Z a.modRev ≤ sint.Z b.modRev
  else if target = targetValue then go.GoStringLe a.value b.value
  else go.GoStringLe a.key b.key

/-- **The limit the store reads with** (`rangeLimit` in `range.go`): the request's limit plus one
(to tell whether there are more), if it is positive and the ordering is the store's own (key
order, no revision filter); no limit (`0`) otherwise. -/
def readLimit (req : RangeRequest) : w64 :=
  let defaultOrder : Bool :=
    decide (req.sortOrder = sortNone ∨ (req.sortTarget = targetKey ∧ req.sortOrder = sortAscend))
  let hasFilter : Bool := decide (req.minModRevision ≠ W64 0 ∨ req.maxModRevision ≠ W64 0 ∨
    req.minCreateRevision ≠ W64 0 ∨ req.maxCreateRevision ≠ W64 0)
  let l := if defaultOrder = false ∨ hasFilter = true then W64 0 else req.limit
  if 0 < sint.Z l ∧ sint.Z l < 2 ^ 63 - 1 then l + W64 1 else l

/-- The first `n` of `l` for a positive `n`, all of `l` otherwise. -/
def takeUpTo {α : Type} (n : w64) (l : List α) : List α :=
  if 0 < sint.Z n then l.take (sint.Z n).toNat else l

/-- **What the store reads**, keys only (no value and no lease) when the request is keys-only and
not sorted by value.

**Deviation** (`issues/etcd-range-keys-only-lease.md`): a keys-only response's key-values have lease
`0` unless it is sorted by value; the documentation says only that keys-only leaves out the
values. -/
def readKv (req : RangeRequest) (v : EtcdKv) : EtcdKv :=
  if req.keysOnly && decide (req.sortTarget ≠ targetValue) then { v with value := [], lease := W64 0 }
  else v

/-- **The key-values to sort**: the map's in the range, at most `readLimit` of them in key order,
as read, those passing the revision filters; none if count-only. -/
def candidates (req : RangeRequest) (m : KVMap) : List EtcdKv :=
  if req.countOnly then []
  else ((takeUpTo (readLimit req) (m.range req.key req.rangeEnd)).map (readKv req)).filter
    (revFiltersOk req)

/-- **The key-values and `more` of a range** of the map `m`: some order `l` of the candidates,
sorted as the request asks (ascending or descending by its target; equal ones in any order, since
the server's sort is not stable), cut at the limit, values dropped if keys-only; `more` when the
limit cut it.

**Deviation** (`issues/etcd-range-sort-none-limit.md`): with a sort target other than the key, no sort
order and a positive limit, the store reads only the first `limit + 1` keys of the range (in key
order) and sorts those (`readLimit` tests the request's order, the sort its effective one), so the
response is not the first `limit` key-values of the whole range in the target's order. -/
def RangeKvsOk (req : RangeRequest) (m : KVMap) (kvs : List EtcdKv) (more : Bool) : Prop :=
  ∃ l : List EtcdKv,
    l.Perm (candidates req m) ∧
    (effectiveSortOrder req = sortAscend → l.Pairwise (sortsBefore req.sortTarget)) ∧
    (effectiveSortOrder req = sortDescend → l.Pairwise (fun a b => sortsBefore req.sortTarget b a)) ∧
    (effectiveSortOrder req ≠ sortAscend → effectiveSortOrder req ≠ sortDescend →
      l = candidates req m) ∧
    more = decide (0 < sint.Z req.limit ∧ sint.Z req.limit < (l.length : Int)) ∧
    kvs = ((if more then l.take (sint.Z req.limit).toNat else l).map
      (fun v => if req.keysOnly then { v with value := [] } else v))

/-- **A range's possible responses** on the state `σ` (a range changes nothing): the revision to
read at (`readRevision`), then a response at the current revision with key-values and `more` as
`RangeKvsOk` allows of the map at that revision, and the count of the range's keys there. -/
def RangeOk (req : RangeRequest) (σ : State) (resp : Except Error RangeResponse) : Prop :=
  match readRevision req σ with
  | .error e => resp = .error e
  | .ok r =>
    ∃ res : RangeResponse, resp = .ok res ∧ res.revision = σ.rev ∧
      RangeKvsOk req (σ.atRev r) res.kvs res.more ∧
      res.count = ((σ.atRev r).range req.key req.rangeEnd).length

/-! ## Txn -/

/-- `Compare.CompareResult`. -/
inductive CompareResult where
  | equal | greater | less | notEqual
  deriving DecidableEq

/-- `Compare.CompareTarget`: what a comparison reads of a key-value. -/
inductive CompareTarget where
  | version | create | mod | value | lease
  deriving DecidableEq

/-- **A comparison** (`etcdserverpb.Compare`) of the keys of the range `[key, rangeEnd)`
against an operand: `number` for a version, a create or mod revision or a lease, `value` for a
value. -/
structure Compare where
  result : CompareResult
  target : CompareTarget
  key : GoString
  rangeEnd : GoString
  number : w64
  value : GoString

/-- `-1`, `0` or `1`: `a` is less than, equal to or greater than `b`, as signed integers. -/
def compareInt64 (a b : w64) : Int :=
  if sint.Z a < sint.Z b then -1 else if a = b then 0 else 1

/-- `-1`, `0` or `1`: `a` is less than, equal to or greater than `b`, as byte strings
(`bytes.Compare`). -/
def compareBytes (a b : GoString) : Int :=
  if go.GoStringLt a b then -1 else if a = b then 0 else 1

/-- The comparison holds of the key-value `v`. -/
def Compare.holdsOn (c : Compare) (v : EtcdKv) : Bool :=
  let sign : Int := match c.target with
    | .version => compareInt64 v.version c.number
    | .create => compareInt64 v.createRev c.number
    | .mod => compareInt64 v.modRev c.number
    | .lease => compareInt64 v.lease c.number
    | .value => compareBytes v.value c.value
  match c.result with
  | .equal => decide (sign = 0)
  | .notEqual => decide (sign ≠ 0)
  | .greater => decide (0 < sign)
  | .less => decide (sign < 0)

/-- A key with no key-value, as a comparison reads it: create and mod revision, version and
lease `0`, an empty value. -/
def absentKv (k : GoString) : EtcdKv :=
  { key := k, createRev := W64 0, modRev := W64 0, version := W64 0, value := [], lease := W64 0 }

/-- **The comparison holds in the map `m`**: of every key-value of its range; if the range has
no key, of an absent key-value, except that a value comparison then fails (`applyCompare`:
"nil == empty string in grpc; no way to represent missing value"). -/
def Compare.holds (c : Compare) (m : KVMap) : Bool :=
  let sel := m.range c.key c.rangeEnd
  if sel = [] then decide (c.target ≠ .value) && c.holdsOn (absentKv c.key)
  else sel.all c.holdsOn

/-- **An operation of a transaction** (`etcdserverpb.RequestOp`): a range, a put, a delete, or a
nested transaction. -/
inductive RequestOp where
  | range (req : RangeRequest)
  | put (req : PutRequest)
  | deleteRange (req : DeleteRangeRequest)
  | txn (compare : List Compare) (success failure : List RequestOp)

/-- **A transaction request** (`etcdserverpb.TxnRequest`): if every comparison holds, the
`success` operations, otherwise the `failure` ones. -/
structure TxnRequest where
  compare : List Compare
  success : List RequestOp
  failure : List RequestOp

/-- **An operation's result**: what a range read (its request and the map it read: its responses
are those `RangeKvsOk` allows of that map, its count the number of keys of its range there, its
header's revision the transaction's), a put's previous key-value if asked, a delete's number of
keys and their key-values if asked, a nested transaction's verdict and its branch's results. -/
inductive OpResult where
  | range (req : RangeRequest) (m : KVMap)
  | put (prevKv : Option EtcdKv)
  | deleteRange (deleted : Nat) (prevKvs : List EtcdKv)
  | txn (succeeded : Bool) (results : List OpResult)

mutual
/-- **The operation's key check** at the map `s0` the transaction started from: a put that keeps
the key's value or lease needs the key there; a nested transaction's, of the branch its
comparisons choose there. -/
def opKeysOk (s0 : KVMap) : RequestOp → Bool
  | .range _ => true
  | .put req => !(req.ignoreValue || req.ignoreLease) || (s0.get req.key).isSome
  | .deleteRange _ => true
  | .txn cs ts es =>
    match cs.all (·.holds s0) with
    | true => opsKeysOk s0 ts
    | false => opsKeysOk s0 es

/-- The key check of every operation. -/
def opsKeysOk (s0 : KVMap) : List RequestOp → Bool
  | [] => true
  | op :: ops => opKeysOk s0 op && opsKeysOk s0 ops
end

mutual
/-- **One operation of a transaction at revision `r`**, on the map `m` the operations before it
left (`s0`: the map the transaction started from): the map after it, whether it wrote, and its
result. A range reads `m`; a put writes as `put` does (its value or lease kept from `m`'s
key-value); a delete removes the keys of its range in `m` (a write if there was one); a nested
transaction's comparisons are evaluated at `s0`, the transaction's start, not at `m`. -/
def runOp (s0 : KVMap) (r : w64) (m : KVMap) : RequestOp → KVMap × Bool × OpResult
  | .range req => (m, false, .range req m)
  | .put req =>
    let old := m.get req.key
    let value := if req.ignoreValue then (old.map EtcdKv.value).getD [] else req.value
    let lease := if req.ignoreLease then (old.map EtcdKv.lease).getD (W64 0) else req.lease
    (m.put r req.key value lease, true, .put (if req.prevKv then old else none))
  | .deleteRange req =>
    let ks := m.range req.key req.rangeEnd
    (m.deleteRange req.key req.rangeEnd, decide (ks ≠ []),
      .deleteRange ks.length (if req.prevKv then ks else []))
  | .txn cs ts es =>
    match cs.all (·.holds s0) with
    | true => let res := runOps s0 r m ts; (res.1, res.2.1, .txn true res.2.2)
    | false => let res := runOps s0 r m es; (res.1, res.2.1, .txn false res.2.2)

/-- The operations in order, each on the map the ones before it left. -/
def runOps (s0 : KVMap) (r : w64) (m : KVMap) : List RequestOp → KVMap × Bool × List OpResult
  | [] => (m, false, [])
  | op :: ops =>
    let a := runOp s0 r m op
    let b := runOps s0 r a.1 ops
    (b.1, a.2.1 || b.2.1, a.2.2 :: b.2.2)
end

/-- **A transaction's result**: the store's revision after it, whether its comparisons held, and
the chosen branch's results. -/
structure TxnResult where
  revision : Nat
  succeeded : Bool
  results : List OpResult

/-- **A transaction** on the state `σ`: its comparisons evaluated at the current map choose a
branch; if a put of the branch (or of a nested transaction's chosen branch) keeps the value or
lease of a key the current map does not have, it fails with `ErrKeyNotFound` and changes
nothing; otherwise the branch runs at the next revision, which it makes only if it wrote.

**Deviation** (`issues/etcd-txn-delete-then-ignore-put.md`): the key check is made at the map the
transaction started from, not at the map a put runs on. A put that keeps the value or lease of
a key an earlier operation of the same transaction deleted passes the check, and the server's
apply loop then panics (on every member; the gRPC layer's overlap check misses a delete of every
key from a key on). `runOp` gives such a put an empty value (and lease `0`); the specs exclude
these transactions. -/
def txn (req : TxnRequest) (σ : State) : Except Error (State × TxnResult) :=
  let s0 := σ.kvs
  let ok := req.compare.all (·.holds s0)
  let ops := if ok then req.success else req.failure
  if opsKeysOk s0 ops = false then .error .keyNotFound
  else
    let res := runOps s0 (W64 ((σ.rev + 1 : Nat) : Int)) s0 ops
    let σ' := if res.2.1 then σ.newRevision res.1 else σ
    .ok (σ', { revision := σ'.rev, succeeded := ok, results := res.2.2 })

mutual
/-- **The operation makes the server panic** (the deviation above): a put that keeps the value or
lease of a key the map it runs on (`m`) does not have, although the map the transaction started
from (`s0`) has it; a nested transaction's chosen branch's. -/
def opPanics (s0 : KVMap) (r : w64) (m : KVMap) : RequestOp → Bool
  | .range _ => false
  | .put req => (req.ignoreValue || req.ignoreLease) && (m.get req.key).isNone &&
      (s0.get req.key).isSome
  | .deleteRange _ => false
  | .txn cs ts es =>
    match cs.all (·.holds s0) with
    | true => opsPanic s0 r m ts
    | false => opsPanic s0 r m es

/-- Some operation makes the server panic, each on the map the ones before it left. -/
def opsPanic (s0 : KVMap) (r : w64) (m : KVMap) : List RequestOp → Bool
  | [] => false
  | op :: ops => opPanics s0 r m op || opsPanic s0 r (runOp s0 r m op).1 ops
end

/-- **The transaction makes the server panic** on the state `σ`. -/
def txnPanics (req : TxnRequest) (σ : State) : Bool :=
  let s0 := σ.kvs
  opsPanic s0 (W64 ((σ.rev + 1 : Nat) : Int)) s0
    (if req.compare.all (·.holds s0) then req.success else req.failure)

/-- The state after a transaction: the new one, or `σ` itself if it fails. -/
def txnNext (req : TxnRequest) (σ : State) : State :=
  match txn req σ with
  | .ok p => p.1
  | .error _ => σ

/-! ## Basic facts (not part of the definitions; for the proofs) -/

@[simp] theorem State.kvs_newRevision (σ : State) (m : KVMap) : (σ.newRevision m).kvs = m := by
  simp [State.newRevision, State.kvs]

@[simp] theorem State.revs_newRevision (σ : State) (m : KVMap) :
    (σ.newRevision m).revs = σ.revs ++ [m] := rfl

theorem State.rev_newRevision (σ : State) (m : KVMap) (h : σ.revs ≠ []) :
    (σ.newRevision m).rev = σ.rev + 1 := by
  have := List.length_pos_iff.2 h
  simp [State.newRevision, State.rev]; omega

theorem State.rev_le_newRevision (σ : State) (m : KVMap) : σ.rev ≤ (σ.newRevision m).rev := by
  simp [State.newRevision, State.rev]

end EtcdSM
end EtcdGrove
end Perennial
