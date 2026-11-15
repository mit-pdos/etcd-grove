/-
# The leasing KV's internal vocabulary (batch 1e)

What the specs of the leasing package's unexported functions (the lease cache, `cache.go`; the
helpers, `util.go`; the KV's and the transaction's own methods, `kv.go`, `txn.go`) are written in.
No client sees it: `Api.lean` is the package's API. These specs are what the client-facing proofs
need (the leasing contract, `LKV.*Triple`), and no more: in particular they say nothing of the
leasing protocol's correctness (which lease key a guard names, what a watch delivered), since the
contract claims none (`Api.lean`'s header, 3.). A stronger contract (after the fixes) strengthens
them.

## Pure models (mirrors of the code)

* `cachedRespOk key σ m`: the Go-level form of `CachedRange`: the response `m` has a header at a
  revision `σ` reached, at most one key-value, of `key`, `More` false, a `Count` of at most one.
  The lease cache keeps it of every cached response (each entry's response, as `Add`, `Update` and
  `delete` leave it), with an `etcdLb γ σ`.
* `leaseGetM o m`: `leaseKey.get(op)`'s copy of the cached response `m` for the get `o`.
* `evalCmpM m c`: `evalCmp(resp, cmp)` (which is not etcd's comparison:
  `issues/leasing-evalcmp-missing-key.md`).
* `inRangeM k b e`, `isBadOpM o`: `inRange`, `isBadOp`.
* `gatherL os` (`gatherOps`), `gatherRespL ms os`, `respOkL ms os` (`gatherResponseOps`), at any depth.
* `recAtHdr key σ m`: the cached response is `key`'s record at its header's revision; `entryOk γL key σ m`:
  that, or the key marked as written through the KV (`lkvMarks`), and `cachedRespOk` either way.
* `guardedReply rq res m`: a transaction reply `m` whose guard held and whose then-branch was the
  single operation of the request `rq`, against `rq`'s answer `res` (what `tryModifyOp`, `revoke`
  and `serverTxn` turn into the caller's reply).

## Resources (opaque; realized by the package's proof)

* `lcAt lc γ γL` (persistent): `lc` is the lease cache of the leasing KV `γL` over the cluster `γ`:
  its `RWMutex` with the lock invariant: the fields `entries`, `revokes`, `header` and the KV's
  `session`, `sessionc` (which the same lock guards, `kv.go`), every entry's response
  (`cachedRespAt`) with `cachedRespOk` and an `etcdLb`, every entry's waiter channel `waitRecv`;
  and the pool of its reader slots.
* `lcHeld lc γ γL q`: the lock invariant's contents, held: `q = 1` with the write lock, a share with
  a read lock (`Update`, `delete`, `evalCmp`, `evalOps` run so).
* `cachedRespAt p q m`: a cached response at `p` (its mutable fields at the share `q`, its header
  and byte slices read-only), modelled by `m`.
* `sessionReady γL` (persistent): a session was set (`lkv.session` is never nil again) and the
  entries map made.
* `waitCloser ch` (exclusive): the right to close the waiter channel `ch` (once); `waitRecv ch`
  (persistent): one may receive from `ch` (nobody sends on it; it is closed or will be).
* `sessMonitor lkv γL`: what `monitorSession`, the only writer of `session` and `sessionc`, holds:
  the other half of the two fields and the current `sessionc`'s close right.

## Laws

`init.spec` (`closedCh` holds a closed channel), `isLeasingKV_lcAt`, `isLeasingKV_ready`
(`sessionReady` and the session's lease id), persistence.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.client.v3.leasing.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Leasing

open Iris Iris.BI EtcdModel EtcdWire ClientV3
open Classical

/-! ## Pure models -/

/-- **A cached response's shape** (`CachedRange` at the Go level): a header at a revision `σ`
reached, at most one key-value, of `key`, `More` false, a `Count` of at most one. -/
def cachedRespOk (key : Key) (σ : State) (m : RangeRespM) : Prop :=
  (∃ h, m.hdr = some h ∧ 0 ≤ sint.Z h.revision ∧ sint.Z h.revision ≤ σ.kv.rev) ∧
  m.kvs.length ≤ 1 ∧ (∀ kv ∈ m.kvs, kv.key = key) ∧ m.more = false ∧
  0 ≤ sint.Z m.count ∧ sint.Z m.count ≤ 1

/-- `leaseKey.get`'s emptiness test: no key-value, a count-only get, or the key-value outside the
get's revision filters. -/
def leaseGetEmpty (o : OpM) (m : RangeRespM) : Bool :=
  match m.kvs with
  | [] => true
  | kv :: _ => decide (o.countOnly = true ∨
      sint.Z kv.modRevision < sint.Z o.minModRev ∨
      (o.maxModRev ≠ W64 0 ∧ sint.Z o.maxModRev < sint.Z kv.modRevision) ∨
      sint.Z kv.createRevision < sint.Z o.minCreateRev ∨
      (o.maxCreateRev ≠ W64 0 ∧ sint.Z o.maxCreateRev < sint.Z kv.createRevision))

/-- **`leaseKey.get(op)`** of the cached response `m` for the get `o`: the header, `More` and
`Count` copied, the first key-value copied (its value dropped for a keys-only get) unless
`leaseGetEmpty`. -/
def leaseGetM (o : OpM) (m : RangeRespM) : RangeRespM :=
  { hdr := m.hdr,
    kvs := if leaseGetEmpty o m then [] else
      (match m.kvs with
       | [] => []
       | kv :: _ => [{ kv with value := if o.keysOnly then [] else kv.value }]),
    more := m.more,
    count := m.count }

/-- `compareInt64`. -/
def cmpInt (a b : Int) : Int := if a < b then -1 else if b < a then 1 else 0

/-- `bytes.Compare`. -/
def cmpBytes (a b : GoString) : Int := if keyLt a b then -1 else if a = b then 0 else 1

/-- **`evalCmp(resp, cmp)`**: the comparison `c` on the cached response `m`: the result `0` when
there is no key-value or the target is the lease (neither as etcd compares). -/
def evalCmpM (m : RangeRespM) (c : EtcdModel.Compare) : Bool :=
  let result : Int :=
    match m.kvs with
    | [] => 0
    | kv :: _ =>
      if c.target = cmpTValue then
        (match c.targetUnion with | .value v => cmpBytes kv.value v | _ => 0)
      else if c.target = cmpTCreate then
        (match c.targetUnion with | .createRevision n => cmpInt (sint.Z kv.createRevision) n | _ => 0)
      else if c.target = cmpTMod then
        (match c.targetUnion with | .modRevision n => cmpInt (sint.Z kv.modRevision) n | _ => 0)
      else if c.target = cmpTVersion then
        (match c.targetUnion with | .version n => cmpInt (sint.Z kv.version) n | _ => 0)
      else 0
  if c.result = cmpEqual then decide (result = 0)
  else if c.result = cmpNotEqual then decide (result ≠ 0)
  else if c.result = cmpGreater then decide (0 < result)
  else if c.result = cmpLess then decide (result < 0)
  else true

/-- **`inRange(k, begin, end)`**: `begin ≤ k`, and `k < end` unless `end` is `"\x00"`. -/
def inRangeM (k b e : GoString) : Bool :=
  decide (keyLe b k ∧ (e = [W8 0] ∨ keyLt k e))

/-- **`isBadOp(op)`**: a revision or a range end set (the cache does not serve it). -/
def isBadOpM (o : OpM) : Bool :=
  decide (0 < sint.Z o.rev ∨ o.rangeEnd.getD [] ≠ [])

/-- A successful answer's revision and its operation-level answer (what a transaction's
`ResponseOp` for the same request carries). -/
def bodyRevOp : RespBody → Option (Nat × OpResp)
  | .range rev a => some (rev, .range rev a)
  | .put rev prev => some (rev, .put prev)
  | .deleteRange rev n l => some (rev, .deleteRange n l)
  | .txn rev ok rs => some (rev, .txn ok rs)
  | _ => none

/-- **A guarded transaction's reply against its single operation's answer**: `m` succeeded, at the
answer's revision, and its one response is the operation's answer (`res` a success). -/
def guardedReply (res : Resp) (m : TxnRespM) : Prop :=
  ∃ b rev o r, res = .ok b ∧ bodyRevOp b = some (rev, o) ∧ m.succeeded = true ∧
    m.hdr.revision = W64 rev ∧ m.responses = [r] ∧ r.ofResp o

mutual
/-- **`gatherOps`** of one operation: a transaction replaced by its branches' operations, at any
depth. -/
def gatherOne : OpM → List OpM
  | o@{ thenOps, elseOps, .. } => if o.t = tTxn then gatherL thenOps ++ gatherL elseOps else [o]
/-- **`gatherOps(ops)`**. -/
def gatherL : List OpM → List OpM
  | [] => []
  | o :: os => gatherOne o ++ gatherL os
end

mutual
/-- `gatherResponseOps` of one operation with its response: a transaction replaced by the operations
of the branch its response took, at any depth. -/
def gatherRespOne : Option ResponseOpM → OpM → List OpM
  | r, o@{ thenOps, elseOps, .. } =>
    if o.t = tTxn then
      (match r with
       | some (.txn _ ok rs) => if ok then gatherRespL rs thenOps else gatherRespL rs elseOps
       | _ => [])
    else [o]
/-- **`gatherResponseOps(resps, ops)`**. -/
def gatherRespL : List ResponseOpM → List OpM → List OpM
  | _, [] => []
  | ms, o :: os => gatherRespOne ms.head? o ++ gatherRespL ms.tail os
end

mutual
/-- `gatherResponseOps` does not panic: a transaction has a transaction response at its index, and
so on in the branch it took. -/
def respOkOne : Option ResponseOpM → OpM → Prop
  | r, o@{ thenOps, elseOps, .. } =>
    o.t = tTxn → ∃ h ok rs, r = some (.txn h ok rs) ∧
      (if ok then respOkL rs thenOps else respOkL rs elseOps)
def respOkL : List ResponseOpM → List OpM → Prop
  | _, [] => True
  | ms, o :: os => respOkOne ms.head? o ∧ respOkL ms.tail os
end

/-- **A cached response is `key`'s record at its header's revision** (a past state's store: what an
acquisition caches, and what stays cached while the key is not written through the KV). -/
def recAtHdr (key : Key) (σ : State) (m : RangeRespM) : Prop :=
  ∃ (h : HeaderM) (r : Nat), m.hdr = some h ∧ h.revision = W64 r ∧ 1 ≤ r ∧ r ≤ σ.kv.rev ∧
    m.kvs = ((σ.kv.storeAt r key).map (fun rc => KeyValueM.ofKV (KV.ofRec key rc))).toList ∧
    m.count = W64 m.kvs.length ∧ m.more = false

/-! ## Resources -/

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- **The lease cache at `lc`** of the leasing KV `γL` over `γ` (persistent; see the header). -/
opaque lcAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (lc : Loc) (γ : Cluster) (γL : LeasingNames) : IProp GF := iprop(True)

/-- **The lease cache's lock invariant, held** (`q = 1`: the write lock; a share: a read lock). -/
opaque lcHeld [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (lc : Loc) (γ : Cluster) (γL : LeasingNames) (q : Qp) : IProp GF := iprop(True)

/-- **A cached response** at `p` (mutable fields at the share `q`), modelled by `m`. -/
opaque cachedRespAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (p : Loc) (q : Qp) (m : RangeRespM) : IProp GF := iprop(True)

/-- **A session was set** (persistent). -/
opaque sessionReady [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (γL : LeasingNames) : IProp GF := iprop(True)

/-- The right to close the waiter channel `ch` (exclusive, once). -/
opaque waitCloser [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (ch : GoChan) : IProp GF := iprop(True)

/-- One may receive from the waiter channel `ch` (persistent). -/
opaque waitRecv [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (ch : GoChan) : IProp GF := iprop(True)

/-- **What the cache keeps of each entry's response** (`m`, with an `etcdLb γ σ`): its shape, and
`key`'s record at its header's revision unless the key is marked as written through the KV. -/
def entryOk (γL : LeasingNames) (key : Key) (σ : State) (m : RangeRespM) : IProp GF :=
  iprop(⌜cachedRespOk key σ m⌝ ∗ (⌜recAtHdr key σ m⌝ ∨ lkvMarks γL (fun k => k = key)))

/-- **`monitorSession`'s resources** (exclusive). -/
opaque sessMonitor [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (lkv : Loc) (γL : LeasingNames) : IProp GF := iprop(True)

def internal_persistent.spec : Prop :=
  (∀ lc γ γL, Persistent (lcAt (GF := GF) lc γ γL)) ∧
  (∀ γL, Persistent (sessionReady (GF := GF) γL)) ∧
  (∀ ch, Persistent (waitRecv (GF := GF) ch))

/-- A waiter channel one may close one may also receive from. -/
def waitCloser_recv.spec : Prop := ∀ ch, waitCloser (GF := GF) ch ⊢ waitCloser ch ∗ waitRecv ch

/-- The package's globals after initialization: `closedCh` holds a closed channel (read-only). -/
def init.spec : Prop :=
  isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ⊢
    ∃ ch : GoChan, globalAddr go_etcd_io.etcd.client.v3.leasing.closedCh ↦□ ch ∗ waitRecv ch

/-- A leasing KV's cache. -/
def isLeasingKV_lcAt.spec : Prop := ∀ lkv γ who pfx γL,
  isLeasingKV (GF := GF) lkv γ who pfx γL ⊢
    lcAt (lkv.[go_etcd_io.etcd.client.v3.leasing.leasingKV, go!"leases"]) γ γL

end res

end Leasing
end EtcdGrove
end Perennial
