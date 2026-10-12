/-
The gRPC KV service's request checks (`key.go`: `checkRangeRequest`, `checkPutRequest`,
`checkDeleteRequest`, `checkTxnRequest`, `checkRequestOp`, `checkIntervals`), as pure
functions of the request models: the shared vocabulary of the checks' specs (unit 1 of the
request path). Lean-first (no Rocq counterpart); plan: `notes/decisions.md`, "The request path:
raft as a contract, the wait registry, the checks as the premises' discharge".

**What the checks read** (`ReqOp`): a `RequestOp` as the checks see it. A range, a put and a
delete keep the txn package's `OpFull` (`txn.rangeOpOf`, `putOpOf`, `deleteOpOf`: the
denotations `txn.requestOpIs` gives), since the put check reads the value and the lease, which a
`TxnOp` forgets (`txn.putTxnOp` of an `IgnoreValue` put has no value); a nested transaction its
comparisons and its two branches; `empty` a `RequestOp` whose oneof is empty (or a `nil`
entry: `checkRequestOp`'s `default`). `ReqOp.toTxnOp` is the transaction model the txn package
runs (`none` for `empty`).

**Each check as the code computes it** (`rangeCheck`, ..., `opCheck`): `none` (the check
returns `nil`), or the first error the code meets (`CheckErr`, the `rpctypes` variable it returns:
`CheckErr.var`). The predicates `rangeReqOk`, `putReqOk`, `deleteReqOk`, `requestOpOk`,
`txnReqOk` are "the check returns `nil`". `checkTxnRequest`'s budget is per level: the nested
operations of a transaction get `maxTxnOps` less the widest of its comparisons and branches
(`opCheck`'s `n - opc`), so the total is not bounded by `maxTxnOps`
(`issues/etcd-max-txn-ops-nested.md`).

**`checkIntervals` as the code computes it** (`ivCheck`): the deletes of a level as affine
intervals (`delIvl`: the point `[k, k + "\x00")` for an empty range end, `[k, end)` otherwise),
the nested transactions' puts and deletes (`ivNest`, both branches, recursively), then the
level's puts (`ivFinish`), with the interval tree's overlap (`adt.ivlCmp`, the `adt` model) and
`Union`'s filter by `["\x00", +∞)`. So a range end `"\x00"` (a from-key delete,
`WithFromKey`) is the interval `[k, "\x00")`, which is empty and overlaps no put: the code's
semantics, not the client's (`issues/etcd-txn-delete-then-ignore-put.md`). The range end is read
from the denotation `o.base.rangeEnd` (`txn.rangeEndOf`), which is the request's bytes for a
request decoded from the wire (protobuf-go decodes an empty `bytes` field as `nil`); an empty but
non-nil `RangeEnd` (built in memory, never from the wire) denotes `[0]` where the code reads a
point: unit 1's specs take the request off the wire.

**What the check is for** (`intervalsOkCheckStmt`, stated, unit 1 proves it): a branch whose
`intervalsOk` holds, run by the server (`txn.srvOps`), writes each key at most once (the
txn package's `keys_nodup_iff_check` condition, hence `NoDupKeysPerRev`), provided it has no
from-key delete (`noFromKeyDel`) and no nested transaction puts a key a later sibling nested
transaction deletes (`siblingSafe`): `checkIntervals` checks a nested transaction's puts against
the deletes of its level and of the siblings *before* it, not after
(`issues/etcd-txn-check-intervals-sibling.md`). Both gaps are the code's.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Base
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.Requests
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.TxnRun
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.HistoryLaws
public import Proof.go_etcd_io.etcd.pkg.v3.adt.Model

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace v3rpc

/-! ## The requests as the checks read them -/

/-- A `RequestOp` as the checks read it (see the file header). -/
inductive ReqOp where
  | range (o : OpFull)
  | put (o : OpFull)
  | delete (o : OpFull)
  | txn (cmps : List CmpModel) (thenOps elseOps : List ReqOp)
  /-- An empty oneof or a `nil` entry: `checkRequestOp`'s `default`. -/
  | empty

mutual
/-- The transaction model of a checked operation (`none`: an empty one). -/
def ReqOp.toTxnOp : ReqOp → Option TxnOp
  | .range o => some (.get o)
  | .put o => some (txn.putTxnOp o)
  | .delete o => some (.delete o)
  | .txn cs ts es =>
    match ReqOp.toTxnOps ts, ReqOp.toTxnOps es with
    | some ts', some es' => some (.txn cs ts' es')
    | _, _ => none
  | .empty => none

/-- The transaction model of checked operations, in order. -/
def ReqOp.toTxnOps : List ReqOp → Option (List TxnOp)
  | [] => some []
  | u :: us =>
    match ReqOp.toTxnOp u, ReqOp.toTxnOps us with
    | some t, some ts => some (t :: ts)
    | _, _ => none
end

/-! ## The checks' errors -/

/-- The errors the checks return, by the `rpctypes` variable. -/
inductive CheckErr where
  | emptyKey | invalidSortOption | valueProvided | leaseProvided | tooManyOps | keyNotFound
  | duplicateKey
  deriving DecidableEq

section vars
variable [FfiSyntax] [GoGlobalContext]

/-- The `rpctypes` variable holding the error. -/
def CheckErr.var : CheckErr → GoString
  | .emptyKey => go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCEmptyKey
  | .invalidSortOption => go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCInvalidSortOption
  | .valueProvided => go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCValueProvided
  | .leaseProvided => go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCLeaseProvided
  | .tooManyOps => go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCTooManyOps
  | .keyNotFound => go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCKeyNotFound
  | .duplicateKey => go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCDuplicateKey

end vars

/-! ## The single-request checks -/

/-- `pb.RangeRequest_SortOrder_name` has the order (`NONE`, `ASCEND`, `DESCEND`). -/
def sortOrderKnown (o : w64) : Bool := decide (0 ≤ sint.Z o ∧ sint.Z o ≤ 2)

/-- `pb.RangeRequest_SortTarget_name` has the target (`KEY`, `VERSION`, `CREATE`, `MOD`,
`VALUE`). -/
def sortTargetKnown (t : w64) : Bool := decide (0 ≤ sint.Z t ∧ sint.Z t ≤ 4)

/-- **`checkRangeRequest`** of the range `o` (`txn.rangeOpOf`'s `sortOrder`/`sortTarget` are
the enumerations' values). -/
def rangeCheck (o : OpFull) : Option CheckErr :=
  if o.key = [] then some .emptyKey
  else if !sortOrderKnown o.sortOrder then some .invalidSortOption
  else if !sortTargetKnown o.sortTarget then some .invalidSortOption
  else none

/-- **`checkPutRequest`** of the put `o` (`txn.putOpOf`). -/
def putCheck (o : OpFull) : Option CheckErr :=
  if o.key = [] then some .emptyKey
  else if o.ignoreValue ∧ o.val ≠ [] then some .valueProvided
  else if o.ignoreLease ∧ o.leaseID ≠ W64 0 then some .leaseProvided
  else none

/-- **`checkDeleteRequest`** of the delete `o` (`txn.deleteOpOf`). -/
def deleteCheck (o : OpFull) : Option CheckErr :=
  if o.key = [] then some .emptyKey else none

def rangeReqOk (o : OpFull) : Prop := rangeCheck o = none
def putReqOk (o : OpFull) : Prop := putCheck o = none
def deleteReqOk (o : OpFull) : Prop := deleteCheck o = none

/-! ## The transaction check -/

/-- The first error of a list of checks. -/
def firstErr : List (Option CheckErr) → Option CheckErr
  | [] => none
  | some e :: _ => some e
  | none :: es => firstErr es

/-- The widest of a transaction's comparisons and branches (`checkTxnRequest`'s `opc`). -/
def txnWidth (cs : List CmpModel) (ts es : List ReqOp) : Nat :=
  max cs.length (max ts.length es.length)

mutual
/-- **`checkRequestOp(u, n)`**: a range, put, delete by its check; a nested transaction by
`checkTxnRequest(_, n)`; an empty one is `ErrGRPCKeyNotFound` (the `etcd-txn-empty-requestop`
precondition of the txn package, discharged here). -/
def opCheck (n : Int) : ReqOp → Option CheckErr
  | .range o => rangeCheck o
  | .put o => putCheck o
  | .delete o => deleteCheck o
  | .txn cs ts es =>
    if n < txnWidth cs ts es then some .tooManyOps
    else if cs.any (fun c => decide (c.key = [])) then some .emptyKey
    else match opsCheck (n - txnWidth cs ts es) ts with
      | some e => some e
      | none => opsCheck (n - txnWidth cs ts es) es
  | .empty => some .keyNotFound

/-- `checkRequestOp(u, n)` of each `u`, in order: the first error. -/
def opsCheck (n : Int) : List ReqOp → Option CheckErr
  | [] => none
  | u :: us =>
    match opCheck n u with
    | some e => some e
    | none => opsCheck n us
end

/-- **`checkTxnRequest(r, n)`** of the transaction with comparisons `cs` and branches `ts`,
`es`. -/
def txnCheck (n : Int) (cs : List CmpModel) (ts es : List ReqOp) : Option CheckErr :=
  opCheck n (.txn cs ts es)

def requestOpOk (n : Int) (u : ReqOp) : Prop := opCheck n u = none
def txnReqOk (maxTxnOps : Int) (cs : List CmpModel) (ts es : List ReqOp) : Prop :=
  txnCheck maxTxnOps cs ts es = none

/-! ## `checkIntervals` -/

/-- `NewStringAffinePoint(k)`: `[k, k + "\x00")`. -/
def pointIvl (k : GoString) : adt.IvlS := (k, k ++ [W8 0])

/-- A delete's interval: `NewStringAffinePoint(Key)` for an empty range end,
`NewStringAffineInterval(Key, RangeEnd)` otherwise (`"\x00"` included: the empty `[k, "\x00")`). -/
def delIvl (o : OpFull) : adt.IvlS :=
  if o.base.rangeEnd = [] then pointIvl o.key else (o.key, o.base.rangeEnd)

/-- `dels.Intersects(NewStringAffinePoint(k))`: some interval of `ds` overlaps the point `k`. -/
def hits (ds : List adt.IvlS) (k : GoString) : Bool :=
  ds.any (fun d => decide (adt.ivlCmp (pointIvl k) d = 0))

/-- `Union`'s interval `NewStringAffineInterval("\x00", "")`: `["\x00", +∞)`. -/
def unionIvl : adt.IvlS := ([W8 0], [])

/-- The intervals `dels.Union(ds, unionIvl)` inserts: those `Visit(unionIvl)` visits. -/
def unionSel (ds : List adt.IvlS) : List adt.IvlS :=
  ds.filter (fun d => decide (adt.ivlCmp unionIvl d = 0))

/-- The level's deletes, in order (the first loop). -/
def levelDels : List ReqOp → List adt.IvlS
  | [] => []
  | .delete o :: us => delIvl o :: levelDels us
  | _ :: us => levelDels us

/-- The level's put keys, in order (the last loop). -/
def levelPuts : List ReqOp → List GoString
  | [] => []
  | .put o :: us => o.key :: levelPuts us
  | _ :: us => levelPuts us

/-- A nested transaction's two `checkIntervals` results (puts and deletes of each branch). -/
structure NestRes where
  putsThen : List GoString
  delsThen : List adt.IvlS
  putsElse : List GoString
  delsElse : List adt.IvlS

/-- The second loop's step for one nested transaction, from the puts and deletes so far. -/
def nestStep : Option (List GoString × List adt.IvlS) → NestRes →
    Option (List GoString × List adt.IvlS)
  | none, _ => none
  | some (puts, dels), r =>
    if r.putsThen.any (fun k => decide (k ∈ puts) || hits dels k) then none
    else if r.putsElse.any (fun k => decide (k ∈ puts ++ r.putsThen ∧ k ∉ r.putsThen) ||
        hits dels k) then none
    else some (puts ++ r.putsThen ++ r.putsElse.filter (fun k => decide (k ∉ puts ++ r.putsThen)),
      dels ++ unionSel r.delsThen ++ unionSel r.delsElse)

/-- The last loop's step for one of the level's puts. -/
def putStep : Option (List GoString × List adt.IvlS) → GoString →
    Option (List GoString × List adt.IvlS)
  | none, _ => none
  | some (puts, dels), k => if decide (k ∈ puts) || hits dels k then none else some (puts ++ [k], dels)

/-- **`checkIntervals(ops)` given its nested transactions' results** `nest` (in order): the
level's deletes, the nested transactions' puts and deletes, the level's puts. -/
def ivFinish (ops : List ReqOp) (nest : List NestRes) : Option (List GoString × List adt.IvlS) :=
  (levelPuts ops).foldl putStep (nest.foldl nestStep (some ([], levelDels ops)))

/-- **The nested transactions' `checkIntervals` results** (both branches), in order: `none` if
one of them fails. -/
def ivNest : List ReqOp → Option (List NestRes)
  | [] => some []
  | .txn _ ts es :: rest =>
    match (ivNest ts).bind (ivFinish ts), (ivNest es).bind (ivFinish es), ivNest rest with
    | some (pT, dT), some (pE, dE), some r => some (⟨pT, dT, pE, dE⟩ :: r)
    | _, _, _ => none
  | _ :: rest => ivNest rest

/-- **`checkIntervals(ops)`**: `some (puts, dels)` (the map's keys and the tree's intervals) if
it returns `nil`, `none` if it returns `ErrGRPCDuplicateKey`. -/
def ivCheck (ops : List ReqOp) : Option (List GoString × List adt.IvlS) :=
  (ivNest ops).bind (ivFinish ops)

/-- **`checkIntervals(ops)` returns `nil`.** -/
def intervalsOk (ops : List ReqOp) : Prop := (ivCheck ops).isSome

/-! ## What the check is for (stated; unit 1) -/

mutual
/-- No delete has the range end `"\x00"` (a from-key delete), at any depth. -/
def ReqOp.noFromKeyDel : ReqOp → Prop
  | .delete o => o.base.rangeEnd ≠ [W8 0]
  | .txn _ ts es => ReqOp.noFromKeyDelL ts ∧ ReqOp.noFromKeyDelL es
  | _ => True

def ReqOp.noFromKeyDelL : List ReqOp → Prop
  | [] => True
  | u :: us => ReqOp.noFromKeyDel u ∧ ReqOp.noFromKeyDelL us
end

mutual
/-- The put keys of an operation, at any depth, both branches. -/
def ReqOp.allPuts : ReqOp → List GoString
  | .put o => [o.key]
  | .txn _ ts es => ReqOp.allPutsL ts ++ ReqOp.allPutsL es
  | _ => []

def ReqOp.allPutsL : List ReqOp → List GoString
  | [] => []
  | u :: us => ReqOp.allPuts u ++ ReqOp.allPutsL us
end

mutual
/-- The deletes' intervals of an operation, at any depth, both branches. -/
def ReqOp.allDels : ReqOp → List adt.IvlS
  | .delete o => [delIvl o]
  | .txn _ ts es => ReqOp.allDelsL ts ++ ReqOp.allDelsL es
  | _ => []

def ReqOp.allDelsL : List ReqOp → List adt.IvlS
  | [] => []
  | u :: us => ReqOp.allDels u ++ ReqOp.allDelsL us
end

/-- Two operations of a level, the first a nested transaction: no key it puts (at any depth)
is in a delete of the second (at any depth). -/
def sibOk (u v : ReqOp) : Prop :=
  match u with
  | .txn _ _ _ => ∀ k ∈ u.allPuts, hits v.allDels k = false
  | _ => True

mutual
/-- **No nested transaction puts a key a later sibling nested transaction deletes**, at every
level: the case `checkIntervals` does not check (it checks a nested transaction's puts against
the deletes of its level and of the earlier siblings only). -/
def ReqOp.siblingSafe : ReqOp → Prop
  | .txn _ ts es => ReqOp.siblingSafeL ts ∧ ReqOp.siblingSafeL es
  | _ => True

def ReqOp.siblingSafeL : List ReqOp → Prop
  | [] => True
  | u :: us => (∀ v ∈ us, sibOk u v) ∧ ReqOp.siblingSafe u ∧ ReqOp.siblingSafeL us
end

/-- **`intervals_ok_check` (stated here, proved by unit 1)**: a branch `ops` that passes
`checkIntervals` (`intervalsOk`), with no from-key delete and no later-sibling delete of a nested
put, run by the server at any state (`txn.srvOps`, whatever its comparisons choose), has
distinct put keys, none of them deleted: the condition of the txn package's
`keys_nodup_iff_check` (with `DelsPresent`, which the run gives, `NoDupKeysPerRev` of the
transaction's revision). Not a theorem yet: a `Prop` whose proof is unit 1's
(`check_gives_nodup`). Without the two exclusions it is false (the two issues). -/
def intervalsOkCheckStmt : Prop :=
  ∀ (ops : List ReqOp) (tops : List TxnOp) (s0 s : List EtcdKv) (r : w64),
    ReqOp.toTxnOps ops = some tops → ReqOp.noFromKeyDelL ops → ReqOp.siblingSafeL ops →
    intervalsOk ops →
    (txn.putKeysOf (txn.srvOps s0 r s tops).1).Nodup ∧
      ∀ k ∈ txn.putKeysOf (txn.srvOps s0 r s tops).1, k ∉ txn.delKeysOf (txn.srvOps s0 r s tops).1

end v3rpc
end EtcdGrove
end Perennial
