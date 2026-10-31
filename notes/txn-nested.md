# Nested transactions in the client's specs (`clientv3.OpTxn` under `Then`/`Else`, `Commit` with auth on)

**Status** (2026-10-31): the design below is approved (the user, 2026-10-30), in code, and **frozen**
("The freeze", below; branch `txn-nested`, off `lean` `51b0f7adad`, with `invoke-size` merged); the
new obligations are not proved yet. It was drafted spec-first (the `spec` skill), reviewed by the
`spec-reviewer` twice (round 1: findings 1-10; round 2: B1-B3, C1-C3), and every finding fixed.

## The freeze (2026-10-31)

The statements are approved (the user, 2026-10-30) and the wire model's axiom review
(`notes/axiom-review/txn-nested-wire.md`, branch `axiom/txn-nested-wire`: grpc `Invoke`'s send side
refuted, an unbounded encoded size) is resolved by `invoke-size`'s encoded-size premise, merged here
(`a095a3b5e5`) with its folds (`notes/invoke-size.md`, "What txn-nested must fold": D1 `reqOpAt`'s
put clause, S2/S4's leaf premise, L5's conjunct, R1 `client_txn_on`'s `hsz`, the auth-off
`txn.Commit`'s `txnSizeOk`, `txnBuilderSpecO`'s `Commit`). At the freeze the full build is green with
only the named stubs ("In code", below) as `sorry`s; `etc/tcb-report.py --check` matches the
baseline (the stubs the only new `sorry`s), every collection `--check` passes, `api-check`,
`gen-interface --check --layout` (0 new violations) pass.

**Frozen** (the exported statements; a change goes to the user):
- the specs `txn.Then.spec` (`Spec/go_etcd_io/etcd/client/v3/txn__Then.lean:28`), `txn.Else.spec`
  (`txn__Else.lean:28`), `Op.toRequestOp.spec`, `Op.isWrite.spec`, `Op.toTxnRequest.spec`, and the
  corollaries `txn.Then.spec_plain`/`txn.Else.spec_plain` (`client/v3/TxnPlain.lean`);
- the vocabulary D1 (`reqOpAt`, `reqOpsAt`, `txnReqFieldsAt`), D2 (`txnWireOk`, `delWireAtT`,
  `delWiresAtT`), N1 (`OpT.wire`, `OpT.isWrite`), D3 (`etcdTxnSpecOn`), D4 (`txnUpdAtOn`),
  `txnNestOk`;
- R1 `client_txn_on` (`Proof/go_etcd_io/etcd/client/v3/ResultsOn.lean:319`);
- the laws the other packages use: `reqPerms_irrTxn_put`, `reqPerms_irrTxn_nestedPut`
  (`KVServiceOn.lean:180`; authkv's), `txnAuthOn_write`, `txnUpdAtOn_write`, `txnNestOk_of_plain`,
  `opTAtC_leaf`, `opTAtC_opTxn`, `opsTAt_nil`, `opsTAt_of_list`, `opsTAt_one`.

**Frozen pending** (internals whose only users are still stubs; final once those proofs are in):
`OpT.wire_txnOp`, `OpT.wireL_txnOps`, `OpT.txnOp_leaves`, `reqOpAt_txn`, `reqOpsAt_index` (users:
`Then`/`Else`, `toRequestOp`, `toTxnRequest`); `txnReadonly_plain`, `txnSibSafeL_of_noDel`
(`txnNestOk_of_plain`'s); `v3rpc.inRange_of_hits`, `siblingSafeL_of_model` (the handler's sibling
fact); `delCount_toTxnOps`, `delWiresAtT_reqOpsWire`, `txnReq_of_requestIs` (the bridge).

## The user's decisions (2026-10-30)

- **Q1** (approval): D1/D2 (the trusted wire model of `*pb.TxnRequest`), D3 (the meaning of the
  auth-on registrations), R1/D4 (the client's auth-on `Commit`), S1-S4 (the linked specs): approved
  as drafted.
- **Q2**: the auth-off `Commit` stays plain-only, a recorded scope restriction (`notes/decisions.md`,
  "Nested transactions with auth on only"; the text is in "The auth-off side", below).
- **Q3**: keep the `spec_plain` corollaries (S1′).
- **Q4**: the `axiom` skill reviews the stronger `pbTxnRequest` wire model with grpc's `Invoke` after
  the statements are in code (open: protobuf-go's unmarshal recursion limit, stack depth on a deep
  tree, the `2 ^ 63` delete bound on the decoded side).
- **Q5** (`txnNestOk` over the model or over the handler's `ReqOp`s; one sibling predicate in the
  server's `kvDepPre`) and **Q7** (moving `OpT`/`opTAtC`/`opsTAt` from `cache/v3/InvEtcdTxnOwn.lean`
  to the client): not now.
- **Q6** (authkv's `opShapeOk` needs a nested case for `kvShapeAll_irrTxn`): authkv's.

## In code (2026-10-30, branch `txn-nested`)

Every statement below is in code; each proof whose statement is new or changed and is not a
trivial adaptation is `sorry -- txn-nested: prove after freeze` (where it replaces a proof, its first
line says where the old one is: `git show 51b0f7adad:<path>`). The named stubs:

- specs' proofs: `txn.Then.wp_proof`, `txn.Else.wp_proof`, `Op.toRequestOp.wp_proof`,
  `Op.isWrite.wp_proof` (each replacing a proof), `Op.toTxnRequest.wp_proof` (new);
  `txn.Then.spec_plain`, `txn.Else.spec_plain` (`client/v3/TxnPlain.lean`);
- `InvKVConn.lean`: `OpT.wire_txnOp`, `OpT.wireL_txnOps`, `OpT.txnOp_leaves` (L5), `reqOpAt_txn`,
  `reqOpsAt_index` (L6);
- `cache/v3/InvEtcdTxnOwn.lean`: `opTAtC_leaf` (L2), `opTAtC_opTxn` (L1), `opsTAt_nil`,
  `opsTAt_of_list` (L3), `opsTAt_one` (L15);
- `KVService.lean`: `txnReadonly_plain` (L9); `KVServiceOn.lean`: `txnNestOk_of_plain`,
  `txnSibSafeL_of_noDel` (L8), `txnAuthOn_write`, `txnUpdAtOn_write` (L13), `reqPerms_irrTxn_put`,
  `reqPerms_irrTxn_nestedPut` (L10);
- `v3rpc/CheckNodup.lean`: `inRange_of_hits`; `ServedOn.lean`: `siblingSafeL_of_model` (L7);
- `Results.lean`: `delWiresAtT_reqOpsWire` (L12), `delCount_toTxnOps` (its plain premise dropped) and
  `txnReq_of_requestIs` (its `hp` dropped), each replacing a proof.

Proved as trivial adaptations: `reqOpsAt_nil`, `reqOpsAt_snoc` (structural `reqOpsAt`), `opWire_txn`
(L14), the persistence of `reqOpAt`/`reqOpsAt`/`txnReqFieldsAt`, `etcd_txnHandlerOn` (no `hp`; the
sibling and no-cut facts from `txnNestOk` by L7), `client_txn_on` (R1), `txnInModel_of` (the gated
`txnModelIn`), `etcd_txnHandlerOk` (passes `fun _ => hin`); `cmpsAt_nil` moved to `InvCmp.lean` with
its proof. The ten plain `Then`/`Else` calls on this branch (`KMTxn`, `ServerKVTxn`, `linkvtxn`'s
`callTxn`, kubernetes' `OptimisticPut`/`OptimisticDelete`) take `v3.txn.wp_Then_plain`/`wp_Else_plain`
(authkv's `Work` is on another branch). The client's `Link.lean` (regenerated) links
`Op.toTxnRequest` and gives `toRequestOp` its two new callees (`Cmp.Clone`, `Cmp.GetCompare`).

Departures from the text below:
- `reqOpAt_txn` (the nested case of `reqOpAt` through `txnReqFieldsAt`, an unfolding law) and
  `OpT.wireL_txnOps` (L5's list version, which the draft mentions in words) are stated as lemmas.
- L3's `opListAtC_cons`/`_nil` and the move of the leasing's `opListAtC_length`/`_get`/`_append`/`_drop`
  beside `opListAtC` are left to the proofs (the stubbed `Then` proof is their only user).
- `reqOp_of_requestOp`/`reqOps_of_requestOps`, `reqOpsWire_of_delWireAt` and `delWireAt` (the old
  bridge's internals, `Results.lean`) are kept as they are; the proof of `txnReq_of_requestIs`
  generalizes or replaces them.
- `txnWireOk_top` is not added (no proof wants it; D2 says "only if some proof still wants it").

## What changes

| # | Item | Kind | Change |
|---|---|---|---|
| S1 | `txn.Then.spec`, `txn.Else.spec` | linked (`v3.txn.wp_Then`, `wp_Else`) | operands are `OpT` trees (`opsTAt sl ts`, `OpT.txnOps ts = some ops`) instead of plain ops (`opsAt sl os`, `os.map txnOpOf = ops.map some`) |
| S2 | `Op.toRequestOp.spec` | linked | an `OpT` tree whose leaves are gets/puts/deletes, post `reqOpAt p (OpT.wire t)` (was: a leaf, `reqOpAt p (leafWire o)`) |
| S3 | `Op.isWrite.spec` | linked | an `OpT` tree, returns `OpT.isWrite t` (was: a leaf with `o.t ≠ 4`, `decide (o.t ≠ 1)`) |
| S4 | `Op.toTxnRequest.spec` | NEW spec + link entry | the nested request of an `OpTxn` tree (`Op.toTxnRequest` is translated, so far unverified) |
| S5 | `OpTxn.spec` | unchanged | the tree comes from a law (L1), not from the spec |
| D1 | `reqOpAt p (.txn …)` | definition inside the TRUSTED wire model `pbTxnRequest.send` | `False` → the nested `*pb.TxnRequest`, recursively; `reqOpsAt` becomes structural (mutual with `reqOpAt`) |
| D2 | `txnWireOk r t` | definition inside the TRUSTED wire model `pbTxnRequest.recv` | the delete wire fact at every depth (was: top-level deletes only), client-side recursive form |
| D3 | `etcdTxnSpecOn` | definition, the meaning of the registrations in `etcd_kv_served_on`, `etcd_kv_auth_served_on`, `etcd_kv_auth_served_onA` (and so of every result built on them) | drops `TxnModel.plain t`; `txnModelIn t` only if read-only; writing disjunct gains `txnNestOk t` |
| D4 | `txnUpdAtOn` | definition in `client_txn_on`'s statement | writing disjunct gains `txnNestOk t` |
| R1 | `client_txn_on` | client-facing result (`ResultsOn.lean`) | drops `hp : TxnModel.plain (txnWireOf b.model)`; `hin` only if read-only |
| N1 | `OpT.wire`, `OpT.isWrite` | new definitions (client, `InvKVConn.lean`) | trees' wire model and write flag |
| N1' | `delWireAtT`, `delWiresAtT` | new definitions (client, `InvKVConn.lean`) | D2's recursive delete fact |
| N2 | `opPutKeys`, `opDelOps` | new definitions (client, `KVServiceOn.lean`) | puts' keys / deletes, at any depth |
| N3 | `txnSibSafe`, `txnSibSafeL` | new definitions (client, `KVServiceOn.lean`) | no nested put a later sibling's delete range contains (model's `inRange`) |
| N4 | `txnNestOk` | new definition (client, `KVServiceOn.lean`) | a writing transaction's nested shape: no get cut early at any depth, sibling-safe |
| L* | laws | new | listed below |
| — | auth-off side (`etcdTxnSpec`, `txn.Commit.spec`, `client_txn_any`) | text unchanged; `etcdTxnSpec`'s meaning moves with D1/D2 (it is typed over `pbTxnRequest`) and `etcd_txnHandlerOk` (`Results.lean:1339`) is re-proved over the generalized bridge | keeps `TxnModel.plain`: a recorded scope restriction (decisions entry below; Q2) |

Statements needing the user's approval (repository policy):
- the trust base: D1, D2 (the wire model of `*pb.TxnRequest` the transport axioms are stated over).
  Through D1 the meaning of every spec stated over `txnReqAt` or `txnObjAt` moves too:
  `kVClient.Txn.spec` (`Spec/go_etcd_io/etcd/api/v3/etcdserverpb/kVClient__Txn.lean`),
  `retryKVClient.Txn.spec`, `kv.Txn.spec`, `txn.If.spec`/`Then`/`Else`/`Commit.spec`/`Commit.specG`/`specM`;
  through D2 the meaning of both registrations, `etcdTxnSpec` (off) and `etcdTxnSpecOn` (on);
- D3 (the meaning of exported registrations), R1, D4, S1–S4 (linked specs).
The one new premise on a statement with clients is `txnNestOk` in the writing disjunct of D3/D4
(presented on its own in "The new premise", below).

## The code

`client/v3/txn.go` (pinned `upamanyus/etcd` `goose-lean`):

```go
func (txn *txn) Then(ops ...Op) Txn {
	txn.mu.Lock(); defer txn.mu.Unlock()
	if txn.cthen { panic("cannot call Then twice!") }
	if txn.celse { panic("cannot call Then after Else!") }
	txn.cthen = true
	for _, op := range ops {
		txn.isWrite = txn.isWrite || op.isWrite()
		txn.sus = append(txn.sus, op.toRequestOp())
	}
	return txn
}
// Else: the same into txn.fas, panics only if celse.
func (txn *txn) Commit() (*TxnResponse, error) {
	... r := &pb.TxnRequest{Compare: txn.cmps, Success: txn.sus, Failure: txn.fas}
	resp, err = txn.kv.remote.Txn(txn.ctx, r, txn.callOpts...) ...
}
```

`client/v3/op.go`:

```go
func (op Op) toTxnRequest() *pb.TxnRequest {
	thenOps := make([]*pb.RequestOp, len(op.thenOps))
	for i, tOp := range op.thenOps { thenOps[i] = tOp.toRequestOp() }
	elseOps := make([]*pb.RequestOp, len(op.elseOps))
	for i, eOp := range op.elseOps { elseOps[i] = eOp.toRequestOp() }
	cmps := make([]*pb.Compare, len(op.cmps))
	for i := range op.cmps { cmp := op.cmps[i].Clone(); cmps[i] = cmp.GetCompare() }
	return &pb.TxnRequest{Compare: cmps, Success: thenOps, Failure: elseOps}
}
func (op Op) toRequestOp() *pb.RequestOp {
	switch op.t {
	case tRange: ...; case tPut: ...; case tDeleteRange: ...
	case tTxn: return &pb.RequestOp{Request: &pb.RequestOp_RequestTxn{RequestTxn: op.toTxnRequest()}}
	default: panic("Unknown Op")
	}
}
func (op Op) isWrite() bool {
	if op.t == tTxn {
		for _, tOp := range op.thenOps { if tOp.isWrite() { return true } }
		for _, tOp := range op.elseOps { if tOp.isWrite() { return true } }
		return false
	}
	return op.t != tRange
}
func OpTxn(cmps []Cmp, thenOps []Op, elseOps []Op) Op {
	clonedCmps := make([]Cmp, len(cmps))
	for i := range cmps { clonedCmps[i] = cmps[i].Clone() }
	return Op{t: tTxn, cmps: clonedCmps, thenOps: thenOps, elseOps: elseOps}
}
```

Server: `IsTxnReadonly` is false for a nested transaction (a top-level op without a `RequestRange`);
`checkTxnRequest`/`checkIntervals` (`v3rpc/key.go`) recurse into nested transactions and reject
duplicate puts and put/delete overlaps, except a put in a nested transaction vs a delete in a later
sibling (`issues/etcd-txn-check-intervals-sibling.md`, known upstream); `checkTxnReqsPermission`
recurses (`opPerms (.txn …)`, `KVAuthModel.lean`). The server's handler proof (`txn_end_to_end_on`)
already handles nested transactions: its premise `kvDepPre` (`v3rpc/ServerKV.lean:293`) for a writing
transaction is `txn.txnPlain t ∧ txnNoZeroEnd t ∧ ReqOp.siblingSafeL ts ∧ ReqOp.siblingSafeL es ∧
txn.OpsNoCut t.thenOps ∧ txn.OpsNoCut t.elseOps`.

What is plain-only today, and why:
- client: `opsAt`/`txnOpOf` (Then/Else), `Op.isWrite.spec`/`toRequestOp.spec` (`o.t ≠ 4`),
  `reqOpAt _ (.txn …) = False`;
- the trusted wire model `pbTxnRequest`: `send` via `reqOpAt` (nested = `False`), `recv`'s
  `txnWireOk` (top-level deletes only);
- the bridge from the decoded copy to the handler's request (`client/v3/Results.lean`,
  `reqOp_of_requestOp`, `txnReq_of_requestIs`: `hp : TxnModel.plain t`) and the handler's
  `siblingSafeL_of_flat`, `opsNoCut_of_flat` (`ServedOn.lean` `etcd_txnHandlerOn`): this is the only
  use of `TxnModel.plain` in `etcdTxnSpecOn`.

`txn.txnPlain` (`txn/TxnRun.lean:534-549`) already admits nesting (`.txn _ ts es => opsPlain ts ∧
opsPlain es`); it is not to widen. `TxnModel.plain` (`client/v3/KVService.lean:66-72`) is the one
that excludes nesting; the design removes it from the auth-on path only.

## New definitions

### N1 (client, `InvKVConn.lean`, beside `leafWire`/`opWire`)

```lean
mutual
/-- **The wire model of an operation tree** (`Op.toRequestOp`'s request, as the server reads it): a
leaf's `leafWire`, a nested transaction's comparisons and its branches' wire models. -/
def OpT.wire : OpT → TxnOp
  | .leaf o => leafWire o
  | .txn _ cs ts es => .txn cs (OpT.wireL ts) (OpT.wireL es)

def OpT.wireL : List OpT → List TxnOp
  | [] => []
  | t :: ts => t.wire :: OpT.wireL ts
end

mutual
/-- **`op.isWrite()` of an operation tree**: a leaf not a range; a nested transaction with a
writing operation in either branch. -/
def OpT.isWrite : OpT → Bool
  | .leaf o => decide (o.t ≠ W64 1)
  | .txn _ _ ts es => OpT.isWriteL ts || OpT.isWriteL es

def OpT.isWriteL : List OpT → Bool
  | [] => false
  | t :: ts => t.isWrite || OpT.isWriteL ts
end
```

### N2, N3, N4 (client, `KVServiceOn.lean`: used only by the auth-on statements; no server module changes)

```lean
mutual
/-- The keys an operation puts, at any depth, both branches. -/
def opPutKeys : TxnOp → List GoString
  | .put k _ _ => [k]
  | .putKeep k _ => [k]
  | .putIgnVal k _ => [k]
  | .txn _ ts es => opsPutKeys ts ++ opsPutKeys es
  | _ => []
def opsPutKeys : List TxnOp → List GoString
  | [] => []
  | op :: ops => opPutKeys op ++ opsPutKeys ops
end

mutual
/-- The deletes of an operation, at any depth, both branches. -/
def opDelOps : TxnOp → List OpFull
  | .delete o => [o]
  | .txn _ ts es => opsDelOps ts ++ opsDelOps es
  | _ => []
def opsDelOps : List TxnOp → List OpFull
  | [] => []
  | op :: ops => opDelOps op ++ opsDelOps ops
end
```

```lean
/-- A nested transaction `u` puts no key (at any depth) that a delete of `v` (at any depth)
covers, in the model's sense of a range (`inRange`: the key alone, from the key on for `[0]`,
`[key, rangeEnd)` otherwise). Constrains nothing unless `u` is a nested transaction. -/
def sibOkT (u v : TxnOp) : Prop :=
  match u with
  | .txn _ _ _ => ∀ k ∈ opPutKeys u, ∀ o ∈ opDelOps v, inRange o.key o.base.rangeEnd k = false
  | _ => True

mutual
/-- **No nested transaction puts a key a later sibling deletes**, at every level (the model's
reading of the server's `ReqOp.siblingSafe`; `issues/etcd-txn-check-intervals-sibling.md`: the case
`checkIntervals` does not check). -/
def txnSibSafe : TxnOp → Prop
  | .txn _ ts es => txnSibSafeL ts ∧ txnSibSafeL es
  | _ => True
def txnSibSafeL : List TxnOp → Prop
  | [] => True
  | u :: us => (∀ v ∈ us, sibOkT u v) ∧ txnSibSafe u ∧ txnSibSafeL us
end

/-- **A writing transaction's nested shape** (a premise; what the server's handler needs of a
writing transaction beyond `txn.txnPlain` and `txnNoZeroEnd`, inherited from its `kvDepPre`, D19c):
no get at any depth a sort cut early by a limit (`txn.OpsNoCut`,
`issues/etcd-range-sort-none-limit.md`), and no nested transaction putting a key a later sibling
deletes (`txnSibSafeL`). A transaction of plain operations within the model has it
(`txnNestOk_of_plain`). -/
def txnNestOk (t : TxnModel) : Prop :=
  txn.OpsNoCut t.thenOps ∧ txn.OpsNoCut t.elseOps ∧ txnSibSafeL t.thenOps ∧ txnSibSafeL t.elseOps
```

`sibOkT` is stricter than the server's `sibOk` only at empty keys, which the server's checks reject
(`ErrGRPCEmptyKey`; L7). There is one definition of sibling safety in the client's statements (this
one, over the model); the handler's `v3rpc.ReqOp.siblingSafeL` stays the server's internal reading, reached by L7 in the bridge
(`client/v3/Results.lean`). Restating `kvDepPre` over the model and dropping the `ReqOp` one is a
server-side clean-up outside this change (Q5).

## The vocabulary changes (D1, D2: the trusted wire model)

### D1 `reqOpAt`, `reqOpsAt` (`InvKVConn.lean:406-432`)

Old:

```lean
def reqOpAt (p : Loc) (op : TxnOp) : IProp GF :=
  match op with
  | .get o => …  | .delete o => …
  | .txn _ _ _ => iprop(False)
  | _ => … (a put)
def reqOpsAt (ps : List Loc) (ops : List TxnOp) : IProp GF :=
  iprop(⌜ps.length = ops.length⌝ ∗
    □ ∀ (i : Nat) (p : Loc) (op : TxnOp), ⌜ps[i]? = some p⌝ -∗ ⌜ops[i]? = some op⌝ -∗ reqOpAt p op)
```

New (the get, delete, put cases unchanged):

```lean
mutual
def reqOpAt (p : Loc) : TxnOp → IProp GF
  | .get o => (as before)
  | .delete o => (as before)
  | .txn cs ts es => iprop(⌜p ≠ null⌝ ∗ ∃ (w r : Loc) (csl ssl fsl : GoSlice)
        (cps sps fps : List Loc),
      structFieldRef etcdserverpb.RequestOp go!"Request" p ↦□
        (interface.mkOk (go.GoType.PointerType etcdserverpb.RequestOp_RequestTxn.ty) #w :
          GoInterface) ∗
      structFieldRef etcdserverpb.RequestOp_RequestTxn go!"RequestTxn" w ↦□ r ∗ ⌜r ≠ null⌝ ∗
      structFieldRef etcdserverpb.TxnRequest go!"Compare" r ↦□ csl ∗ csl ↦*□ cps ∗
        comparesAt cps cs ∗
      structFieldRef etcdserverpb.TxnRequest go!"Success" r ↦□ ssl ∗ ssl ↦*□ sps ∗
        reqOpsAt sps ts ∗
      structFieldRef etcdserverpb.TxnRequest go!"Failure" r ↦□ fsl ∗ fsl ↦*□ fps ∗
        reqOpsAt fps es)
  | op => (as before: a put)

def reqOpsAt : List Loc → List TxnOp → IProp GF
  | [], [] => iprop(True)
  | p :: ps, op :: ops => iprop(reqOpAt p op ∗ reqOpsAt ps ops)
  | _, _ => iprop(False)
end
```

(`reqOpsAt` becomes structural: Lean's structural recursion over the nested `List TxnOp`; the index
form is a law, `reqOpsAt_index`, L6.) Docstring: "a nested transaction's request (`Op.toTxnRequest`'s)
with its comparisons and operations, recursively".

`txnReqAt` (the sender's message, `pbTxnRequest.send`) is unchanged in text; its meaning grows with
`reqOpAt`.

### D2 `txnWireOk` (`InvKVConn.lean:513`)

Old: the delete count bound per branch, and for each *top-level* delete of `Success`/`Failure`, its
`RangeEnd` `nil` or not empty.

New (round 1: the client-side form, recursive over `TxnOp` as `delCountT` already is; no `v3rpc`
import into `InvKVConn`, whose closure would otherwise grow from ~200 to ~650 modules):

```lean
mutual
/-- **The deletes of the operation `op` at `p` are as decoded** (persistent): a delete's `RangeEnd`
`nil` or not empty; a nested transaction's, recursively, through its `Success` and `Failure`.
Stated over the fields' points-tos (whatever they hold), as a wand, as `v3rpc.reqOpWire` is. -/
def delWireAtT (p : Loc) : TxnOp → IProp GF
  | .delete _ => iprop(□ ∀ (w d : Loc) (esl : GoSlice),
      structFieldRef etcdserverpb.RequestOp go!"Request" p ↦□
        (interface.mkOk (go.GoType.PointerType etcdserverpb.RequestOp_RequestDeleteRange.ty) #w :
          GoInterface) -∗
      structFieldRef etcdserverpb.RequestOp_RequestDeleteRange go!"RequestDeleteRange" w ↦□ d -∗
      structFieldRef etcdserverpb.DeleteRangeRequest go!"RangeEnd" d ↦□ esl -∗
      ⌜esl = slice.nil ∨ esl.len ≠ W64 0⌝)
  | .txn _ ts es => iprop(□ ∀ (w r : Loc) (ssl fsl : GoSlice) (sps fps : List Loc),
      structFieldRef etcdserverpb.RequestOp go!"Request" p ↦□
        (interface.mkOk (go.GoType.PointerType etcdserverpb.RequestOp_RequestTxn.ty) #w :
          GoInterface) -∗
      structFieldRef etcdserverpb.RequestOp_RequestTxn go!"RequestTxn" w ↦□ r -∗
      structFieldRef etcdserverpb.TxnRequest go!"Success" r ↦□ ssl -∗ ssl ↦*□ sps -∗
      structFieldRef etcdserverpb.TxnRequest go!"Failure" r ↦□ fsl -∗ fsl ↦*□ fps -∗
      delWiresAtT sps ts ∗ delWiresAtT fps es)
  | _ => iprop(True)

def delWiresAtT : List Loc → List TxnOp → IProp GF
  | p :: ps, op :: ops => iprop(delWireAtT p op ∗ delWiresAtT ps ops)
  | _, _ => iprop(True)
end

/-- **What the decoding gives of a transaction request's deletes** (`r`, the server's copy;
persistent): every delete's `RangeEnd`, at every depth, `nil` or not empty (protobuf-go decodes an
empty proto3 `bytes` field as `nil`, at any depth), and the deletes, at every depth, fewer than
`2 ^ 63` in each branch (the decoded copy is a tree parsed from one byte slice, each delete at least
two bytes of it). -/
def txnWireOk (r : Loc) (t : TxnModel) : IProp GF :=
  iprop(⌜delCountT t.thenOps < 2 ^ 63 ∧ delCountT t.elseOps < 2 ^ 63⌝ ∗
    □ ∀ (ssl fsl : GoSlice) (sps fps : List Loc),
      structFieldRef etcdserverpb.TxnRequest go!"Success" r ↦□ ssl -∗ ssl ↦*□ sps -∗
      structFieldRef etcdserverpb.TxnRequest go!"Failure" r ↦□ fsl -∗ fsl ↦*□ fps -∗
      delWiresAtT sps t.thenOps ∗ delWiresAtT fps t.elseOps)
```

(The old form, a disjunction over `Success`/`Failure` and an index into the slice, says the delete
fact at every index whose wire holds a delete; the new one at the model's deletes. They agree given
the decoded copy's denotation: `txnWireOk_top : txn.txnRequestIs r t ∗ txnWireOk r t ⊢ (old form)`,
only if some proof still wants it; the bridge uses L12.) The bridge maps it to the handler's
`v3rpc.txnReqWire r ts es` for `v3rpc.txnModelOf t.cmps ts es = some t` (L12: `delWiresAtT ps ops ⊢
v3rpc.reqOpsWire ps us` when `ReqOp.toTxnOps us = some ops`, and `delCount_toTxnOps` without its
plain premise), replacing `reqOpsWire_of_delWireAt`/`reqNotTxn_of_toTxnOps`.

Rejected (round 0's D2): `txnWireOk r t := □ ∀ ts es, ⌜v3rpc.txnModelOf t.cmps ts es = some t⌝ -∗
v3rpc.txnReqWire r ts es`: no mirrored definition, but the trusted `recv` would be read through the
gRPC handler's internal predicates, and every client module would import `v3rpc`.

Soundness of D1/D2 as a trusted claim (for the `axiom` skill, Q4). `send` now holds of a request
with nested transactions built in memory, possibly sharing a nested `*pb.TxnRequest` between
branches (a DAG; a cyclic graph cannot satisfy the finite `reqOpAt`). The claim is about the
*decoded* copy: a tree parsed from one byte slice, denoting the same `t` (`txn.txnRequestIs`), every
delete's `RangeEnd` `nil`-or-non-empty (proto3 `bytes` decoding, at every depth), fewer than `2 ^ 63`
deletes per branch (each at least two bytes of the parsed slice; the server also caps the request at
`MaxRequestBytesWithOverhead`, `v3rpc/grpc.go:74`). What the axiom review must still look at:
protobuf-go's unmarshal recursion limit (a deeper request is refused with a status error, covered by
`txnCallOut`'s error branch) and Go stack exhaustion on a very deep tree (outside the model, as memory
exhaustion is). Still a strengthening of a trusted statement (watch-auth principle), listed with the
collections that rest on it (Q4).

## The specs (S1–S4)

### S1 `txn.Then.spec`

Old:

```lean
abbrev txn.Then.spec : Prop :=
  ∀ (tp : Loc) (addr : List GoString) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (b : TxnBuild) (sl : GoSlice) (os : List OpFull) (ops : List TxnOp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ txnObjAt tp addr ci cd b ∗
      opsAt sl os ∗ ⌜os.map txnOpOf = ops.map some ∧ b.cthen = false ∧ b.celse = false⌝ }}
    (App (Val (tp @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.txn.ty @!! go!"Then")) (Val #sl))
  {{ RET #(interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.txn.ty) #tp : GoInterface);
      txnObjAt tp addr ci cd { b with model := { b.model with thenOps := b.model.thenOps ++ ops }, cthen := true } }}
```

New:

```lean
/-- `t.Then(ops...)` (before `Else`, once; else it panics) with operations `ts`, each a plain
operation or a nested transaction (`OpTxn`), whose transaction operations are `ops` (`OpT.txnOps`:
every get at revision `0`, every put one etcd accepts): their requests (`Op.toRequestOp`, nested
ones recursively) appended, `cthen` set; returns the builder as a `Txn`. -/
abbrev txn.Then.spec : Prop :=
  ∀ (tp : Loc) (addr : List GoString) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (b : TxnBuild) (sl : GoSlice) (ts : List OpT) (ops : List TxnOp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ txnObjAt tp addr ci cd b ∗
      opsTAt sl ts ∗ ⌜OpT.txnOps ts = some ops ∧ b.cthen = false ∧ b.celse = false⌝ }}
    (App (Val (tp @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.txn.ty @!! go!"Then")) (Val #sl))
  {{ RET #(interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.txn.ty) #tp : GoInterface);
      txnObjAt tp addr ci cd { b with model := { b.model with thenOps := b.model.thenOps ++ ops }, cthen := true } }}
```

The triple is exactly `txnBuilderSpecO`'s `Then` (`cache/v3/InvEtcdTxnOwn.lean:455`, the leasing KV's
assumption of the client) at `B := txnObjAt tp addr ci cd`. `txnObjAt` is unchanged: its `sus`
slice holds `reqOpsAt sps (b.model.thenOps.map opWire)`, now with nested requests (D1).

### S1 `txn.Else.spec`

Old: as `Then` but `elseOps`, `celse`, premise `b.celse = false` only. New: the same replacement
(`opsTAt sl ts ∗ ⌜OpT.txnOps ts = some ops ∧ b.celse = false⌝`), post unchanged.

### S1′ the corollaries for plain operations (round 1, finding 6)

Variant statements as corollaries of the one proof (PRINCIPLES, "One spec per function"), stating
the old specs exactly, so that the 12 existing calls (all plain) change only the lemma's name:

```lean
/-- `txn.Then.spec` at plain operations (the statement until the nested generalization). -/
abbrev txn.Then.specPlain : Prop := (the old `txn.Then.spec`, verbatim, above)
theorem txn.Then.spec_plain (h : txn.Then.spec (GF := GF) (hG := hG)) :
    txn.Then.specPlain (GF := GF) (hG := hG)   -- from L4: `opsAt_leaves`, `txnOps_leaves`
-- and `txn.Else.specPlain`, `txn.Else.spec_plain` likewise
```

in a client file outside the link (e.g. `Proof/go_etcd_io/etcd/client/v3/TxnPlain.lean`, importing
`Link`, never imported by it), with `v3.txn.wp_Then_plain := txn.Then.spec_plain v3.txn.wp_Then`. To
check when done: `etc/gen-link.py` and `etc/verified-code.py` do not count `wp_Then_plain` as a second
proof of `Then` (it is not in a `Link.lean`/`Results.lean`).

### S2 `Op.toRequestOp.spec`

Old:

```lean
abbrev Op.toRequestOp.spec : Prop :=
  ∀ (opv : go_etcd_io.etcd.client.v3.Op) (o : OpFull),
  {{ isPkgInit … ∗ opFullAt opv o ∗ ⌜o.t = W64 1 ∨ o.t = W64 2 ∨ o.t = W64 3⌝ }}
    (App (Val (opv @!! go_etcd_io.etcd.client.v3.Op.ty @!! go!"toRequestOp")) (Val #()))
  {{ (p : Loc), RET #p; reqOpAt p (leafWire o) }}
```

New:

```lean
/-- `op.toRequestOp()` of an operation tree `t` whose plain operations are gets, puts and deletes
(else it panics, `"Unknown Op"`): a new `*pb.RequestOp` wrapping the request of its kind, a nested
transaction's `toTxnRequest` (its comparisons cloned, its operations' requests, recursively),
holding (read-only) the tree's wire model (`OpT.wire`). -/
abbrev Op.toRequestOp.spec : Prop :=
  ∀ (opv : go_etcd_io.etcd.client.v3.Op) (t : OpT),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ opTAtC false opv t ∗
      ⌜∀ o ∈ t.leaves, o.t = W64 1 ∨ o.t = W64 2 ∨ o.t = W64 3⌝ }}
    (App (Val (opv @!! go_etcd_io.etcd.client.v3.Op.ty @!! go!"toRequestOp")) (Val #()))
  {{ (p : Loc), RET #p; reqOpAt p (OpT.wire t) }}
```

The old spec is the instance `t := .leaf o` (L2: `opTAtC false v (.leaf o) ⊣⊢ opFullAt v o ∗ ⌜o.t ≠ 4⌝`;
`OpT.wire (.leaf o) = leafWire o`; `(.leaf o).leaves = [o]`).

### S3 `Op.isWrite.spec`

Old: `opFullAt opv o ∗ ⌜o.t ≠ W64 4⌝` → `RET #(decide (o.t ≠ W64 1)); True`.

New:

```lean
/-- `op.isWrite()` of an operation tree: whether it is not a range, for a nested transaction
whether some operation of either branch writes (`OpT.isWrite`). -/
abbrev Op.isWrite.spec : Prop :=
  ∀ (opv : go_etcd_io.etcd.client.v3.Op) (t : OpT),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ opTAtC false opv t }}
    (App (Val (opv @!! go_etcd_io.etcd.client.v3.Op.ty @!! go!"isWrite")) (Val #()))
  {{ RET #(OpT.isWrite t); True }}
```

Old = instance `t := .leaf o` (L2, `OpT.isWrite (.leaf o) = decide (o.t ≠ W64 1)` by `rfl`).

### S4 `Op.toTxnRequest.spec` (new)

```lean
/-- `op.toTxnRequest()` of a nested transaction tree `.txn o cs ts es` (its plain operations gets,
puts and deletes): a new `*pb.TxnRequest` whose comparisons are clones of the `Op`'s (`cs`), and
whose `Success` and `Failure` hold the requests of `ts` and `es` (`Op.toRequestOp`'s), read-only:
the fields of `reqOpAt`'s nested case. -/
abbrev Op.toTxnRequest.spec : Prop :=
  ∀ (opv : go_etcd_io.etcd.client.v3.Op) (o : OpFull) (cs : List CmpModel) (ts es : List OpT),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      opTAtC false opv (.txn o cs ts es) ∗
      ⌜∀ x ∈ (OpT.txn o cs ts es).leaves, x.t = W64 1 ∨ x.t = W64 2 ∨ x.t = W64 3⌝ }}
    (App (Val (opv @!! go_etcd_io.etcd.client.v3.Op.ty @!! go!"toTxnRequest")) (Val #()))
  {{ (r : Loc), RET #r; ⌜r ≠ null⌝ ∗ txnReqFieldsAt r cs (OpT.wireL ts) (OpT.wireL es) }}
```

with `txnReqFieldsAt r cs ts es` the `*pb.TxnRequest`-fields part of `reqOpAt`'s nested case (factored
out of D1 so both use it: `reqOpAt p (.txn cs ts es) = ⌜p ≠ null⌝ ∗ ∃ w r, Request ↦□ … ∗ RequestTxn ↦□ r
∗ ⌜r ≠ null⌝ ∗ txnReqFieldsAt r cs ts es`; inside the mutual block).

**The mutual recursion and the link.** `toRequestOp` and `toTxnRequest` call each other; the link
(one proof per function, callees' specs as hypotheses) has no cycle form (`notes/decisions.md`, "The
recursion `appliedTo` → `Step`"). The proofs: `Op.toRequestOp.wp_proof (wp_toRangeRequest)
(wp_Clone) (wp_GetCompare)` by Löb induction (`iloeb`, as `btree.node.reset`), unfolding
`toTxnRequest`'s body at the `tTxn` case and using the induction hypothesis for the inner calls;
`Op.toTxnRequest.wp_proof (wp_toRequestOp) (wp_Clone) (wp_GetCompare)` from the former's spec.
`Op.isWrite.wp_proof` by Löb (self-recursion). `etc/link-lean-first*.txt`/`gen-link.py` gain the
callees; `toTxnRequest` becomes verified (`etc/verified-code.py`).

S4 has no caller today: `toRequestOp`'s Löb proof unfolds `toTxnRequest`'s body itself, so its body
is proved twice and `Op.toTxnRequest.wp_proof` exists for the accounting (and for `kv.Do` of a
transaction, a future caller). To check when it is done: that `gen-link.py` and `verified-code.py`
accept `toRequestOp` proved without `toTxnRequest`'s spec among its hypotheses although it calls it
(else: drop S4 and count `toTxnRequest` as verified through `toRequestOp`, if the scripts allow).

### S5 `OpTxn.spec` (unchanged)

```lean
abbrev OpTxn.spec : Prop :=
  ∀ (csl : GoSlice) (ms : List CmpModel) (tsl esl : GoSlice),
  {{ isPkgInit … ∗ cmpsAt csl ms }}
    (App (App (App (Val (@! go_etcd_io.etcd.client.v3.OpTxn)) (Val #csl)) (Val #tsl)) (Val #esl))
  {{ (op : go_etcd_io.etcd.client.v3.Op), RET #op; opFullAt op OpFull.txnInit ∗
      cmpsAt op.cmps' ms ∗ ⌜op.thenOps' = tsl ∧ op.elseOps' = esl⌝ }}
```

`OpTxn` reads neither operation slice; taking `opsTAt tsl ts ∗ opsTAt esl es` in its pre to return the
tree would add premises the code does not need. The tree is assembled by the law L1, which a caller
applies when it has the trees (the leasing KV's `userTxn_tree`, `InvLeasingCommitLemmas.lean:388`, is
L1's instance at leaves and becomes a one-line corollary).

## The auth-on server spec and `Commit` (D3, D4, R1)

### D3 `etcdTxnSpecOn` (`KVServiceOn.lean:99`)

Old:

```lean
def etcdTxnSpecOn (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (cid mid : w64) :
    GrpcSpecMd (GF := GF) pbTxnRequest pbTxnResponse :=
  fun md (t : TxnModel) (Φ : TxnRespM → IProp GF) =>
    iprop(⌜TxnModel.plain t ∧ txnModelIn t ∧ (txn.txnReadonly t = false →
        ∀ tw : txn.TxnModelW, tw.toModel = t → kvShapeAll (irrTxn tw))⌝ ∗
      ∃ Q : KVState → IProp GF,
      (⌜txn.txnReadonly t = true ∧ Q = fun _ => iprop(True)⌝ ∨
        (⌜txn.txnReadonly t = true ∧ txn.txnSerializable t = false⌝ ∗ kvReadAu γr.kv Q) ∨
        (⌜txn.txnReadonly t = false ∧ txn.txnPlain t ∧ txnNoZeroEnd t⌝ ∗
          v3rpc.kvOpAuOn s E ρ (auth.mdTokenOf md) (.txn t) Q)) ∗
      ∃ (c : w64) (F : mvcc.Log) (n : Nat), committedAtLeast γr c ∗
      mvcc.idxCert E.γ.idx F ∗ auth.authPubLbM E.authMode n ∗
      ∀ m : TxnRespM, txnReplied E ρ.rd γr c F t Q cid mid m -∗
        txnAuthOn s E ρ γr c n (auth.mdTokenOf md) t -∗ Φ m)
```

New (three edits: `TxnModel.plain t ∧` dropped; `txnModelIn t` only for a read-only transaction;
`∧ txnNestOk t` in the writing disjunct):

```lean
    iprop(⌜(txn.txnReadonly t = true → txnModelIn t) ∧ (txn.txnReadonly t = false →
        ∀ tw : txn.TxnModelW, tw.toModel = t → kvShapeAll (irrTxn tw))⌝ ∗
      ∃ Q : KVState → IProp GF,
      (⌜txn.txnReadonly t = true ∧ Q = fun _ => iprop(True)⌝ ∨
        (⌜txn.txnReadonly t = true ∧ txn.txnSerializable t = false⌝ ∗ kvReadAu γr.kv Q) ∨
        (⌜txn.txnReadonly t = false ∧ txn.txnPlain t ∧ txnNoZeroEnd t ∧ txnNestOk t⌝ ∗
          v3rpc.kvOpAuOn s E ρ (auth.mdTokenOf md) (.txn t) Q)) ∗
      (rest unchanged)
```

A read-only transaction is flat (`txnReadonly t = true` means every operation is a get: L9), so
dropping `TxnModel.plain` changes only the writing case. `txnModelIn` (gets at revision `0`, no
sort cut early: top level only) is used by the handler only through `txnInModel_of`, and
`v3rpc.txnInModel` constrains read-only transactions only (`ServerKV.lean:203-205`); for a writing one
its content is in `txn.txnPlain` (gets at revision `0`, every depth) and `txnNestOk` (`OpsNoCut`, every
depth), so it is gated (round 1, finding 3). Docstring: "a writing transaction may nest transactions
(plain, `txn.txnPlain`, at every depth; `txnNestOk`)".

The server's side (`etcd_txnHandlerOn`, `ServedOn.lean:452`) is re-proved: the bridge
`txnReq_of_requestIs` loses `hp` (`reqOp_of_requestOp`'s nested case by recursion: `txn.requestOpIs`
and `v3rpc.reqOpIs` have the same nested shape; `delCount_toTxnOps` loses its plain premise; the wire
part from D2 by L12), and `siblingSafeL_of_flat`/`opsNoCut_of_flat` are replaced by L7 and
`txnNestOk`'s `OpsNoCut`; `txnInModel_of` takes the gated `txnModelIn`. `etcd_kv_served_on`,
`etcd_kv_auth_served_on`, `etcd_kv_auth_served_onA` keep their text; their registration of
`etcdTxnSpecOn` now admits nested writing transactions (a stronger result). The auth-off handler
`etcd_txnHandlerOk` (`Results.lean:1339`) is re-proved over the same generalized bridge (its spec
`etcdTxnSpec` keeps `TxnModel.plain`, so its `siblingSafeL_of_flat`/`opsNoCut_of_flat` stay).

### D4 `txnUpdAtOn` (`KVServiceOn.lean:185`)

Old writing disjunct `⌜txn.txnReadonly t = false ∧ txn.txnPlain t ∧ txnNoZeroEnd t⌝ ∗ clientOpAuOn …`;
new `⌜txn.txnReadonly t = false ∧ txn.txnPlain t ∧ txnNoZeroEnd t ∧ txnNestOk t⌝ ∗ clientOpAuOn …`
(the read-only disjuncts unchanged).

### R1 `client_txn_on` (`ResultsOn.lean:309`)

Old premises: `(hp : TxnModel.plain (txnWireOf b.model)) (hin : txnModelIn (txnWireOf b.model))
(hsh : txn.txnReadonly (txnWireOf b.model) = false → ∀ tw, tw.toModel = txnWireOf b.model →
kvShapeAll (irrTxn tw))`.

New: `hp` dropped; `hin` gated on read-only; everything else (precondition, postcondition)
unchanged in text:

```lean
theorem client_txn_on (tp api conn : Loc) (addr : GoString) (s : Loc) (E : apply.AEnv GF)
    (ρ : ReqNames) (γr : ReadNames) (cid mid c : w64) (n : Nat) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (b : TxnBuild) (Q : KVState → IProp GF) (F : mvcc.Log)
    (hin : txn.txnReadonly (txnWireOf b.model) = true → txnModelIn (txnWireOf b.model))
    (hsh : txn.txnReadonly (txnWireOf b.model) = false →
      ∀ tw : txn.TxnModelW, tw.toModel = txnWireOf b.model → kvShapeAll (irrTxn tw)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
        txnObjAt tp [addr] ci cd b ∗ txnKvIs tp api ∗ kvObjAtC api conn [addr] ∗
        isGrpcRpcMd addr go!"/etcdserverpb.KV/Txn" (etcdTxnSpecOn s E ρ γr cid mid) ∗
        committedAtLeast γr c ∗ mvcc.idxCert E.γ.idx F ∗ auth.authPubLbM E.authMode n ∗
        (□ txnUpdAtOn s E ρ conn (GoInterface.ok ci) γr (txnWireOf b.model) Q ∨
          (txnWriteOnce tp [addr] ∗ txnUpdAtOn s E ρ conn (GoInterface.ok ci) γr (txnWireOf b.model) Q)) }}
      (App (Val (tp @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.txn.ty @!! go!"Commit"))
        (Val #()))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        (⌜err = GoInterface.nil⌝ ∗ ∃ m : TxnRespM, txnRespMsg resp m ∗
            txnReplied E ρ.rd γr c F (txnWireOf b.model) Q cid mid m ∗
            ∃ md, ⌜clientAttemptMd conn (GoInterface.ok ci) md⌝ ∗
              txnAuthOn s E ρ γr c n (auth.mdTokenOf md) (txnWireOf b.model)) ∨
          (⌜err ≠ GoInterface.nil ∧ resp = null⌝ ∗ kvErr err) }}
```

`txn.Commit.specG` (`KVMembers.lean:245`, its proof `txn.Commit.wp_generic`) is generic in the model and
unchanged: it passes `txnReqAt req (txnWireOf b.model)` from `txnObjAt`, which D1 extends.

### The new premise: `txnNestOk` (in D3's and D4's writing disjunct)

This is a new premise on statements with clients (`client_txn_on` through `txnUpdAtOn`; the
registration `etcdTxnSpecOn`); presented on its own as the policy asks.

- Old (writing disjunct): `txn.txnReadonly t = false ∧ txn.txnPlain t ∧ txnNoZeroEnd t`, with
  `TxnModel.plain t` (no nesting) at the top of `etcdTxnSpecOn` and as `client_txn_on`'s `hp`.
- New: `txn.txnReadonly t = false ∧ txn.txnPlain t ∧ txnNoZeroEnd t ∧ txnNestOk t`, no
  `TxnModel.plain`.
- Why: the server's handler needs `ReqOp.siblingSafeL ts ∧ siblingSafeL es ∧ txn.OpsNoCut …` of a
  writing transaction (`kvDepPre`); today they come from flatness (`siblingSafeL_of_flat`) and the
  top-level `txnModelIn` (`opsNoCut_of_flat`). For nested ones they are real conditions:
  `siblingSafe` is the server's unchecked case (`issues/etcd-txn-check-intervals-sibling.md`:
  `checkIntervals` lets a nested put and a later sibling's delete of the same key through; the issue
  finds no harm downstream, and the proof's premise is stronger than needed:
  `CheckShape.lean:13-15`, `decisions.md` D19c); `OpsNoCut` is `issues/etcd-range-sort-none-limit.md`
  at depth. Both are `kvDepPre`'s scope restrictions (D19c, `check_gives_nodup`), inherited here, not
  new ones.
- Strictly weaker overall than today's: every transaction today's statement admits (plain, in the
  model) has `txnNestOk` (L8), so each existing caller supplies it with one law.
- Alternatives: (a) `txnNestOk` stated over the handler's `ReqOp`s (`∀ ts es, v3rpc.txnModelOf
  t.cmps ts es = some t → ReqOp.siblingSafeL ts ∧ …`, as `hsh` is): no new N3 definitions, but in
  the handler's vocabulary and not decidable on the client's model; (b) over the model but with the
  handler's intervals (`hits`, `delIvl`: round 0's N3): the server's representation, not the client's
  meaning; (c) put `txnNestOk` beside `hsh` as a separate implication premise of `client_txn_on`
  (`txnReadonly = false → txnNestOk`) instead of inside `txnUpdAtOn`: the writing disjunct already
  holds the writing transaction's shape facts (`txnPlain`, `txnNoZeroEnd`), so I put it there.

## Laws

- **L1** (client, beside `opsTAt`; generalizes leasing's `userTxn_tree`)
  ```lean
  theorem opTAtC_opTxn (v : go_etcd_io.etcd.client.v3.Op) (ms : List CmpModel) (tsl esl : GoSlice)
      (ts es : List OpT) (hs : v.thenOps' = tsl ∧ v.elseOps' = esl) :
      opFullAt (GF := GF) v OpFull.txnInit ∗ cmpsAt v.cmps' ms ∗ opsTAt tsl ts ∗ opsTAt esl es ⊢
        opTAtC false v (.txn OpFull.txnInit ms ts es)
  ```
- **L2** `opTAtC_leaf : opTAtC (GF := GF) false v (.leaf o) ⊣⊢ opFullAt v o ∗ ⌜o.t ≠ W64 4⌝`.
- **L3** `opsTAt_nil : ⊢ opsTAt (GF := GF) slice.nil []`; `opsTAt_of_list : sl ↦*□ vs ∗ opListAtC false vs ts ⊢ opsTAt sl ts`;
  `opListAtC_cons`/`_nil` (a Go slice literal of trees); the leasing's `opListAtC_length`, `_get`,
  `_append`, `_drop` (`leasing/InvLeasingTxnLemmas.lean`) move beside `opListAtC` (the client's
  `Then` proof needs `_get`).
- **L4** (existing, kept) `opsAt_leaves`, `txnOps_leaves`: plain operations as leaves.
- **L5** `OpT.wire_txnOp : OpT.txnOp t = some op → OpT.wire t = opWire op` (and `wireL` of `txnOps`);
  `OpT.txnOp_leaves : OpT.txnOp t = some op → ∀ o ∈ t.leaves, o.t = W64 1 ∨ o.t = W64 2 ∨ o.t = W64 3`
  (so `Then`'s premise gives `toRequestOp`'s).
- **L6** `reqOpsAt_nil`, `reqOpsAt_snoc` (existing, re-proved for the structural form), `reqOpsAt_index`
  (`reqOpsAt ps ops ⊣⊢ ⌜ps.length = ops.length⌝ ∗ □ ∀ i p op, ⌜ps[i]? = some p⌝ -∗ ⌜ops[i]? = some
  op⌝ -∗ reqOpAt p op`, the old definition).
- **L7** (client, `ServedOn.lean`, which reaches both `KVServiceOn` and `v3rpc`; not `Results.lean`,
  which does not import `KVServiceOn`) `siblingSafeL_of_model : ReqOp.toTxnOps us = some ops →
  txnSibSafeL ops → ReqOp.siblingSafeL us` (by recursion: `allPuts` is `opPutKeys` and `allDels` is
  `(opDelOps ·).map delIvl` under `toTxnOp`; a put's key under `putTxnOp` is `o.key`), resting on
  **`inRange_of_hits`** (server, `v3rpc/CheckNodup.lean`, beside its converse `hits_of_inRange:88`):
  `hits [delIvl o] k = true → inRange o.key o.base.rangeEnd k = true`, for every key and range end
  (inverted ranges included; at an empty `k` or `key` there is never a hit, `affCmp` reading `[]` as
  `+∞`). The converse fails only at empty keys (`o.key = []`), which the server's checks reject
  (`ErrGRPCEmptyKey`): so the model's `sibOkT` is stricter than the server's only there.
- **L8** `txnNestOk_of_plain : TxnModel.plain t → txnModelIn t → txnNestOk t` (flat: `sibOkT` only
  constrains a nested transaction; `OpsNoCut` from `txnModelIn`'s cut clause).
  `txnSibSafeL_of_noDel : opsDelOps ops = [] → txnSibSafeL ops` (no delete at any depth).
  (L8 is now the one place a writing transaction's caller still meets `txnModelIn`: it is the source
  of `OpsNoCut` for a plain transaction; its docstring says so.)
- **L9** `txnReadonly_plain : txn.txnReadonly t = true → TxnModel.plain t` (read-only is flat).
- **L10** (client, `KVServiceOn.lean`, beside `txnAuthOn`; client vocabulary) the requester's lemma,
  generally:
  ```lean
  /-- **A put at any depth of a transaction needs the write permission on its key.** -/
  theorem reqPerms_irrTxn_put (tw : txn.TxnModelW) (k : GoString)
      (h : k ∈ opsPutKeys (tw.toModel.thenOps ++ tw.toModel.elseOps)) :
      ((k, [], .write) : apply.Perm3) ∈ reqPerms (irrTxn tw)
  ```
  and its instance at one level in the then-branch:
  ```lean
  theorem reqPerms_irrTxn_nestedPut (tw : txn.TxnModelW) (cs : List CmpModel) (ts es : List TxnOp)
      (k v : GoString) (l : w64) (hm : TxnOp.txn cs ts es ∈ tw.toModel.thenOps)
      (hp : TxnOp.put k v l ∈ ts) :
      ((k, [], .write) : apply.Perm3) ∈ reqPerms (irrTxn tw)
  ```
  (Proof: `TxnOpW.toOp` maps a `.put o` to `putTxnOp o`, whose key is `o.key`, and `opPerms (.put o) =
  apply.putPerms o ∋ (o.key, [], .write)`; a `.txn` to `.txn` with `opsPerms` of both branches.)
- **L12** (client, `Results.lean`: needs only `InvKVConn` and `v3rpc`) `delWiresAtT_reqOpsWire : ReqOp.toTxnOps us = some ops →
  delWiresAtT ps ops ⊢ v3rpc.reqOpsWire ps us`; `delCount_toTxnOps` without its plain premise.
- **L13** (client, `KVServiceOn.lean`; round 1, finding 5: callers no longer unfold)
  ```lean
  theorem txnUpdAtOn_write (h1 : txn.txnReadonly t = false) (h2 : txn.txnPlain t)
      (h3 : txnNoZeroEnd t) (h4 : txnNestOk t) :
      clientOpAuOn (GF := GF) s E ρ conn ctx (.txn t) Q ⊢ txnUpdAtOn s E ρ conn ctx γr t Q
  theorem txnAuthOn_write (h : txn.txnReadonly t = false) :
      txnAuthOn (GF := GF) s E ρ γr c n tok t ⊣⊢
        ∃ tw : txn.TxnModelW, ⌜tw.toModel = t⌝ ∗ v3rpc.writeGrantOn s E ρ tok (irrTxn tw)
  ```
- **L14** (client, `InvKVConn.lean`) `opWire_txn : opWire (.txn cs ts es) = .txn cs (ts.map opWire)
  (es.map opWire)` (`opWire` is written with `attach`); `txnWireOf_put_only`-style computations follow.
- **L15** `cmpsAt_nil : ⊢ cmpsAt (GF := GF) slice.nil []` moves from
  `client/v3/concurrency/InvSTMRun.lean:343` beside `cmpsAt` (`InvCmp.lean`; the old copy deleted, else the
two declarations clash in importers of both); `opsTAt_one : sl ↦*□ [v] ∗
  opTAtC false v t ⊢ opsTAt sl [t]` (a one-element slice literal) beside `opsTAt`.

(Round 0's L11, "decides by `simp`", is dropped: `txnSibSafeL` with deletes needs `inRange` on concrete
strings; callers use L8 or `txnSibSafeL_of_noDel`.)

## The requester's instance (authkv `Work`, `examples/authkv/authkv.go:250`)

`cli.Txn(ctx).Then(clientv3.OpTxn(nil, []clientv3.Op{clientv3.OpPut(k, "vt")}, nil)).Commit()`:

1. `OpPut(k, "vt")` (`OpPut.spec`): `opFullAt v1 o1`, `o1 := opPutModel k "vt" []`, `o1.t = 2`,
   `txnOpOf o1 = some (.put k "vt" (W64 0))` (authkv's `txnOpOf_put`).
2. The literal `[]Op{v1}` at `sl1` (persisted): `opsTAt sl1 [.leaf o1]` (L15 `opsTAt_one`, L2).
3. `OpTxn(nil, sl1, nil)` (S5, `cmpsAt slice.nil []`, L15): then L1 with `opsTAt slice.nil []` (L3):
   `opTAtC false v (.txn OpFull.txnInit [] [.leaf o1] [])`.
4. The variadic slice `[]Op{v}` at `sl`: `opsTAt sl [T]`, `T := .txn OpFull.txnInit [] [.leaf o1] []`,
   `OpT.txnOps [T] = some [.txn [] [.put k "vt" (W64 0)] []]` (by `simp` with step 1).
5. `Then` (S1): `b.model = { cmps := [], thenOps := [.txn [] [.put k "vt" (W64 0)] []], elseOps := [] }`;
   `txnWireOf b.model = b.model` (L14; `opWire` fixes a put).
6. `Commit` (R1) with: `hin` (vacuous: not read-only), `hsh` (authkv's `kvShapeAll_irrTxn`, whose `opShapeOk`
   gains a nested case: Q6), the writing disjunct of `txnUpdAtOn` (D4): `txnReadonly = false`,
   `txnPlain` (lease `0`), `txnNoZeroEnd`, `txnNestOk` (no get; `txnSibSafeL` of one element, or L8's
   `txnSibSafeL_of_noDel`), and `clientOpAuOn … (.txn t) Q` (authkv's `akWriteAu`), assembled by
   L13 `txnUpdAtOn_write` (no unfold).
7. On `err = nil`: `txnReplied … Q …` (so `Q` at the state the update fired, `txnReplied_Q`) and
   `txnAuthOn … t`, by L13 `txnAuthOn_write`: `∃ tw, ⌜tw.toModel = t⌝ ∗ v3rpc.writeGrantOn s E ρ tok (irrTxn tw)`;
   L10's instance gives `(k, [], .write) ∈ reqPerms (irrTxn tw)`.

## Callers and how each keeps working

| Statement | Callers | How |
|---|---|---|
| `txn.Then.spec`/`Else.spec` (S1) | `txn.Then.wp_proof`/`Else.wp_proof` (re-proved: the loop reads each op's tree, `opListAtC_get`; `wp_isWrite`/`wp_toRequestOp` at the tree, L5) | re-proof |
| | `KMTxn.lean:581,598`, `ServerKVTxn.lean:1143,1160`, `examples/linkvtxn/callTxn.lean:85,91`, `kubernetes/Client__OptimisticDelete.lean:117,197`, `Client__OptimisticPut.lean:138,218`, authkv `Work.lean:269,361` (akr3) (12 calls, all plain ops) | the lemma's name only: `wp_Then_plain`/`wp_Else_plain` (S1′) |
| | authkv `Work` (branch `authkv-hist`): the nested T3' (the instance above) | the general `wp_Then` with L1, L15 |
| `Op.toRequestOp.spec` (S2), `Op.isWrite.spec` (S3) | only `txn.Then`/`Else` proofs (and `toTxnRequest`'s) | re-proof (the leaf case is the old proof) |
| `OpTxn.spec` (S5) | leasing `txnLeasing.serverTxn` (unchanged), authkv `Work` | unchanged; leasing's `userTxn_tree` may become L1's corollary |
| `reqOpAt`/`reqOpsAt` (D1) | `txnObjAt`, `txnReqAt`, `reqOpAt_put`, `reqOpsAt_nil`/`_snoc`, the `Then`/`Else` proofs, `Op.toRequestOp` proof (`unfold reqOpAt`) | the leaf cases are unchanged; `reqOpAt_put`'s case analysis unchanged (`op ≠ .txn`); `reqOpsAt` laws re-proved (L6) |
| `txnWireOk` (D2) | `pbTxnRequest.recv`; `etcd_txnHandlerOk` (off, `Results.lean:1339`) and `etcd_txnHandlerOn` (`ServedOn.lean:452`) via `txnReq_of_requestIs` | the bridge maps D2 by L12 (both handlers re-proved over it); the off handler keeps its `TxnModel.plain` premise |
| `etcdTxnSpecOn` (D3) | `etcd_txnHandlerOn` (re-proved as above), `etcd_kv_served_on`, `etcd_kv_auth_served_on`, `etcd_kv_auth_served_onA` (registrations; text unchanged), `client_txn_on`, authkv `WorkEnv` (registration) | the registrations are untouched in text |
| `txnUpdAtOn` (D4) | `client_txn_on`; authkv `work_commit` (today `unfold txnUpdAtOn`, supplies `⟨hro, hpl⟩`) | L13 `txnUpdAtOn_write` (the unfold goes); `txnNestOk` by L8 for T1–T3, by `txnSibSafeL_of_noDel` for the nested one |
| `client_txn_on` (R1) | authkv `work_commit` only (none on `lean`) | drops `hp`; `hin` gated (supplied as `fun h => …` or vacuously); `akTxnOk` drops `TxnModel.plain` |
| `TxnModel.plain` | kept by the auth-off side (`txn.Commit.spec`, `etcdTxnSpec`, `KMTxn`, `ServerKVTxn`, `linkvtxn`) | unchanged |

## The auth-off side: a recorded scope restriction (round 1, finding 4)

The `notes/decisions.md` entry (Q2, recorded): "**Nested transactions with auth on only (2026-10-30).** The auth-on
`Commit` (`client_txn_on`, `etcdTxnSpecOn`) admits writing transactions with nested transactions
(`txnNestOk`); the auth-off one (`txn.Commit.spec`, `etcdTxnSpec`, `client_txn_any`) keeps `TxnModel.plain`:
its response relation (`txnSpec_of`, `ServerKVTxn.srvRunTxn_wire`: `srvOp` of `opWire op` = `srvOp` of
`op`, `plain_branch`, `flat_branch`) is proved for plain operations only. A scope restriction, not a
second design: lifting it is the same premise change on the off side plus those pure lemmas at depth,
to do with (or before) the auth-mode merge; the merge takes the on side's premise (`txnNestOk`), not
`TxnModel.plain`."

## Margins (what the code guarantees beyond the specs)

- `Then`/`Else` still exclude leaves `txnOpOf` rejects (a get at another revision, `WithIgnoreValue`
  with a value): unchanged from today (the transaction model has no operation for them).
- `toRequestOp`'s post does not say the request is fresh (owned); unchanged.
- The auth-off `Commit` stays plain-only (the recorded scope restriction above; Q2).
