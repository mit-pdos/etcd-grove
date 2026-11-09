# Repair of RR-grpc-auth's RR3 and RR4 (apply-txn / 2c request path / 3h / proto)

Date: 2026-11-09. Base: `41c6c3a39f` (its WIP already carried part of RR3: the three check specs
without `endsDecoded`, `holds_depth_txn`, `Unmarshal`'s depth; this pass checked it, finished it,
and did RR4's remaining sources).

## RR3: `EtcdServer.Txn`'s read-only path cannot give back `txnReqOwn r dq t`

**Fixed, the reviewer's first fix.**

- `apply.CheckTxnAuth`, `checkTxnPermission`, `checkTxnReqsPermission` take and give back only
  `txnReqOwn rt dq' t` / `msgsOwn requestOpOwn sl dq' ops`. They have no `endsDecoded`/`opsDecoded`
  any more (this was in the WIP; checked). The range-end facts come from W0's unfolds:
  `txnReqOwn_unfold`/`requestOpOwn_unfold`/`compareOwn_unfold` carry `es = slice.nil ∨ ebs ≠ []`
  (`Wire.lean:374,410,443`), and 3h's `*ReqOwn_msgAt` carry `endsOk c`.
- So `EtcdServer.Txn`'s read path splits `txnReqOwn r dq t` into two shares (one for `doSerialize`'s
  `chk`, one kept), gets the `chk` share back from `CheckTxnAuth` and rejoins it. Its statement is
  unchanged; its sketch now says this (`EtcdServer__Txn.lean`).
- **Retired in 3h** (`etcdserverpb/Api.lean`): `endsDecoded`, `opsDecoded`, `cmpsDecoded`,
  `endsDecoded_of_canon`, `endsDecoded_ro`, `endsDecoded_range`/`_delete`/`_compare`/`_txn`/`_op`.
  - Grep found no statement using them in `Spec/`.
  - In `examples/` only one comment used them (`apply/auth.go`), now reworded.
  - `reqMsgAt_endsDecoded` was already gone.
  - `endsOk`, `endsOk_canon` and `endsOk_range_intro` stay.
  - The section header now records the retirement.
- Comments brought up to date: `proto/Api.lean`'s Changes line, `apply/auth.go`.
- C19 can be retired (Requests).

## RR4: the stringers' depth premise has no source for a transaction or an internal request

**Fixed by supplying the bound. The premise stays.** It is the hard rule's "sound" side: protobuf's
text marshaling recurses per level on the stack, as `Marshal` does, and the Proto header already
bounds that by `depthMax`.

**The sources, each checked against the Go code:**

- **Decoded messages.**
  - `Proto.Unmarshal.spec`'s success case states `depth c < depthMax` (the WIP had this).
  - It is true of protobuf-go v1.36.12. `proto.Unmarshal` uses
    `RecursionLimit: protowire.DefaultRecursionLimit` = `10000` (`proto/decode.go:62`,
    `encoding/protowire/wire.go:28`).
  - `unmarshalPointer` decrements the budget per message level, the top level included, and fails
    below `0` (`internal/impl/decode.go:105`). So a successful decode has depth ≤ `10000` < `depthMax` = `10001`.
- **The apply's entry.**
  - `Apply.irrMsgAt_msg` now gives `∃ c, msgAt IRR p discard c ∗ ⌜depth c < depthMax⌝`. That is
    exactly what `stringerAt_irr` takes in `uberApplier.dispatch`.
  - The realization: `MustUnmarshalMessage`'s content `c` encodes the bytes with `norm c = c`. Its
    premise (from `irrDecodes`, which already says "protobuf's limits included") gives some `c'`
    of depth below `depthMax` encoding them. Then `encodes_fun` and `norm_facts` give
    `depth c = depth c'`.
  - The dispatch sketch now says this.
- **A transaction.**
  - 3h's `holds_depth_txn` (`reqHolds c (.txn t) → depth c ≤ txnMsgDepth t`; the WIP had this).
    It is true: `Compare`, `RangeRequest`, `PutRequest` and `DeleteRangeRequest` have no message
    fields. A `RequestOp` adds a level, and a nested `TxnRequest` another, which is
    `opMsgDepth`'s `2 + …`.
- **`txn.WarnOfExpensiveReadOnlyTxnRequest`.**
  - New premise `⌜EtcdServerPb.txnMsgDepth t < Proto.depthMax⌝`. This is the need, not
    `t.readonly`, which would be stronger.
  - Its proof: `txnReqOwn_msgAt`, then `holds_depth_txn`, then `NewLoggableTxnRequest`.
- **`EtcdServer.Txn`** (its statement is unchanged).
  - The reviewer suggested making the depth premise unconditional. That is not needed: the warning
    is called only on the read-only path, and `t.readonly` (only ranges in both branches;
    `opMsgDepth (.range _) = 2`) gives `txnMsgDepth t ≤ 3`.
  - The write-only premise `isRead = false → txnMsgDepth t + 1 ≤ 10000` stays as it was. This
    asks less of callers (the snippets build small transactions; `kvServer.Txn` has the bound
    either way).
- **`EtcdServer.Range`**: the sketch now names the deferred warning's source (`stringerAt_msg`;
  `holds_depth`: a range request is at most 3 levels deep). Statement unchanged.
- `Stringer.lean`'s header lists where each caller gets the bound.

## Requests

**To the coordinator (`open-questions.md`).**
- Retire C19 ("`CheckTxnAuth` and its helpers give `endsDecoded`/`opsDecoded` back"). Superseded by
  RR3: the three specs take only the request's own predicate, and 3h's `endsDecoded` family is
  deleted.

**To grpc-v3rpc.** Stale comments that name the retired construct:
- `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/kvServer__RangeStream.lean:20-21`: "and 3h's
  `endsDecoded` (`endsDecoded_of_canon`) for 2c's `RangeStream`". Drop it: 2c takes only
  `rangeReqOwn r (own 1) rm`, whose `endsOk` comes from `endsOk_canon` and `rangeReqOwn_msgAt`.
- `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/Api.lean:712-714`: "a share of it is 3h's
  `EtcdServerPb.endsDecoded`, what 2c's … take". Replace it with: 2c's `Range`/`RangeStream`/`Txn`
  take the request's W0 predicate, which carries `endsOk`.

**To backend-schema (optional, cosmetic).**
- `PbUtil.MustUnmarshalMessage.spec`'s post could state `depth c < depthMax` directly. It is
  derivable today (premise, `encodes_fun`, `norm_facts`), so nothing depends on it.

## New decisions

- **RR4: the depth bound is kept and supplied, not reverted.** Text marshaling recurses on the
  stack like `Marshal`, `Size`, `Clone` and `Equal`, which all take `depth c < depthMax`. Dropping
  it only for the stringers would make them the one unbounded protobuf recursion in the trust base.
- **`EtcdServer.Txn` keeps its write-only depth premise.** The read path gets the bound from
  `t.readonly` (`txnMsgDepth t ≤ 3`), so the premise did not need to become unconditional (the
  reviewer's suggestion).
- **`WarnOfExpensiveReadOnlyTxnRequest` takes the depth itself, not `t.readonly`.**

## Build

`etc/specs-build.sh --dir` over `Spec/google_golang_org/protobuf/proto`,
`Spec/go_etcd_io/etcd/api/v3/etcdserverpb`, `.../etcdserver/txn`, `.../etcdserver/apply`,
`.../etcdserver` (top level) and `.../etcdserver/api/v3rpc`: **OK (561 modules)**.

Snippets: `go vet ./specreq/apply/... ./specreq/etcdserverreq/... ./specreq/txn/...` is clean.
