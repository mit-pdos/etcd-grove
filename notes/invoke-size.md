# The encoded-size bound at grpc's send side (2026-10-30, branch `invoke-size`)

The repair of `grpc.ClientConn.Invoke.wp_proof` and `grpc.ClientConn.NewStream.wp_proof`, which
the axiom review `axiom/txn-nested-wire` refuted. grpc v1.84's `codecV2.Marshal` allocates
`proto.Size` bytes before checking any size (`issues/grpc-codec-alloc-before-size-check.md`, on
`axiom/txn-nested-wire` `b157b99a97`). The design was approved by the user on 2026-10-30 (Q1-Q6); it
is recorded in `notes/decisions.md`, "The encoded-size bound at grpc's send side". This file
records the state of the change and what `txn-nested` must fold.

## State: partial (one pass did not reach the libraries)

**Done (builds: `Proof.go_etcd_io.etcd.client.v3.Link`, `Results`, `ResultsOn`, `ClientPutGet`,
`KMWatch`, `watcher__Watch`):**

- **The gRPC layer.**
  - `grpcMsgMax`, `wireSlack`, `ProtoMsg.wireLen` and `grpcInvokerOk`'s new premise are in
    `Proof/google_golang_org/grpc/InvGrpc.lean`.
  - `StreamMsg.wireLen` is in `InvGrpcStream.lean`. The `SendMsg`/`Send` triples of
    `cliStreamIs`/`cliBidiStreamIs` gain the premise.
- **The wire models.** Each request instance gets a `wireLen`, and the whole-struct sends gain
  `unknownFields' = slice.nil`:
  - the KV requests (`InvKVConn`);
  - the auth requests (`InvAuthConn`, `InvClientAuth`);
  - the lease requests (`InvLease`, `InvLessor`);
  - the watch request (`v3rpc.watchReqWireLen`, `InvWatchStream`).

  `reqOpAt`'s put case gains `o.ignoreValue = true → o.val = []` (W2).
- **The client's vocabulary and laws.** In `InvKVConn.lean`:
  - `opWireLen`, `cmpWireLen`, `TxnOp.wireLen`, `txnWireLen`;
  - the predicates `opSizeOk`, `watchSizeOk`, `txnSizeOk`, `strsSizeOk`;
  - the option laws `OpShape`, `optsKeep`, `optsKeep_*`, `withPrefixM_keep`, `withFromKeyM_keep`,
    `withRangeM_keep` and `opShape_opFold`;
  - the laws `opSizeOk_opGetModel`/`opPutModel`/`opDeleteModel`, `watchSizeOk_opWatchModel` and
    `strsSizeOk_of_le`.
- **The specs, from the interceptor up, which gain the premise:**
  - `etcdInterceptorOk(M)` and `EtcdInvoke`;
  - the stubs and the retry clients (KV, auth, lease);
  - `kv.Do`/`Put`/`Get`/`Delete` and `txn.Commit` (`spec`, `specM`, `specG`);
  - the auth client's methods (`strsSizeOk`), with the credentials' bound in `clientAuthAt`/`clientAuthPre`;
  - `watcher.Watch` (`watchSizeOk`).

  The internal `Op.toRequestOp` premise and the `Op.toRangeRequest` post change too.
- **The client results.** A hypothesis `hsz` is added to:
  - `client_{put,range,delete,txn}_any`;
  - `client_{put,range,get,delete,txn}_end_to_end` and `client_get_after_put`;
  - `client_{put,range,delete,txn}_on`;
  - `client_{Put_own,Get_own,Get_st,Put_rep,Put_any,Put_st,Delete_st,Put_kv}`.
- **The adapter `isEtcdWatcher_of_km`** gains `pfx.length ≤ 2 ^ 28`, which pins the prefix watch's
  size. `isEtcdClient_of_km` does not yet pass it on.

**Left (not started; the build is red from here on):**

1. **cache/v3's client contracts.** Each operation gains the size premise:
   - `isEtcdKV`/`isEtcdKVE` (`InvEtcd.lean:790,813`) and `isEtcdWatcher` (`:943`);
   - `isEtcdRangeWatcher` (`InvEtcdTxn.lean:1091`);
   - `txnBuilderSpec`/`X` (`:561,629`), `readTxnBuilderSpec` (`:723`), `isEtcdTxnKV`,
     `isEtcdReadTxnKV`, `isEtcdDeleteKV` and the `…Todo` contracts (`:878-970`);
   - `txnBuilderSpecO`, `isEtcdTxnKVO` and `isEtcdDoKV` (`InvEtcdTxnOwn.lean:448-496`).

   Their adapters must be updated with them: `KMGet`, `KMPut`, `KMTxn`, `ServerKVGet` (the first
   to fail, `:303`, `kv_get_server_r` against `kv.Get.specM`), `ServerKVTxn`, `ServerKVPut` and
   `KMClient` (`isEtcdClient_of_km` needs `hpl`).
2. **The libraries that call the contracts:**
   - the cache (`New` gains `pfx.length ≤ 2 ^ 28`, kept in its state);
   - concurrency (`Mutex`, `Election`, the locker; STM per call, Q6);
   - leasing;
   - recipes (`experimental/`);
   - k8s (the store's specs, `kubernetes.Client`).
3. **The examples' closed theorems.** The size facts are discharged inside each one. Examples
   are `GenKv`, `common.Writer.spec`, linkvtxn's `GenIn` (it needs a law `txnSizeOk_of_bounds`,
   L-s4, not yet written), k8setcd3's `GenIn` and authkv's `ClientOn` (`client_put_on`).
4. **The checks.** None has been run on this state: the full build, `etc/tcb-report.py --check`
   (expected to show nothing, since the baseline lists names), the collections, `etc/api-check.py`,
   `etc/gen-interface.py --check --layout`, `gen-link`, `gen-init`.

## Departures from the approved draft

- `wireSlack` is in `InvGrpc.lean` (the watch's `wireLen` in `v3rpc` uses it), not in `InvKVConn`.
- `pbTxnRequest.send` also pins the top-level `TxnRequest`'s `unknownFields` (an extension of W3).
- The lease stubs and retry clients (`LeaseGrant`, `LeaseRevoke`) gain the `unknownFields` premise.
  The draft had "unchanged".
- `Op.toRangeRequest.spec`'s post (internal) also gives `req.unknownFields' = slice.nil`.
- The watch has no filters bound: `createOf` has `filters := []`.
- `watcher.Watch`'s premise is `watchSizeOk` (key and range end), not `opSizeOk`, because a watch
  sends no value. With `opSizeOk`, the adapter could not bound a value the options might set.
- L-s5 takes the `OpShape`/`optsKeep` form: options that keep `key ≤ K`, `rangeEnd ≤ E` and
  `val ≤ V`, with `K + E + V ≤ 2 ^ 30`.
- The client results take the size as a Lean hypothesis (`hsz`), as `client_txn_any` already took
  `hp`/`hin`, rather than as a pure conjunct in the pre.

## What `txn-nested` must fold (from `lean` at this branch)

- **D1** `reqOpAt` (`Proof/go_etcd_io/etcd/client/v3/InvKVConn.lean:742`): the put case is
  `⌜op = txn.putTxnOp o ∧ (o.ignoreValue = true → o.val = [])⌝`. `reqOpAt_put` (`:806`) takes
  `(hv : o.ignoreValue = true → o.val = [])`. The nested case is unchanged: its bound is
  `TxnOp.wireLen`'s `.txn` case (`:253`).
- **S2** `Op.toRequestOp.spec` (`Spec/go_etcd_io/etcd/client/v3/Op__toRequestOp.lean:31`): on
  `lean`, the leaf premise is `(o.t = W64 1 ∨ o.t = W64 2 ∨ o.t = W64 3) ∧ (o.t = W64 2 →
  o.ignoreValue = true → o.val = [])`.
  - On `txn-nested`, **S2/S4** (`Op.toTxnRequest.spec`) take it for every leaf: `∀ o ∈
    t.leaves, …`.
  - `txn.Then`/`Else` pass `⟨Ht123, txnOpOf_put_val Hto⟩` (`txnOpOf_put_val`,
    `InvKVConn.lean:227`).
- **L5** `OpT.txnOp_leaves` (and L4 `opsAt_leaves`/`txnOps_leaves`): the conclusion gains the
  conjunct, from `txnOpOf_put_val`.
- **R1** `client_txn_on` (`Proof/go_etcd_io/etcd/client/v3/ResultsOn.lean:322`): `(hsz : txnSizeOk
  (txnWireOf b.model))`. The same hypothesis is on `client_txn_any` (`Results.lean:2002`) and
  `client_txn_end_to_end` (`:2315`).
- **The auth-off `txn.Commit`** (`Spec/go_etcd_io/etcd/client/v3/txn__Commit.lean:50`, `specM`/`specG`
  at `Proof/go_etcd_io/etcd/client/v3/KVMembers.lean:152,270`): the pre's last conjunct is
  `⌜txnSizeOk (txnWireOf b.model)⌝`.
- **`txnBuilderSpecO`'s `Commit`** (`InvEtcdTxnOwn.lean:448`): `txnSizeOk`, with the contracts
  (item 1 above, not yet on this branch).
- **Unchanged:** D3 `etcdTxnSpecOn`, D4 `txnUpdAtOn`, S1, S3, S5, D2 and N1–N4. The size is the
  sender's obligation to grpc, not part of the registered spec.
