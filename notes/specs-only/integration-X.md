# Integration X: the residue between the gRPC boundary, the client and the server (after I1-I7, Y)

Owned: `SpecPlan/Spec/go_etcd_io/etcd/api/v3/**`, `client/**`, `cache/`, `SpecPlan/Spec/context/`, `SpecPlan/Spec/google_golang_org/**`,
`server/v3/etcdserver/**` but `apply/`, `txn/`; `server/v3/storage/*.lean`, `storage/wal/`;
`pkg/v3/{wait,idutil,notify,schedule}/`; `raft/v3/raftpb/`; `SpecPlan/Spec/net/http/`; their snippets.

## Build

- All 49 owned directories in one `etc/specs-build.sh --dir` run: **OK, 1396 modules** (before
  Y's follow-ups). After the Y follow-ups: `etcdserver`, `api/{snap,v3compactor,rafthttp}`, `storage`:
  **OK, 295 modules**. Final run over all 49 owned directories after every edit: **OK, 1396 modules**.
- The dependents I do not own (Y's): `etcdserver/{apply,txn}`, `auth`, `lease`, `storage/{mvcc,backend,
  schema}`, `pkg/v3/pbutil`: **OK, 606 modules**.
- Snippets: `go vet` of `specreq/{cache,cindex,clientv3client,clientv3kv,clientv3lease,clientv3watch,
  concurrency,etcdserverboot,etcdserverpb,etcdserverreq,grpc,leasing,rafthttp,raftpb,recipes,schedule,
  v3rpc,v3rpcwatch,wait}/...` is clean. `gofmt -l` of the same directories plus `etcdserverapply`
  prints nothing. No Go file changed.

## What changed, by item

### I3 → 1c/1b: the streams' records and the credentials

- `callAU`, `AttemptTriple` and `uiOk_call` already took `lo` with `authLb γ lo`. I1 did this, so
  nothing was left to do.
- **The client cannot import `v3rpc/Api.lean`, because that module imports the client.** So the
  stream contracts and their records moved down to the client. They are still 2a's obligations.
  - `client/v3/ApiLease.lean`:
    - `kaReq`, `kaLog`, `kaSpec` and the laws `kaLog_alloc`, `kaLog_add`, `kaReq_lookup` and
      `kaReq_persistent` moved here from v3rpc.
    - **`kaSent g id` is now a definition**: `∃ i, kaReq g i id`.
    - The halves now take the stream's name: `kaSendAt sc g ids` and `kaRecvAt sc g`. They stay 2a's
      opaque slots, because their realization goes through 3h's stub wrapper.
    - `kaSent_sent` is now over `g`.
    - The module imports `etcdserverpb/Api`.
    - Followers updated: `retryLeaseClient__LeaseKeepAlive`, `lessor__resetRecv`,
      `lessor__sendKeepAliveLoop` and the sketch of `lessor__keepAliveOnce` (`∃ g`).
  - `client/v3/ApiWatch.lean`:
    - `watchSpec`, `wsReq`, `wsSt`, `wsWho` and `watchSpec_records` moved here from v3rpc.
    - New: a request log `wsLog`, with the laws `wsLog_alloc` (it mints `wsWho` from `streamKey`),
      `wsLog_add` and `wsLog_lb`.
    - **`WatchStreamNames` is now `Grpc.StreamName`.**
    - **`wireWatchSentLb g ss` is now a definition**: `[∗list] i ↦ r ∈ ss, wsReq g i r`.
    - `wireWatchSend` and `wireWatchRecv` stay slots. Their intended realization is now stated in
      terms of the records.
  - `etcdserverpb/Api.lean`: `watchReqHolds`, `watchRespHolds`, `eventHolds`, `watch_holds_fun` and
    `watch_holds_depth` moved here from `Realize.lean`. Without the move there would be an import
    cycle.
- **`credMD` is now 1c's `Credentials.credMD γ who mdc`**, a definition: either no metadata, or
  `token: tok` with a non-empty `tokFor` token.
  - New law `Credentials.rpcCredsAt_perRPC`: `rpcCredsAt v γ who ⊢ Grpc.perRPCAt v (credMD γ who)`.
  - The dial's sketch (`Client__dial`) now passes it as grpc's `R`.
  - `V3rpc.mdPrin_of` cites `Credentials.credMD`. V3rpc imports `credentials/Api`.

### I4 → 2a

- **`firedAns` is now an `abbrev` of 2c's `srvFiredAns`.** The composition paragraph cites
  `srvStep_step` and `txnChecked_safe`.
- **`rsSink`**: it stays 2c's opaque, and its laws are 2a's.
  - New `rsSink_send.spec` (on `KV_RangeStreamServer.Send`): a chunk is recorded, or `ownErr` and
    nothing is recorded.
  - New `rsSink_context.spec`: the result is `ctxOk`, `reqCtxOk`, and `reqPrin ctx p tls`.
  - `rsSink_intro` now also takes `srvCtxOf rs ctx md ∗ mdPrin γ md who`, which `rsSink_context`
    needs.
- **The `srvGate` share** (design, google_golang_org and v3rpc):
  - grpc's runs now carry a run resource `T`: `Grpc.unaryOk … T`, `streamOk … T` and
    `regsOk B C T`.
  - `Grpc.start.spec` takes `n` copies of `T` and also gives a new `drainTok gs T n`.
  - `Server.GracefulStop.spec` takes the `drainTok`s and gives the copies back.
  - `startHTTP` lends `emp`.
  - `V3rpc.HandlerTriple` has an optional last argument `T`, default `True`, which the handler holds
    and returns.
  - The handlers over 2c methods take `(gq : Qp)` and pass `(srvGate s gq)`. That is 41 unary
    handlers: `kvServer`, `quotaKVServer`, `LeaseServer`, `quotaLeaseServer` (the unary ones), every
    `AuthServer`, `ClusterServer.Member{Add,Remove,Update,Promote}`, and both `Alarm`s.
  - The same applies to `kvServer.RangeStream`, `LeaseServer.LeaseKeepAlive`/`leaseKeepAlive` and
    `quotaAlarmer.check`.
  - `icEtcdOk` and `healthRegs_ok` are now `∀ T`.
  - `Server.spec` registers for `∀ ep gq, regsOk B (etcdContract γ ep) (srvGate s gq)`.

### I5 → 2c

- **`Authenticate`'s provider error** (sketch, `EtcdServer__Authenticate.lean`): the update fires
  with `.ok .authenticate`, then the call returns the apply's error. That is outcome 3 (`srvIndef`),
  because the member's provider is simple or JWT (2e's `authBootRes`). JWT fails only with its
  signer's non-etcd error, and the no-op provider's `ErrAuthFailed` is excluded. The post is
  unchanged. This needs a fact from 3d (below).
- **Empty range ends**:
  - New `Proto.decodedAt t p` (persistent, scope). `Proto.Unmarshal.spec` gives it on success, and so
    do grpc's `decOk_call`, `srvRecv_recv` and `cliRecv_recv`.
  - 3h (`etcdserverpb/Api.lean`) gives:
    - `endsDecoded t p` (opaque, persistent), introduced by `endsDecoded_of_decoded` and
      `endsDecoded_range_intro` (a range request a caller built: the health checks');
    - `opsDecoded sl` (a definition);
    - the elimination laws `endsDecoded_range`, `_delete` and `_compare`;
    - the split laws `endsDecoded_txn` and `endsDecoded_op`, which are W0/3h's requested split.
  - `EtcdServer.Range`, `RangeStream` and `Txn` take `EtcdServerPb.endsDecoded … r`.
  - `HandlerTriple` and `icEtcdOk` carry `Proto.decodedAt reqT q`. The 15 generated unary handlers'
    wands (`etcdserverpb/_*_Handler.lean`) take it. `kvServer.RangeStream` takes it for its request.

### I4 → 3h: `irrOwn` at a fraction

- In `etcdserverpb/Api.lean`, `irrOwnH p dq ir h` and `irrOwn p dq ir` now have the outer struct
  owned and the inner request at `dq`.
- New definitions:
  - `irrCarries`;
  - `irrInner ir` (the inner type and content relation; alarms through `alarmReqHolds`);
  - `irrLit ir q` (`&pb.InternalRaftRequest{F: q}`, over `zero_val`);
  - `irrInnerAt p q` (persistent).
- New laws: `irrOwn_wrap`, `irrOwn_unwrap` and `irrOwnH_read` (a fraction for `Marshal`).
  `irrOwnH_msgAt` now holds only at `dq = 1`, and `setHeader`/`header` take `dq`.
- `ApiReq.lean`: **`EtcdServer.irrOwn` is now an `abbrev` of 3h's**, and `irrOwn_own` is gone (it had
  no users).

### Other items

- `raftpb/Api.lean`: the stale `mergeDstOk` text now says `Proto.mergeDst`.
- 3a's alarm activation reply: 2c states it. `irrReply (.alarmActivate al)` is
  `reqReply γ (.alarmActivate al)`, the `*AlarmResponse`.

### Y's follow-ups (`integration-Y.md`, "What X needs")

- **`NewServer.lean` sketch**, which now covers:
  - the post-lock hook, proved once as `∀ q, Backend.hookRun γ q Pk f Pre Q` and converted by
    `keyBackend_intro`, `leaseHookRun_intro` and `applyHook_intro`;
  - the lessor's resources: `beOpen γ 1` is split into `Backend.leaseShare` and the rest;
    `leaseBeOk_intro`, with `_elim` before `Close`; `leaseBeHook_intro`; `leaseBeLeases_intro` after
    `beVis_drop`; and `mvccDeleter_rdOk` via `leaseTxHeld_intro` with `mvccOn γ B`;
  - the compactor: `mvccRevTok_of` gives the persistent `mvccRevTok`, plus the caller's `threadTok`,
    and that is `revRd γ true`. **I4's gap is closed.**
- `v3compactor/Api.lean`: `revGetter_intro` already took `threadTok` per call. Its docstring now cites
  the realization.
- `mvccClosed_rest`'s new shape: no spec or sketch of mine cites it, so nothing changed.
- **`ApiApply.lean`: `beSnap` and `dbReader` are now definitions**, over `Backend.beSnap` and
  `Snap.dbReader`, with `histAt γ k σ` and `⌜Backend.smImage I σ k⌝`. The module imports
  `backend/StateImage` and `snap/Api`.
- **`Snap.BeImage` is now an `abbrev` of `Backend.Image`.** `snap/Api` imports `backend/Api`.
- `context.isCtxErr`: `srvErrShape`'s context branch is already `context.isCtxErr err`, so mvcc's
  `.ctxErr` result composes directly.

## Provisional names

**Resolved:**
- `kaSent`, `WatchStreamNames`, `wireWatchSentLb`, `credMD`, `firedAns`, `irrOwn` (2c's);
- `beSnap`, `dbReader`, `Snap.BeImage`;
- I5's `endsDecoded`/`opsDecoded`, which now exist as 3h's.

**Kept, and why:**
- `kaSendAt`, `kaRecvAt`, `wireWatchSend`, `wireWatchRecv`, `remoteWatchAt`: their realization goes
  through 3h's stub wrapper and grpc's halves. Making them definitions would hard-code the wrapper
  types.
- `rsSink`: 2c's opaque; its laws are now all 2a's.
- `mdPrin`, `quotaOk`, `sicEtcdOk`, `watchMemberAt`: unchanged since I3.
- The other provisional names listed in I4's report as still open (`entryAt`, `mergedSnap`,
  `httpForbidden`, `raftNodeBuilt`, `v3rpcBootCfg`, `raftNodeBootCfg`, `gaugeVecOk`, 2f's names):
  I did not revisit them.

## Sketches that do not fit (open)

1. **`LeaseServer.LeaseKeepAlive`.**
   - On the context-done path the handler returns while its `leaseKeepAlive` goroutine may still be
     inside 2c's `LeaseRenew`, which holds a `srvGate` share.
   - So the run cannot give its share back (`lease.go`: `errc` is buffered and not waited for), and
     the post's `srvGate s gq` is unprovable on that path.
   - The open paragraph is recorded in the file.
   - Ways out:
     - 2c's `LeaseRenew` without the gate: it touches no backend `Cleanup` closes. A decision for
       2c/2e.
     - A fork change.
2. **The TLS path (`Grpc.startHTTP`) lends no run resource.** An etcd member serving clients over
   TLS therefore cannot run handlers over 2c's request path from these specs. Closing this needs
   net/http's handler pool to lend a resource too: 2f's `Http.handlerPool`.
3. **`maintenanceServer.Snapshot`** reads the backend without a gate share. This is the same race as
   `issues/etcd-read-after-backend-close-panic.md`, and no 2c method is involved. I did not change it.
4. **`Authenticate`**: excluding a mapped provider error needs 3d's provider fact (below).

## Needed from directories I do not own

- **3d** (`server/v3/auth/Api.lean`): a token-provider fact that simple and JWT providers (2e's
  `authBootRes`) never fail `assign` with a mapped etcd sentinel, for example the `aok` flag on
  `tokenProviderAt` that I5 proposed. `Auth.ctxInMD`/`ctxPeerCN`/`ctxCertUser` should be defined as
  `Grpc`'s (I3's request, still open there).
- **3a** (`etcdserver/apply/Api.lean`):
  - Replace the provisional `endsDecoded rt`/`opsDecoded sl` with
    `EtcdServerPb.endsDecoded etcdserverpb.TxnRequest.ty rt`/`EtcdServerPb.opsDecoded`.
  - `reqMsgAt_endsDecoded` then follows from the apply's `Unmarshal` (`Proto.decodedAt`) and
    `endsDecoded_of_decoded`.
  - Use 3h's `irrInner`/`irrOwn_unwrap` where it decodes the inner request.
- **2f** (`net/http`'s handler pool, in my `SpecPlan/Spec/net/http/` but a protocol decision): a pool that lends
  a run resource, for open item 2.

## Process note

I ran one `git checkout` of `SpecPlan/Spec/google_golang_org/grpc/Api.lean`, a file in my own directory, to
undo my own first edit (the abandoned `cliStreamOf` design). No other file was touched.
