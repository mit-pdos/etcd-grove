# Verification round, area A2 (client watch, lease, lifecycle): provability

Reviewer: independent provability check (2026-11-09), worktree `specs-only` at `1aa6fc1337`.
Scope: `SpecPlan/Spec/go_etcd_io/etcd/client/v3/` (watch: `ApiWatch.lean`, `WatchInternal.lean`, `watcher__*`,
`watchGRPCStream__*`, `watcherStream__*`, `WatchResponse__*`, `NewWatcher`, `NewWatchFromWatchClient`,
`Client__Watch`/`RequestProgress`, `ensureWatchHeader`, `valCtx__*`, `streamKeyFromCtx`, the `toPB`s,
the block logger; lease: `ApiLease.lean`, `lessor__*`, `keepAlive__close`, `NewLease*`,
`RetryLeaseClient`, `retryLeaseClient__*`, the promoted lease methods; client: `ApiClient.lean`,
`New`, `newClient`, `Client__*` (non-KV), `dial*`, the interceptors, `isSafeRetry*`, `authClient__*`,
`retryAuthClient__*`, `cluster__*`, `retryClusterClient__*`, `maintenance__*`, the small helpers),
`kubernetes/`, `credentials/`, `internal/{endpoint,resolver}/`, `client/pkg/v3/`; snippets
`examples/specreq/{clientv3watch,clientv3lease,clientv3client}/`.
Go: `.lake/src/client/` (= the pinned `client/v3@a4d2bb17`), server `.lake/src/server/`.

I wrote the findings below before reading `batch-*.md`, `integration-*.md`, `open-questions.md` and
`reviews/`; I read them afterwards only to mark what is already a recorded decision.

## Verdicts

| batch | verdict |
|---|---|
| **1b** (watch) | **FAIL**: W1, W2, W3 (proof plans that do not close), W4 (a snippet the spec does not give) |
| **1c** (lease, lifecycle, auth, cluster, maintenance, interceptors, kubernetes, credentials, internal, client/pkg) | **FAIL**: L1, L2 (proof plans that do not close); otherwise passes, except `ReqRefusedPrincipals`' second half, which waits on recorded open question 1.5 |

## First-tier findings

### W1. `run` cannot get `watchStep` for a reassembled fragmented response: `wireStep` does not bind the first fragment's header and compaction revision

- **Step that does not close**: `watchGRPCStream.run.spec`'s plan, case "a fragment waits" then
  `dispatchEvent.spec`. `run` keeps the **first** fragment as `cur` and appends the later fragments'
  events to it (`watch.go:596-603`), then dispatches `cur` (`:647-649`). So the `WatchResponse`
  built by `dispatchEvent` (`:737-744`) has the first fragment's `Header`, `CompactRevision` and
  `CancelReason`. `wireStep` states the completing response's fact on `m.toResp evs`, where `m` is
  the **last** message (`ApiWatch.lean:396`, `toResp` `:305-308`). Its fragment branch
  (`:362-365`) constrains a fragment's `created`, `canceled` and events, and records only
  `(id, events)` in `WireSt.frag` (`:315`). It says nothing of the first fragment's header (not
  even that its revision has been reached) or of its `compactRev`. So `deliverOk` cannot be built
  for what `run` dispatches: `watchStep` needs `hdr.revision ≤ σ.kv.rev` and `c' ≤ hdr.revision`, and
  a non-zero `compactRev` would make it an error response that has events.
- **True of the server**: `sendFragments` copies `Header`, `WatchId`, `Created`, `Canceled`,
  `CompactRevision` and `CancelReason` into every fragment (`server/etcdserver/api/v3rpc/watch.go:634-643`).
- **Callers affected**: every watch consumer that uses `WithFragment` (the `ReqWatch*` snippets
  with fragments; grpcproxy forwards the flag). The internal chain `run` → `dispatchEvent` →
  `serveSubstream` → `watchChAt_recv`.
- **Fix**: let `WireSt.frag` keep the first fragment's message (or its `hdr`, `compactRev`,
  `cancelReason`), and require each later fragment and the completing response to agree on them,
  or state the completing step on `first.toResp evs`. 2b proves this from `sendFragments`.
  (Round 1's F4, `reviews/1b-provability-1.md:77`, fixed the fragments' **id**. The header is
  new.)

### W2. `Watch` and `RequestProgress` join a stream by its key, but nothing ties the key to the principal: `watchChAt … p` is unprovable for a stream another context opened

- **Step that does not close**: `watcher.Watch.spec` (`Watcher.WatchTriple`, `ApiWatch.lean:492-500`)
  gives the caller's consumer at the **caller's** principal `p` (`ctxPrin who ctx p`). The code looks
  the stream up by `streamKeyFromCtx(ctx)` (`watch.go:330,343`) and reuses a stream that another
  context with the same key opened. The member authenticates that stream with the first context's
  metadata (`newWatcherGRPCStream` keeps `inctx`, `:282-288`), so `wgsAt s w γ p'` holds at the first
  context's `p'`, and the `wireStep` facts are `p'`'s (`σa.permits p' …`). To give
  `watchChAt ch γ p …`, the proof needs `p = p'`. But `streamKeyFromCtx.spec` returns "some string"
  (`streamKeyFromCtx.lean`), and W0 has no law relating equal keys to equal principals
  (`Api.lean:1104-1150`: `ctxPrin_of_noMeta`, `_token`, `_tokenSame`, `_value`, `_child` only).
  The old tree had this (`streamKeyOf`, the key's laws, `Proof/.../StreamKey.lean`). The nonissue
  `etcd-watch-stream-key-collision.md` says "Proof: no" because of those laws, and they are gone.
- **Callers affected**: every `Watch` caller whose context carries metadata (Kubernetes'
  `WithRequireLeader` contexts, forwarded tokens, the in-process client) and every snippet in
  `clientv3watch/` (they take `Client.Watch.spec` at the caller's principal).
- **Fix**: make `streamKeyFromCtx.spec` return `streamKeyOf (outgoing metadata of ctx)`, and add a
  W0 or 2a law `ctxPrin dflt ctx p ∗ ctxPrin dflt ctx' p' ∗ ⌜streamKeyOf ctx = streamKeyOf ctx'⌝ ⊢
  ⌜p = p'⌝`. It is sound for the contexts the intro laws admit: a token with a space never gets
  `tokenUser`, which is the nonissue's argument. The watcher's lock invariant then maps each key to a
  stream of that key's principal. The weaker alternative states the consumer at the stream's
  principal, which callers cannot use.

### W3. The watch chain has no readiness: `remoteWatchAt_watch` runs the client's stream interceptor, which needs `clientReady c`

- **Step that does not close**: `NewWatcher.spec`'s plan gets `remoteWatchAt` unconditionally from
  3h's `NewWatchClient.spec` over `connOk` (`api/v3/etcdserverpb/NewWatchClient.lean:41-46`), and
  `remoteWatchAt_watch` (`ApiWatch.lean:596-604`) has no readiness premise. But the stub's `Watch`
  opens the stream through the client's stream interceptor (`client.go:269-270`,
  `grpc.WithStreamInterceptor(c.streamClientInterceptor(...))`). That interceptor calls `c.getToken`
  (`retry_interceptor.go:123`), which calls `c.Auth.Authenticate` (`client.go:297`). 1c's
  `siOk_call.spec` (`ApiClient.lean:467`) and `Client.getToken.spec` both take `clientReady c`
  for this reason: `newClient` runs `NewWatcher` before it sets `c.Auth` (`client.go:460-461`).
  So 3h's `NewWatchClient.spec` cannot be proved as stated: its post lets a stream be opened
  before `Auth` is set. And `watcher.Watch.spec` (pre `watcherHandle` only) has no `clientReady` to
  pass on. The lease and KV chains do this right: `retryLeaseHandle_remoteLeaseAt`,
  `lessorHandle_leaseAt` and `kvHandle_kvAt` take `clientReady c`.
- **Callers affected**: `NewWatcher`, `newClient`, `watcherHandle_watcherAt`, and so every
  `Client.Watch` user.
- **Fix**: record the client in the handle (`watcherHandle w c γ who`). Then
  `watcherHandle_watcherAt` takes `clientReady c` (`null` for a caller's remote, as `lessorHandle`
  does), and `remoteWatchAt` comes either gated (`clientReady c -∗ remoteWatchAt …`) or from a
  `remoteWatchAt_watch` that takes it. 3h's `NewWatchClient.spec` changes with it.

### W4. Snippet `ReqWatchCreatedFirst` is not provable: `watchStep`'s ended case leaves `created` free

- **Evidence**: `watchStep`'s `p.ended = true` branch (`ApiWatch.lean:274-276`) has `closeErr ≠ none`,
  `compactRev = 0`, header `0`, no events and `canceled`, but **no `m.created = false`**. A
  `WatchPos.closed` watch starts ended (`:244-245`). So its second response may have
  `Created = true` under the spec, and so may any response after an error, and
  `ending.go:ReqWatchCreatedFirst` can panic. The code never sends such a response: every `closeErr`
  response is `WatchResponse{Header: &pb.ResponseHeader{}, Canceled: true, closeErr: …}`
  (`watch.go:366,381,500`).
- **Callers affected**: grpcproxy's leader probe and health check, and the cache's readiness. They
  rely on "`Created` only first".
- **Fix**: add `m.created = false` to the ended branch.

### L1. `NewLease` cannot use `NewLeaseFromLeaseClient.spec`: wrong pre (no readiness yet) and wrong post (`null` handle)

- **Step that does not close**: `NewLease` calls
  `NewLeaseFromLeaseClient(RetryLeaseClient(c), c, …)` (`lease.go:199-201`).
  `RetryLeaseClient.spec` gives only `retryLeaseHandle r c γ who`. Turning that into `remoteLeaseAt`
  takes `clientReady c` (`retryLeaseHandle_remoteLeaseAt`), and `newClient` does not have it at
  `client.go:459` (`Auth` is set at `:461`). `NewLeaseFromLeaseClient.spec` needs
  `remoteLeaseAt remote γ who` (`NewLeaseFromLeaseClient.lean:46`) and returns
  `lessorHandle l null γ who` (`:51`). `NewLease.spec` promises `lessorHandle l c γ who`
  (`NewLease.lean:42`), and no law converts. This is unlike `NewAuth`, `NewCluster` and `NewKV`,
  which do not call their `From*Client` constructor (`auth.go:120-126`, `cluster.go:60-66`).
- **Callers affected**: `newClient`, so `isClient`'s `leaseAt`, so every lease user (sessions, the
  recipes, Kubernetes' lease manager).
- **Fix**: generalize `NewLeaseFromLeaseClient.spec`. Pre: `□ (clientReady c -∗ remoteLeaseAt
  remote γ who) ∗ clientBase c who`. Post: `lessorHandle l c γ who`. The in-process caller passes
  `remoteLeaseAt` itself, and for it `clientReady` is minted by `clientBare_assemble`.

### L2. The per-member lease clauses (`via = some ep`) have no source: the wire contract carries no member view

- **Step that does not close**: `lessor.Grant.spec` (`Lease.GrantTriple`, `ApiLease.lean:221-233`)
  promises `leaseViewLb γ ep (σ'.leaseTables.length - 1)` for a client frozen at `ep`. Likewise
  `lessor.TimeToLive.spec` and `lessor.Leases.spec` (`LeaseRead.Triple`, `:238-250`) promise
  `σ.leaseAnsAt j rq res ∗ leaseViewLb γ ep j` from `leaseViewLb γ ep i`. The plan's only callee is
  `remoteLeaseAt_call`, which is `RemoteCallTriple` (`ApiClient.lean:388-395`), and
  `retryLeaseClient.Lease*.spec` restate it. That triple has no `via`, no `clientVia`, and gives no
  `leaseViewLb`. Inside the update the proof cannot tell which member applied the step. 2a's
  server side has the member view (`server/.../v3rpc/Api.lean:305-326`, `leaseFact`), but the
  client's wire contract (stub, interceptor, `AttemptTriple`) does not carry it up. Recorded
  decision A4 keeps per-member reads in scope. It does not record this gap.
- **Callers affected**: `examples/etcd/{leasegrant,leaseexpiry,leasecatchup}`. Snippets
  `clientv3lease/member.go:ReqGrantThenListOneMember` and `ReqGoneNotListed` are provable **from**
  the lessor specs, but those specs are not provable from their callees.
- **Fix**: give the lease requests a member-indexed wire triple: `RemoteCallTriple` with a `via`
  argument, or a law `remoteLeaseAt_callVia` taking the endpoints token frozen at `[ep]` and the
  `leaseViewLb γ ep i`. Carry it through `retryLeaseClient.Lease*`, 3h's stub, 1c's `uiOk_call`
  (an attempt goes to `ep` when the resolver holds only `ep`) and 2a's `AttemptTriple` (`servesAt γ
  ep` already names the member).

## Second-tier findings (do not block a verdict alone)

- **S1 (`WatchInternal.lean` header, the tie).** A watch from the current revision that is resumed
  twice, with a progress notification in between, needs more than the tie as written. After the
  first resume, from `H`, a progress at `P > floor` raises `nextRev` to `P+1` (`watch.go:873-878`).
  After the second resume, the first event's registration covers only `P+1..`. The consumer's fact
  needs `lo ≤ floor+1` (`ApiWatch.lean:295`), so the substream must remember the earlier progress
  fact (nothing in `[H, P]`). The tie says only "`done = none` where the registration has one". The
  realization can carry this, so state it. It also needs a pure model lemma: `exactFrom` is
  antitone along `Reach`, and `watchEvents` is stable on the history prefix.
- **S2 (`watchStep`).** The range membership of events (`WatchReq.keeps`) holds only under
  `exactFrom` (the `Forall₂` at `ApiWatch.lean:297-298`). The code delivers in-range keys whatever
  compaction did. The namespace wrapper slices `ev.Kv.Key[len(pfx):]` without any compaction
  assumption (`namespace/watch.go`), so outside the condition its panic-freedom does not follow.
  Suggest putting `∀ e ∈ m.events, w.range.mem e.kv.key` (and the filters) outside the guard. This
  is for the completeness reviewer. `ReqWatchRewrite` assumes the condition, so it closes.
- **S3 (`Client.unaryClientInterceptor.spec`, `streamClientInterceptor`).** The refresh calls
  `refreshToken`/`getToken`, whose pre is `clientCore c γ who`. `uiOk_call` gives only
  `uiOk ui c γ who ∗ clientReady c`, and `uiOk` is made at `clientPre` time. The plan says "see the
  margin", and the margin says "none". It closes only if `clientReady c`'s realization is
  `c = null ∨ ∃ γ' who', clientCore c γ' who'` (the disjunction is needed because of
  `clientReady_null`), with `clientPre` agreeing on `γ` and `who`. Write that down.
- **S4 (`internal/resolver`, uncertain).** grpc calls `EtcdManualResolver.Build` on its own
  goroutine (on exiting idle, the first RPC and later idle exits). `Build` reads `r.endpoints` and
  writes `r.serviceConfig`, while `SetEndpoints` writes `r.endpoints` under the client's `epMu`
  only, which `Build` does not take. `Build` has no spec, and `resolverAt` is exclusive. How the
  `dialTargetOk` and grpc boundary admits `Build` is not stated. I could not settle whether 2a's
  grpc model calls back into `Build`. If it does, with auto-sync on, this is a data race in the Go
  code too: `issues/` should get a note after a Go race test.
- **S5 (`Lease.KeepAliveTriple`, `lessor.Close.spec`).** `lessor.Close.spec` takes `clientReady c`,
  which `Close` does not need (it only cancels and waits). It is harmless through the bundle. Note
  it as an unneeded premise.

## Proof plans, per target

Legend: ✓ closes from the cited callee specs as they are now; ✗ a first-tier finding;
(s) a second-tier note.

### Batch 1b: the watch

- `ApiWatch.lean`, the vocabulary. Good: the responses are persistent `etcdLb` facts. `WatchPos`
  separates `done`, `floor` and `evDone`, and the compaction case is checked against `evDone`
  (matches `watcher_group.go`'s `minRev`). `wireStep` covers the registration order (`creates ss
  [answered]`), ids that are seen and retired, the `-1` progress exemption for ids with a cancel in
  flight, and fragments by id. The server's progress guard `rev < w.startRev`
  (`mvcc/watchable_store.go:539`) makes "progress not below `done`" true. Laws:
  `watchRespAt_fields`, `_persist` and `watchRespRO_persistent` are plausible.
  `watchRespAt_noEvents_dup` holds: for `[]`, `msgsOwn` is a pure slice fact, the header is at
  `discard`, and `closeErrOk` is persistent. `watchSpec_records`, `wsLog_*`, `wireWatchSend_*` and
  `wireWatchRecv_recv` are realizable over 2a's grpc stream. Flaws: W1 (fragments), W4 (ended
  branch), S2.
- `watcher.Watch.spec`: `OpWatch.spec`, then the loop under `mu` (`streams = nil`: a fresh closed
  channel, `WatchPos.closed`), `newWatcherGRPCStream.spec`, and `select` over `reqc` (`wgsAt`'s
  protocol: the `*watchRequest` with `initReqAt`, `rev`, `retc`), `ctx.Done()` (`ctxOk`) and
  `donec` (closed after `run`'s deferred `w.closeErr = …`, so the unlocked read of `wgs.closeErr` at
  `:365,380` is ordered by the close). On `retc` the consumer arrives at `WatchPos.init rev r0` with
  `etcdLb γ σ0`, `H ≤ r0` from the registration's `wireStep`, or at `WatchPos.closed` from
  `closeSubstream`'s hand-off. Every channel is non-nil (`closeSubstream` hands out `outc` only if it
  is non-nil). ✗ W2 (the principal of a joined stream), ✗ W3 (readiness).
- `watcher.RequestProgress.spec` (post `True`): ✓ by Löb over the recursive call. Its join by key
  has no principal fact to give, so W2 does not bite here.
- `watcher.Close.spec`: ✓ (`close.spec` per stream; a hang is liveness).
  `watchGRPCStream.close.spec`: ✓.
- `NewWatcher.spec`: ✓ as stated, but only because `NewWatchClient.spec` is too strong (✗ W3).
  `NewWatchFromWatchClient.spec`: ✓ (`clientBase`: a non-nil logger).
- `Client.Watch.spec`, `Client.RequestProgress.spec`: ✓ by dispatch through `isClient`'s
  `watcherAt` (they inherit W2 and W3).
- `watchGRPCStream.run.spec`: the loop carries `wgsRun`, `wgsSend`, `cancelSet`, `closing` and `cur`.
  The cases match the code (`:557-718`): `Created` → `addSubstream`, `dispatchEvent`,
  `nextResume`; `Canceled` without compaction closes `recvc` and forgets the id; the failed dispatch
  sends a cancel; `errc` → `newWatchClient`; `closingc` → `closeSubstream` and a cancel. The teardown
  is `joinSubstreams`, then `closeSubstream` × `len(closing)`, then `wg.Wait`, then `closeStream`.
  A refused create's substream is not in `closing` (`issues/etcd-watch-close-hang-refused-create.md`),
  so the teardown can hang: liveness only. ✗ W1 (fragment dispatch).
- `serveSubstream.spec`: ✓. The `panic` is unreachable (`q.closing = false`: both forkers fork only
  non-closing substreams, `:572-578,970-977`). `last.Kv` is non-nil (`eventOwn` models a `KeyValueM`
  with no option). `wr.Header` is non-nil (`ensureWatchHeader`). Responses buffered after an error
  are never delivered (it returns at `:838-839`); the realization must allow factless buffer entries
  there (the tie's "an ended substream delivers nothing more"). (s) S1.
- `serveWatchClient`, `newWatchClient`, `openWatchClient`, `waitCancelSubstreams` (with
  `wcsPending_close` and `_join`), `joinSubstreams`, `nextResume`, `addSubstream`, `dispatchEvent`,
  `broadcastResponse` (the dup law), `unicastResponse`, `closeSubstream`, `sendCloseSubstream`,
  `backoffIfUnavailable`, `newWatcherGRPCStream` (`valCtx_ctxOk`, `ctxPrin_child`), `closeStream`,
  `startBufWait`, `recordBufWait`, `newWatcherStreamBufLogger`, `resetBufWait`, `toPB` × 2,
  `ensureWatchHeader`, `WatchResponse.Err` (matches `:123-136`; `isErr` omits `Canceled`, which is
  never delivered without `closeErr` or a compaction: `run` handles it at `:625-640`),
  `IsProgressNotify`, `valCtx.{Done,Err,Deadline}`, `newBlockLogger`, `blockLogger.recordWait`,
  `streamKeyFromCtx` (✓ as stated; W2 is about what it should state): ✓ as internal mirrors over
  opaque internals with stated realizations.

### Batch 1c: the lease

- `ApiLease.lean`: good. The persistent update for repeatable `Grant` and `Revoke` matches
  `retry.go:150-155`. The not-found `TimeToLive` reply is modelled (`leaseTTLReply`). `kaRespAt` is
  read-only, as `recvKeepAlive` shares one response across channels. `kaSent_sent` lets
  `keepAliveOnce` prove `id' = id`. Laws: plausible (`kaLog_*`, `kaReq_lookup`, `kaChan_recv`).
  ✗ L2.
- `lessor.Grant`, `lessor.Revoke`, `lessor.TimeToLive`, `lessor.Leases`: ✓ for `via = none`
  (`remoteLeaseAt_call`, `ContextError`, the reply unfolds of 3h); ✗ L2 for `via = some`.
- `lessor.KeepAlive.spec`: ✓. Under `mu`: a closed `donec` gives a closed channel; otherwise the
  entry holds the channel's close token. The `keepAliveCtxCloser` goroutine and the `Once`-started
  loops get `clientReady` from the pre. No close happens twice: every closer removes the channel
  under `mu`, `keepAlive.close` acts on an entry just removed from the map, and the closer matches
  its context by the unique `&ctx` value.
- `lessor.KeepAliveOnce`, `keepAliveOnce`: ✓. Three outcomes, including the case where a deferred
  `CloseSend` error replaces a `nil` result while the response is non-nil (`lease.go:429-436`);
  the third disjunct covers it.
- `lessor.Close`: ✓ (the `Once` decides who closes `donec`). (s) S5.
- `recvKeepAliveLoop`, `resetRecv`, `recvKeepAlive`, `sendKeepAliveLoop`, `deadlineLoop`,
  `keepAliveCtxCloser`, `closeRequireLeader`, `keepAlive.close`: ✓. The `lg` is non-nil by
  `clientBase`. `append(l.callOpts, withMax(0))` allocates: `callOptsOk_full` holds, since the slice
  literals have `cap = len`.
- `NewLease.spec`: ✗ L1. `NewLeaseFromLeaseClient.spec`: ✓ as stated for a caller's remote.
  `RetryLeaseClient`, `retryLeaseClient.*`: ✓ (through `siOk_call` and `uiOk_call` with
  `clientReady`).
- `Client.{Grant,Revoke,TimeToLive,Leases,KeepAlive,KeepAliveOnce}` (promoted): ✓ by dispatch
  through `clientRest`'s field.

### Batch 1c: the client, auth, cluster, maintenance, interceptors

- `ApiClient.lean`: good. `AttemptTriple`'s four outcomes and `uiOk_call`'s "never (3)" match
  `retry_interceptor.go:41-110`, including the fork's non-repeatable context-error return (`:89-91`)
  and the `max == 0` short-circuit, where the interceptor fires a refusal as a ghost step. Readiness
  (`clientReady`) is explicit. Laws: `callOptsOk_*`, `cfgPrincipal_*`, `clientBare_assemble`,
  `*_methods`, `retry*Handle_remote*At` are plausible. (s) S3.
- `New`, `newClient`: ✓ (no endpoints: an error and `nil`; `ErrMutuallyExclusiveCfg` has no
  `cfgPrincipal`, so it is unreachable; `clientReady` is minted after `client.go:461`), except that
  the `Lease` member inherits L1.
- `Client.Close`, `Ctx`, `GetLogger`, `WithLogger`, `Endpoints`, `SetEndpoints`, `Sync` (the update
  is built from `idUpd`, `etcdLb` comes from inside the commit, then 2e's `memberServes`),
  `autoSync`, `checkVersion`, `dial`, `dialSetupOpts`, `dialWithBalancer`, `Dial`,
  `credentialsForEndpoint`, `getToken`, `refreshToken`, `shouldRefreshToken`,
  `roundRobinQuorumBackoff`, `ActiveConnection`, `NewFromURL(s)`, `NewCtxClient`: ✓.
- `unaryClientInterceptor`, `streamClientInterceptor`: ✓ modulo S3.
- `isSafeRetry`, `isSafeRetryMutableRPC`, `isSafeRetryImmutableRPC`, `isContextError`,
  `contextErrToGRPCErr`, `waitRetryBackoff`, `withRepeatablePolicy`, `withMax`, `withBackoff`,
  `reuseOrNewWithCallOptions`, `filterCallOptions`, `backoffLinearWithJitter`, `jitterUp`,
  `retryPolicy.String`, `isHaltErr`, `isUnavailableErr`, `canceledByCaller`, `IsConnCanceled`,
  `authority`, `ClientLogLevel`, `WithZapLogger`: ✓ (one line each: total, or classified by 2a's
  `callErr`).
- `authClient.*` (18), `retryAuthClient.*` (17), `cluster.*` (7: `memberAdd`'s `NewURLs` check is
  `CheckedCallTriple`), `retryClusterClient.*` (5), `maintenance.{AlarmList,AlarmDisarm,Status}`
  (`(0, NONE)` excluded by premise, `maintenance.go:168-181`; `Status` dials through the endpoints
  token), `retryMaintenanceClient.Alarm`, `New{Auth,Cluster,Maintenance}` and their `From*Client`
  forms, `Retry*Client`: ✓.
- `kubernetes/`: `New`, `Client.{Get,List,Count,OptimisticPut,OptimisticDelete}`, `kvFromTxnResponse`:
  ✓ (each one KV call; `txnReply`'s `rs = [.range …]` excludes the
  `len(Responses) == 0` error; `singleKV` matches `len(Kvs) == 1`).
- `credentials/` (8): ✓ (an `RWMutex` invariant holding a `tokFor` token).
- `internal/endpoint` (2), `internal/resolver` (3): ✓ as stated. (s) S4, uncertain.
- `client/pkg/v3/` (`logutil`, `transport`, `types`, `verify`): ✓ (`idStr` is lowercase hex as
  `FormatUint(…,16)`; `Verify` matches `verify.go:69-74`; `Assert(true, …)` is a no-op).

## Snippets

| file | snippet | result |
|---|---|---|
| clientv3watch/history.go | FromGet, WaitDelete, RevisionWhole, Order, Filter, History, FromNow, Chained | ✓ (8). `watchStep`'s event case with `lo = done + 1`, or `≤ floor + 1` from now; progress `c ≤ P`; `etcdLb_reach` for the put's revision above `r0` and `P` |
| clientv3watch/consume.go | Select (`watchChAt_recvAu`), Rewrite (header owned in full with events), PrevKVCompacting (`prevOk`), Share (`watchRespAt_persist`), Options | ✓ (5) |
| clientv3watch/ending.go | Compacted (`evDone + 1 < cr`, `cr > rev`), Ends, WatcherClose | ✓ (3) |
| clientv3watch/ending.go | CreatedFirst | ✗ **W4** |
| clientv3watch/progress.go | ProgressComplete, RequestProgress | ✓ (2) |
| clientv3lease/grant.go | GrantTTL, GrantThenPut | ✓ (2) |
| clientv3lease/member.go | GrantThenListOneMember, GoneNotListed | ✓ from the lessor specs; those specs are ✗ **L2** |
| clientv3lease/reads.go | TimeToLiveAbout, LeasesNoDup, KeepAliveOnce | ✓ (3) |
| clientv3lease/session.go | SessionLifecycle, KeepAliveValues | ✓ (2) |
| clientv3client/lifecycle.go | NewWrapClose, NewNoEndpoints, Endpoints, CtxPut, NewFromURL | ✓ (5) |
| clientv3client/auth.go | AdminSetUp, UserClient, RefreshAtMostOnce | ✓ (3) |
| clientv3client/auth.go | RefusedPrincipals | first half ✓; second half (a context carrying an unissued token) waits on **open question 1.5** (`tokenUnissued`) |
| clientv3client/cluster.go | MemberAddThenList, Sync | ✓ (2) |
| clientv3client/maint.go | Status, AlarmDisarm | ✓ (2) |
| clientv3client/tls.go, inproc.go | NewTLS, InProcClient | ✓ (2) |
| clientv3client/kubernetes.go | KubeNew, KubeCAS, KubeList | ✓ (3) |

Every watch snippet also inherits W2 and W3 through `Client.Watch.spec`'s provability. Given the
spec as stated, they close except CreatedFirst.

## Counts

- Specs: about 245 files in scope read (watch 41, lease 33, client and auth/cluster/maintenance
  127 non-KV, kubernetes 8, credentials 8, internal 5, client/pkg 13, plus the 5 vocabulary files).
  About 75 have a written-out plan above; the rest are one-line helpers or thin wrappers checked by
  signature against the Go body. They close except: `watchGRPCStream.run` (W1);
  `watcher.Watch`, `Client.Watch` (W2, W3); `NewWatcher` (W3, via 3h's stub spec); `NewLease` (L1);
  `lessor.Grant`, `lessor.TimeToLive`, `lessor.Leases` and their promoted `Client.*` forms (L2, their
  `via` clause). That is 11 specs that fail.
- Laws: about 60 checked (the persistence bundles, the record laws, the field unfolds, the
  introductions); none vacuous, none false. `wireStep` is too weak (W1); `watchStep`'s ended
  branch is too weak (W4).
- Snippets: 46 checked. 42 close outright, 2 close from specs that fail (L2), 1 fails (W4), 1 waits
  on open question 1.5.
- Users: not this reviewer's kind (completeness). S2 is passed on.

## Ranked by need of revision

1. `ApiWatch.lean` (`wireStep` fragments W1, `watchStep` ended branch W4, S2) with
   `watchGRPCStream__run.lean`.
2. `watcher__Watch.lean`, `streamKeyFromCtx.lean` and W0's `ctxPrin` laws (W2).
3. The lease wire contract: `ApiClient.lean`'s `RemoteCallTriple` for lease requests and
   `retryLeaseClient__*`, with `ApiLease.lean`'s `via` clauses (L2).
4. `NewWatcher.lean`, `ApiWatch.lean`'s `watcherHandle`/`remoteWatchAt_watch`, and 3h's
   `NewWatchClient.lean` (W3).
5. `NewLeaseFromLeaseClient.lean` and `NewLease.lean` (L1).
6. `WatchInternal.lean`'s tie (S1); the interceptor sketches (S3); the resolver (S4, uncertain);
   `lessor__Close.lean` (S5).

## Already recorded?

Checked after writing the findings against `open-questions.md`, `batch-1b.md`, `batch-1c.md`,
`integration-*.md` and `reviews/1b-*`, `1c-*`. W1 is not recorded: round 1's F4 covered the
fragment id, not the header or compaction revision. W2, W3, W4, L1 and L2 are not recorded (A4
keeps per-member reads in scope without noticing that the wire contract does not carry the view).
`RefusedPrincipals`' unissued token is open question 1.5. The refused-watch check of the auth
example is open question 1.2 (no snippet; consistent). The close hang is
`issues/etcd-watch-close-hang-refused-create.md` (liveness). No new Go bug was found. S4 is
uncertain and needs a Go race test before it is filed.
