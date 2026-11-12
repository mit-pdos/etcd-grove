# Integration I1 (the client side): report

Integration agent I1, 2026-11-09, per `integration-brief.md`. Directories: W0's model and client
KV (`api/v3/{Model,State,Wire}.lean`, `client/v3/Api.lean` and W0's specs, `SpecPlan/Spec/context`,
`SpecPlan/Spec/go_uber_org`), 1b (watch), 1c (lease, lifecycle, auth, cluster, maintenance, interceptors,
`kubernetes`, `credentials`, `internal/*`, `client/pkg/v3/*`), 1d (`concurrency`), 1e (`leasing`),
1f (`recipes`, `SpecPlan/Spec/fmt`), 1g (`cache`, the B-tree), `SpecPlan/Spec/sort` (3c's; checked only). The work
per batch was done by forks of I1; their sections follow I1's summary.

## Build result (every directory I own)

`etc/specs-build.sh --dir SpecPlan/Spec/go_etcd_io/etcd/api/v3 SpecPlan/Spec/context SpecPlan/Spec/go_uber_org/zap SpecPlan/Spec/go_uber_org/zap/zapcore SpecPlan/Spec/go_etcd_io/etcd/client/pkg/v3/{logutil,transport,types,verify} SpecPlan/Spec/go_etcd_io/etcd/client/v3 SpecPlan/Spec/go_etcd_io/etcd/client/v3/{concurrency,credentials,experimental/recipes,internal/endpoint,internal/resolver,kubernetes,leasing} SpecPlan/Spec/go_etcd_io/etcd/cache/v3 SpecPlan/Spec/k8s_io/utils/third_party/forked/golang/btree SpecPlan/Spec/fmt SpecPlan/Spec/sort`: **OK (746 modules)**, after all edits.

Snippets: `cd examples && go vet ./specreq/{clientv3kv,clientv3watch,clientv3lease,clientv3client,concurrency,leasing,recipes,cache,btree}/`
clean; `gofmt -l` on them prints nothing.

Before integration the cache (`Cache__Get`, `Cache__serverRevision`, `Cache__get`) and the whole
`leasing` directory failed (`ctxPrin` arity, W0's round 3).

## The peer-URL right (the coordinator's decision, after the forks)

**For I4: the name and signature.** `EtcdModel.urlsRight (γ : Cluster) (urls : List GoString) :
IProp GF` (opaque, exclusive) in `SpecPlan/Spec/go_etcd_io/etcd/api/v3/State.lean`, with
`EtcdModel.urlsRight_excl.spec : ∀ (γ : Cluster) (urls urls' : List GoString), urls.Perm urls' →
urlsRight γ urls ∗ urlsRight γ urls' ⊢ False`: the same signature and law as 2e's
`EtcdServer.urlsRight`/`urlsRight_excl` (`etcdserver/ApiBoot.lean:235, :473`), which I4 deletes;
2e's `urls_reserve` (it mentions `srvNet`, `Http.addrFree`) stays 2e's and mints W0's
`urlsRight`. Until 2e's copy is deleted, a bare `urlsRight` inside namespace `EtcdServer` is 2e's
own (the namespace wins); outside it, a file opening both `EtcdModel` and `EtcdServer` would see an
ambiguity.

The client takes it: 1c's `Cluster.MemberAddTriple` (hence `MemberAdd`, `MemberAddAsLearner`) and
`Cluster.MemberUpdateTriple` add `urlsRight γ urls` to their precondition; `cluster.memberAdd.spec`
too; the wire contract `RemoteCallTriple` takes the new `reqRight γ rq` (`ApiClient.lean`:
`urlsRight γ urls` for `.memberAdd urls _` and `.memberUpdate _ urls`, `True` otherwise), so
`retryClusterClient.{MemberAdd,MemberUpdate}` take it. Margin: the right is spent even when the
call is refused or fails. **Still needed of 2a**: a way for the right to reach the server's
`AddMember`/`UpdateMember` through `etcdUnary` (e.g. `callAU`'s firing taking `reqRight γ rq` with
`etcdState`); the snippet `clientv3client/cluster.go` (`ReqMemberAddThenList`) assumes the caller
holds `urlsRight γ [peerURL]`.

Rebuilt after this change: `etc/specs-build.sh --dir SpecPlan/Spec/go_etcd_io/etcd/api/v3 SpecPlan/Spec/go_etcd_io/etcd/client/v3{,/concurrency,/experimental/recipes,/kubernetes,/leasing} SpecPlan/Spec/go_etcd_io/etcd/cache/v3 SpecPlan/Spec/go_etcd_io/etcd/server/v3/etcdserver`: OK (787 modules; 2e's `etcdserver` included: no clash); `go vet ./specreq/clientv3client/` clean.

## The known items, resolved

| item | resolution |
|---|---|
| W0 rounds 3-6 renames in 1b-1g | adopted everywhere: `ctxPrin dflt ctx p` per call (1e and 1g had not); `lo`/`authLb` on reads (`lo = 0`, or the caller's `lo` where a contract passes it on); `RespBody.authenticate`, `Req.alarmActivate`, `AlarmKind.other` (1c); `endOf`/`OpM.endReq` (the cache and the watch read an empty end differently from W0's ranges, as their code does: documented); `permittedSince` (covered by 1b's any-reached `σa`); `putOnce`, `TxnReq.valid` (covered by the generic refusal disjuncts); `etcdPerm`/`etcdPeek`, `etcdLb_init`, `leaseViewLb`, `compactLag` in use |
| recipes' `sessionAt` → 1d's `isSession` | done: `Concurrency.isSession s c γ id ∗ isClient c γ who` (1d's predicate names its client, no principal) |
| 1f/1g local permission copies | none left: W0's `etcdPerm`/`etcdPeek` (`dbPerm` is `etcdPerm` over `dbWrite`) |
| one `exactFrom` | `EtcdModel.exactFrom` (+ `Event.key`) in `Model.lean`; `ClientV3.exactFrom` an `abbrev`. **Hazard**: a file outside namespace `ClientV3` opening both `EtcdModel` and `ClientV3` gets "Ambiguous term" for a bare `exactFrom`; 1d, 1f, 1g write `EtcdModel.exactFrom`. 3f's `Mvcc.exactFrom` can become an abbreviation too (3f's file; inside namespace `Mvcc` its own name wins) |
| 1b's watch messages into `Wire.lean` | done: `WatchReq`, `EventM`, `WireWatchReq` (+ `.creates`), `WireWatchRespM`, `HeaderM.zero`, `eventOwn`, `watchReqOwn`, `wireWatchRespOwn`, `eventOwn_unfold`, `eventOwn_persist`; `WatchReq.keeps/prevOk`, `EventM.isOf`, `WireWatchRespM.toResp` stay in ApiWatch under their `EtcdWire.` names. 2b's `v3rpc` and 3f's `mvcc` rebuild OK; 3h's `Realize.lean` could not be checked (its directory fails earlier, below) but opens `EtcdWire` and names nothing by `ClientV3.` |
| the cache as a `Watcher` (1g's open question 1) | recorded, not unified (five differences, and the 1b changes it would need, in 1g's section); the cheap part done: the cache's events are W0's `EtcdWire.eventOwn` |
| 1d's `concErr` vs `callErr_errorsNew` | consistent (`concErrVal_ok`, `concErrVal_notCanceled`, `callErr_errorsNew` give `TryLock`'s, `Proclaim`'s, `Lock`'s error disjuncts) |
| 1e's `lkvAt`/`ltxnAt` bridging laws | consistent with W0's current `KV.*Triple`s (1e's section) |
| leasing's proxy via `clientRest`/`clientMut_split` | consistent; 1d's `NewSession` now takes `clientRest` (1e's round-1 request) |
| `RemoteKV`/`AttemptTriple` vs 2a | mismatches recorded below (the read window `lo`, `mdPrin`, `kaSpec`, `watchSpec`) |

## The main finding: watch exactness was claimed unconditionally downstream

1b's round 3 made a watch response's events (and a progress's "no events") exact only under the
compaction condition `exactFrom`. Three batches built on the watch still claimed them
unconditionally, which no proof from 1b's contract can give: 1d's `Election.Observe`
(`observeAt_recv`/`_recvAu`); 1f's watch-based facts (`waitEvents`, `WaitEvents`,
`WaitPrefixEvents`, `Barrier.Wait`'s `goneAt`, `DoubleBarrier.Enter`'s `readyPutAt`, both
`Dequeue`s' front and value); 1g's cache (`deliv`, `quiet`, `getOk`, `snapCert`, `store.Get`).
Each is now under `EtcdModel.exactFrom` at the fact's state; facts from reads are unchanged; the
snippets that rely on a watch assume the condition (an invariant clause of their owner). The step
rests on a pure lemma clients prove: `exactFrom` at a later state implies it at an earlier one
(the history only grows, compaction only rises).

## Other soundness fixes

- 1d's `Concurrency.grantEff` did not append the old lease table to `leaseHist`, so W0's real
  grant was not a `grantEff` step and `NewSession`'s `effIn` did not cover the grant it fires
  (found by the 1e fork; fixed by I1 in `concurrency/Api.lean`).
- 1c's `RemoteCallTriple` answered `LeaseTimeToLive`'s not-found with an error, contradicting
  2a's `ansOutcome` (a reply, `err = nil`) and `lessor.TimeToLive`'s sketch (`replyAns`, `wireAns`).
- 1c's `keepAliveOnce` could not conclude the response is about its `id` (`kaSent`, `kaSent_sent`;
  needs 2a, below).
- 1b's `wireWatchSend_send` dropped a failed send from the sent list, while 2a counts it sent.
- W0's `kvHandle_kvAt` ignored 1c's readiness gap (`kvHandle kv c γ who`, `clientReady c`);
  `isClient_conn`/`clientRest_conn` were false of an in-process client (removed).

## I1's own edits

- `api/v3/Model.lean`: `Event.key`, `exactFrom` (from `ApiWatch.lean`).
- `api/v3/Wire.lean`: the watch messages (above); new laws `msgOwn_discard_persistent`,
  `eventOwn_discard_persistent` (1g's need: read-only messages are persistent).
- `client/v3/ApiWatch.lean`: the moved definitions removed, `exactFrom` an abbreviation.
- `client/v3/Api.lean`, `ApiClient.lean`: `clientReady`'s opaque moved into `Api.lean`.
- `concurrency/Api.lean`: `grantEff` (above).
- `retryKVClient__{Range,Txn,Compact}.lean`: the Open note says 1c's chain now carries `lo`.

## Needs from directories I1 does not own

1. **2a** (`server/v3/etcdserver/api/v3rpc/Api.lean`):
   - `etcdUnary` and `rangeStreamSpec` must carry the caller's read window: an update over
     `Step p rq σ σ' res lo` with `authLb γ lo` (today `lo = 0`). Until then W0's
     `retryKVHandle_remoteKVAt` cannot be realized for `Range`, `RangeStream`, `Txn`, `Compact`
     (1c's `callAU`/`AttemptTriple`/`uiOk_call` now carry `lo`).
   - `mdPrin_of`: an introduction of `V3rpc.mdPrin γ md who` from the client's `ctxPrin` and the
     credentials' token metadata (with 3d); the client cannot state it (no server imports).
   - `kaSpec`'s `dn`: a response's ID is the ID of a request sent before (1c's `kaSent`).
   - `watchSpec γ` (a trivial opaque `StreamSpec`, "slot, 2b"): define it or its laws so 1b's
     `remoteWatchAt`, `wireWatchSend`, `wireWatchRecv`, `wireWatchSentLb` are realized from
     `Grpc.cliSend`/`cliRecv` (`dn` giving `wireStep p σ σa ss st m st'`, `etcdLb γ σ`,
     `etcdLb γ σa`, `wireWatchSentLb g ss`), with 2b's server slots on the same stream names.
   - Margin recorded: definite answers rpctypes does not map (`invalidClientAPIVersion`,
     `permissionNotGiven`) reach the client as `.other` (covered by `wireIndef`).
2. **3h** (`api/v3/etcdserverpb/Api.lean:97`): `reqType`'s match lacks `Req.alarmActivate` (W0's
   round 5), so the directory, and `Realize.lean` with it, does not build. Also realize the new
   `msgOwn_discard_persistent`, `eventOwn_discard_persistent`.
3. **3d**: `tokenUnissued γ tok` (with an introduction a program can use and `tokenUnissued ∗
   tokenUser ⊢ False`), so that W0 can add `ctxTokenMd ctx tok ∗ tokenUnissued γ tok ⊢ ctxPrin
   none ctx p` (1c's round-1 item 3, `ReqRefusedPrincipals`). 3d round 1's `roleGrantPermission`
   with a nil or unknown-typed `Perm` needs `Req.roleGrantPermission`'s argument to become an
   `Option`: a coordinated change (every match on `Req` in 1c, 2a, 2c, 3a, 3d), not done.
4. **2e**: `v3client.New` is 2e's spec (1c gives `NewCtxClient.spec`, `clientBare_assemble`; its
   `NewWatchFromWatchClient(adapter, c)` now needs `clientBase` and `remoteWatchAt` of the
   in-process adapter, whose contract is unstated). `urlsRight`: now W0's (above); 2e deletes its
   own copy and cites `EtcdModel.urlsRight`. 2e's provisional
   `Config.urlsStrs` → 1c's `Types.urlsStrs`. 1d's `NewSession.spec` now takes `clientRest`
   (`isClient_rest` gives it) for 2e's v3lock/v3election sketches.
5. **2f**: provisional `Rafthttp.urlsAt`/`urlsHosts` → 1c's `Types.urlsAt`/`urlsHosts`
   (`urlsNoComma`, `Http.urlOk`, `urlsMapStrs` stay theirs: `NewURLs` accepts a comma).
6. **3f**: `Mvcc.exactFrom` may become an abbreviation of `EtcdModel.exactFrom`.
7. **1b, optional** (my directory; left as a decision): an unconditional weak fact in
   `watchStep`'s events case (each delivered event is the last change of its key at its revision)
   would make 1f's `goneAt`/`readyPutAt` unconditional.

## Provisional names left (by owner)

- 2a's slots, realized by laws rather than renamed: `callErr` (`callErr_view`), `connOk`,
  `dialOptsOk`, `grpcConnAt`, `unaryArgs`, `grpcCallOptsOk`, `transportCredsOk`, `kaSendAt`/
  `kaRecvAt`, `wireStreamAt`, `ctxTokenMd`, `ctxRequireLeader`, `tlsCfgOk`; 3h's `replyOwn`,
  `reqOwn`, `statusRespOwn`, `userAddOptsAt`, `authTokenAt`; 2e's `tlsPrincipal`.
- 1b's watch-stream slots (`remoteWatchAt`, `wireWatchSend`, `wireWatchRecv`, `wireWatchSentLb`):
  nothing realizes them yet (2a's `watchSpec`, above).

# Per batch (the forks' reports)

## W0 (model, client KV, context, zap)

Build: `etc/specs-build.sh --dir SpecPlan/Spec/go_etcd_io/etcd/api/v3 SpecPlan/Spec/context SpecPlan/Spec/go_uber_org/zap SpecPlan/Spec/go_uber_org/zap/zapcore SpecPlan/Spec/sort` OK (32 modules); W0's client/v3 modules by name OK (142); `go vet ./specreq/clientv3kv/` clean, gofmt clean.

Changed:
- `api/v3/Model.lean` (I1): `EtcdModel.Event.key`, `EtcdModel.exactFrom` (3f's request; 1b's `ClientV3.exactFrom` is an `abbrev` of it).
- `api/v3/Wire.lean` (I1): the watch messages moved in from `client/v3/ApiWatch.lean` (`WatchReq`, `EventM`, `WireWatchReq` + `.creates`, `WireWatchRespM`, `HeaderM.zero`; `eventOwn`, `watchReqOwn`, `wireWatchRespOwn`; `eventOwn_unfold`, `eventOwn_persist`); `WatchReq.keeps`/`.prevOk`, `EventM.isOf`, `WireWatchRespM.toResp` stay in ApiWatch under their `EtcdWire.` names. New laws `msgOwn_discard_persistent` (every message predicate and `protoRest` at `DFrac.discard` persistent) and `eventOwn_discard_persistent` (1g's need).
- `client/v3/Api.lean`: `clientReady` declared here (moved from 1c's ApiClient; laws stay there); `kvHandle kv c γ who`, `retryKVHandle rkv c γ who` record their client; `kvHandle_kvAt`, `retryKVHandle_remoteKVAt` take `clientReady c` (1c round 1 item 1). `isClient_conn`, `clientRest_conn` removed (false of an in-process client, item 2); `clientMut_conn` kept. Header: every KV write fired at most once; only `LeaseGrant`, `LeaseRevoke`, `Alarm` repeatable (item 4); stale law names fixed.
- `kv__*` (7), `retryKVClient__*` (6): `∀ c`, `…Handle … c γ who ∗ clientReady c`; the retry sketches name the real path (3h's stub → 1c's `uiOk_call`/`siOk_call` → 2a's `AttemptTriple`/`etcdUnary`/`rangeStreamSpec`, `callErr_view`); `Range`, `Txn`, `Compact`, `RangeStream` mark the `lo` gap Open.
- `NewKV`, `RetryKVClient`, `NewKVFromKVClient`: posts give the handle with `c` (`null` for `NewKVFromKVClient`).
- `State.lean`: new law `etcdLb_leases` (no lease table has lease 0; every present key's non-zero lease is live) — 3a round 1 item 6.
- `SpecPlan/Spec/context/Api.lean`: `TODO.spec`/`Background.spec` name their values (`todoCtxVal`, `backgroundCtxVal`; 4b's request).

Open (the biggest): the read window `lo`. `RemoteKV.{Range,RangeStream,Txn,Compact}Triple` take `authLb γ lo` and an update over `Step p rq σ σ' res lo`; 1c's `callAU` (hence `AttemptTriple`, `uiOk_call`, `siOk_call`), 2a's `V3rpc.etcdUnary` and `V3rpc.rangeStreamSpec` have no `lo` (work at `0`). An update over `Step … lo` does not accept every `Step … 0` transition, so `retryKVHandle_remoteKVAt` cannot be realized for reads and `Compact` until 1c and 2a carry `lo` and `authLb γ lo`. (1c: see its section.)

Other mismatches with 2a: `mdPrin` has no introduction from `ctxPrin` + the credentials' metadata (1c, 3d or 2a owe it); definite answers rpctypes does not map (`invalidClientAPIVersion`, `permissionNotGiven`) reach the client as `.other` (covered by `wireIndef`: recorded as a margin); 2a's `callErr_eof` exists (item 4 met).
Requests to W0 after round 6: 3c round 1 met (TimeToLive keys bounded above only); 3a round 1 item 5 met (`invertedDeny`), item 6 met (`etcdLb_leases`); 2e round 1 item 5 and round 2 met; `context.md` all met; 3f's `exactFrom` met (I1). Not done: 1c's item 3 (`ctxPrin` of an unissued token: no `tokenUnissued` exists; 3d must add it, with an introduction and `tokenUnissued ∗ tokenUser ⊢ False`; then `ctxTokenMd ctx tok ∗ tokenUnissued γ tok ⊢ ctxPrin none ctx p`); 3d round 1 (`roleGrantPermission` with a nil/unknown-typed `Perm`: needs `Req`'s argument to become an `Option`, breaking every match on `Req` across 1c, 2a, 2c, 3a, 3d: a coordinated change).

## 1b (watch)

Build: ApiWatch, WatchInternal, the 38 watch specs and the 2 new block-logger specs (42 modules) OK by name through `etc/specs-build.sh`; `go vet ./specreq/clientv3watch/` clean, gofmt clean.

Changed:
- `client/v3/ApiWatch.lean`: header follows the move of the watch messages to `Wire.lean` and of `exactFrom` to `Model.lean` (`exactFrom` an `abbrev`). `OpM.watchReq` docstring: for a watch a non-nil empty end is the single key, while W0's `OpM.endReq` reads it as "from the key on" for a range — they deliberately differ (the member's `recvLoop`, `v3rpc/watch.go:322-329`, turns an empty `RangeEnd` into nil and `"\x00"` into from-key, which `KeyRange.mem` models); no statement change. `wireWatchSend_send.spec`: the error branch records the request as sent (`ss ++ [r]`, was `ss`): 2a's `cliSend_send` counts a failed message as sent, so the member may have read it, and 2b's `srvWatchRecvdLb_sent` relies on the client's list being a prefix of what the member reads; `run` only logs a failed `Send` (note added).
- `NewWatchFromWatchClient.lean`: pre 1c's `clientBase c who` (was `clientConnOk`, which an in-process client cannot give; it reads `c.callOpts`, `c.GetLogger()`). `NewWatcher.lean`: pre `clientCore c γ who` (as 1c's `NewLease`, `NewAuth`). Both import `ApiClient`.
- New `newBlockLogger.lean`, `blockLogger__recordWait.lean` (`block_logger.go` had no spec: 1b and 1c each left it to the other), over a new opaque persistent `blockLoggerAt bl A` (`WatchInternal.lean`); `bufLoggerAt`'s realization points to it.
- Sketches of `watchGRPCStream__{run,newWatcherStreamBufLogger,recordBufWait}`; `examples/specreq/clientv3watch/ending.go` `ReqWatcherClose`: `NewWatcher`'s `clientCore` from `isClient` by `isClient_core` (was the removed `isClient_conn`).

Provisional names left: the stream slots `remoteWatchAt`, `wireWatchSend`, `wireWatchRecv`, `wireWatchSentLb`: nothing realizes them; 2a's `V3rpc.watchSpec γ` (`v3rpc/Api.lean:277`, "slot, 2b") is an opaque `StreamSpec` with a trivial body, and 2b states the server end over its own slots (`srvWatchRecv`, `srvWatchSend`).
Checked: W0 rounds 3-6 (`ctxPrin dflt ctx p` in place; `endReq` not on the watch path; `σa` any reached state covers `permittedSince`); 2b's sends are `wireStep` with its corrections; 2a's errors for `remoteWatchAt_watch`, `wireWatchRecv_recv` (`callErr_eof`, `callErr_status`/`_unmapped`, `callErr_ownErr`); 1c's `isHaltErr`, `isUnavailableErr`, `ContextError`, `GetLogger`, `Close`; W0's `WithCancel`, `Done`, `doneRecv`. Open question 3 (`deliverOk`): consistent with `wireStep`; only the slots' realization remains.
Requests to 1b: from 1f 1-4, 1d (3 withdrawn, 4), 1e 4, 1g 1-4 met; 2b's corrections adopted; `context.md` met. Made by 1b: 1c met (block logger added here); W0 met (messages, `exactFrom`, `EnvCfg.compactLag`); 3h realizes the messages (`Realize.lean`); 2a/2b slots not realized.
Needs: (1) 2a/2b (`v3rpc/Api.lean`): define `V3rpc.watchSpec γ` or laws of it, so `wireWatchSend` comes from `Grpc.cliSend` over it and `wireWatchRecv` from `cliRecv` with `dn` giving `wireStep p σ σa ss st m st'`, `etcdLb γ σ`, `etcdLb γ σa`, `wireWatchSentLb g ss`; 2b's server slots on the same stream names. (2) 1c: `clientBase`'s realization should list `callOpts` (read-only, `callOptsOk _ false`); `newClient`'s sketch must hold `clientCore` when calling `NewWatcher`. (3) 2e (`v3client.New`): `NewWatchFromWatchClient(adapter, c)` needs `clientBase` (from `clientBare_base`) and `remoteWatchAt` of the in-process adapter, whose contract is unstated.

## 1c (lease, lifecycle, auth, cluster, maintenance, interceptors, kubernetes, credentials, internal, client/pkg)

Build: all 1c directories plus 2a's v3rpc (which uses the changed `callAU`), 496 modules, OK; `go vet ./specreq/clientv3lease/ ./specreq/clientv3client/` clean, gofmt clean.

Changed:
- `ApiClient.lean`: `clientReady`'s opaque moved to W0's `Api.lean` (I1; laws stay). Not-found lease reply: `LeaseTimeToLive` of an unknown lease is a reply (`TTL = -1`, `err = nil`), as 2a's `ansOutcome` sends it (2a round 1): new `replyAns rq res`, `wireAns rq`; `AttemptTriple`'s nil branch is `replyAns`, its error branch excludes it; `uiOk_call` follows; `RemoteCallTriple` returns `wireAns rq` (it used `wireReply ansReply`, which stated an error for that answer and contradicted `lessor.TimeToLive`'s sketch). Read window: `callAU` takes an optional last `(lo : Nat := 0)` and fires over `Step … lo`; `AttemptTriple`, `uiOk_call` bind `lo` and take `authLb γ lo` (W0's `RemoteKV` reads need it); other 1c uses at `lo = 0`; `siOk_call` unchanged (no update). `cfgOk` carries `⌜Grpc.msgsFit⌝` (2a's `NewClient.spec` requires it); imports grpc's Api.
- `ApiLease.lean`: `kaSendAt sc ids` records the ids sent; `kaRecvAt_recv` gives a persistent `kaSent sc id` for the response's ID; new law `kaSent_sent` (`⌜id ∈ ids⌝`): without it `keepAliveOnce`'s "the response is about `id`" (and `ReqKeepAliveOnce`) did not follow. `lessor__sendKeepAliveLoop`, `retryLeaseClient__LeaseKeepAlive`, `lessor__keepAliveOnce` follow.
- `client/pkg/v3/types` (for 2e, 2f): pure `urlsHosts`, `urlsNorm`, law `urlsHosts_len`; `urlsValid := (urlsHosts ss).isSome`; persistent `urlsStrs sl us`, `urlsAt sl hs` given by `NewURLs` (read-only for good); `URLs.StringSlice` takes `urlsStrs us ss`, returns `sl ↦* ss`.

Checked, no change: W0 rounds 4-6 followed; Kubernetes' specs fit W0's KV triples at `lo = 0`; requests from W0, 1b, 1d, 1e, 1g, 2a, 2a round 1 met; `idUpd` kept (weaker than `etcdPeek`, so any holder of `etcdPeek` gives it).
Not met, recorded: 2a `kaSpec.dn` must say a response's ID is a sent request's (to realize `kaSent`); 2a `etcdUnary` must carry `lo` + `authLb`; `V3rpc.mdPrin` has no introduction from `ctxPrin` + the token metadata (the client cannot import server vocabulary: `mdPrin_of` belongs in 2a's Api, with 3d); 2e item 1 (`v3client.New`) is 2e's spec (1c gives `NewCtxClient.spec`, `clientBare_assemble`); 2e item 2 (`urlsRight` on `MemberAdd`/`MemberUpdate`): `urlsRight` lives in the server's `ApiBoot.lean`, which the client cannot import, and `etcdUnary` cannot carry it: needs W0 to host `urlsRight` in `State.lean` and 2a to carry it on the wire; 2e/2f must replace their provisional `Config.urlsStrs`, `Rafthttp.urlsAt`/`urlsHosts` by `Types.*`; `urlsMapStrs` (no `NewURLsMap` spec), 2f's `urlsNoComma`, `Http.urlOk` stay theirs (`NewURLs` accepts a comma).

## 1d (concurrency)

Build: `etc/specs-build.sh --dir SpecPlan/Spec/go_etcd_io/etcd/client/v3/concurrency` OK (63 modules); `go vet ./specreq/concurrency/` clean, gofmt clean.

Changed:
- `concurrency/NewSession.lean`: pre `clientRest c γ dflt` (was `isClient`; `isClient_rest` gives it) — meets 1e round 1 (the proxy makes sessions after overwriting `client.KV`); sketch reaches `Client.Ctx`/`GetLogger` via `clientRest_core`, `clientCore_pre`, `clientPre_base`.
- `concurrency/Api.lean`: `observeAt_recv`/`observeAt_recvAu`: `v.modRev ≤ header ∧ ObservedAt pfx v σ.kv` now gated on `EtcdModel.exactFrom σ.kv (σ0.kv.rev + 1)` (1b's round-3 `watchStep` gives events only under `exactFrom`); the rest unconditional. Header: reads pass `lo := 0` (`authLb γ 0` by its left disjunct); invalid / `putOnce`-violating txns are only refused (covered by the generic error disjuncts). `isSession`'s realization over `clientRest`.
- `Election__observe.lean`, `Election__Observe.lean`: sketches cite the gate. `Mutex__Lock.lean`: `Client.Ctx.spec` wording (`clientBase c dflt`, `ctxPrin dflt ctx dflt`).
- `examples/specreq/concurrency/election.go`: `ReqObserve` assumes the compaction condition.

Sketches that did not fit: (1) `Election.observe` assumed gap-free events unconditionally; fixed by the gate. (2) Files outside namespace `ClientV3` opening both `EtcdModel` and `ClientV3` must write `EtcdModel.exactFrom` (the `ClientV3.exactFrom` abbrev makes the bare name ambiguous).
Checked and fitting: `Lock`/`waitDeletes`/`Campaign` facts from `Get`; W0 reads with `lo := 0`; `TryLock`/`Proclaim`/`Lock` error disjuncts vs `callErr_errorsNew`, `concErrVal_notCanceled`, `concErrVal_ok`; 1c's `Lease.GrantTriple` (`via := none`, `callAU … true` from `etcdPerm`), `KeepAliveTriple`, `RevokeTriple` (repeatable, persistent update); 1b's `Watcher.WatchTriple` per-call principal (`ctxPrin_child`); `WriteM.op .del`'s end vs `OpM.endReq`.
Provisional names: none (the round-1 `Concurrency.etcdPerm` already W0's).
Requests to 1d: 1f (Session.Client/Lease) met (`isSession s c γ id`, no principal); 1e round 0 met; 1e round 1 item 3 (`NewSession` over `clientRest`) met now; 2e round 1: tell 2e `NewSession.spec` takes `clientRest` (`isClient_rest`) and `observeAt_recv` is gated (2e has no `Observe` handler spec).
Requests 1d made: client_v3 "from 1d" items 1,2,4,5 met (1c `clientBase`, 1b `hdrDq`, W0 `callErr_errorsNew`), 3 withdrawn; "from 1d (round 1)" met (`Client.Ctx.spec`; W0 round 3 + 1c `clientBare_assemble`); etcdserver "from 1d": 2e's to state, not rechecked.

## 1e (leasing)

Build: `etc/specs-build.sh --dir SpecPlan/Spec/go_etcd_io/etcd/client/v3/leasing` OK (68 modules) — was FAILED (`Api.lean:332,349,366,385,400`, `ctxPrin` arity); `go vet ./specreq/leasing/` clean, gofmt clean.

Changed:
- `leasing/Api.lean`: per-call principal (W0 round 3): every `LKV.*Triple` binds `p` with `ctxPrin who ctx p` (`who` the client's default), update `p`'s; `LKV.TxnTriple` returns `ltxnAt iv γ p …`. Auth window (W0 round 4): `LStep`/`lstep` take `lo`, step `Step who rq σ σ' res lo` (and for `execReq`); `LKV.GetTriple`, `LKV.DoTriple`, `LTxn.CommitTriple` bind `(lo)` with `authLb γ lo`; `Put`/`Delete` at `lo = 0`. `ProtoStep pfx σ σ'` (was `ProtoStep pfx who`): the protocol's requests run with the caller's context or the KV's own, so any principal; it now admits a real `leaseGrant`/`leaseKeepAlive` `Step` (W0's grant appends to `leaseHist`; the old inline clause did not); the grant clause cites `Concurrency.grantEff`; `protoUpd γ pfx` loses `who`; imports concurrency's Api. `evKey` → W0's `Event.key`.
- 14 internal `leasingKV__*` specs (`acquire`, `delete`, `deleteRange`, `deleteRangeRPC`, `get`, `monitorLease`, `put`, `rescind`, `revoke`, `revokeLeaseKvs`, `revokeRange`, `tryModifyOp`, `waitRescind`, `waitSession`): binder `(who p)`, `ctxPrin who ctx p`; those carrying the caller's update also `(lo)`, `authLb γ lo`, `lstep γL pfx p lo`. `txnLeasing__serverTxn.lean`: `lo`, `authLb γ lo`, `lstep … who lo`.
- `NewKV.lean`: `protoUpd γ pfx`, binder `sp` for the session's principal (`optCtxOk o who sp`); sketch: `Client.Ctx` via `clientBase` (`ctxPrin who ctx who`); `NewSession` over `clientRest`, its `etcdLb` from a no-op firing of `protoUpd`.
- Sketch text: `leasingKV__Put`, `__Delete` (`lo = 0`, `authLb γ 0` by its first disjunct), `__Do`.
- `examples/specreq/leasing/lifecycle.go`: the proxy's per-requester principals now covered (no longer "auth off").

Checked: bridging laws `kvAt_lkvAt`, `txnAt_ltxnAt`, `lkvAt_methods` consistent with W0's current `KV.*Triple`s (same `p`, `lo`, `authLb`, `ctxPrin` premises; W0's `Step p … lo` is `LStep`'s first case; the persistent leasing update yields W0's exclusive update for `Put`/`Delete` at `lo = 0` and the `□?` update for `Do`/`Commit`; `KV.CompactTriple`/`GetStreamTriple` by delegation / `Unimplemented`). Proxy: `clientMut_split` gives the `KV` field, `kvAt`, `clientRest` = what `NewKV` takes; `NewKV` consumes only `kvAt`, so the `kvHandle` readiness change does not affect it. Internal txns at the call's `p` and the caller's `lo`; protocol txns fire `protoUpd` at `lo = 0`; `get` via `KV.DoTriple`; watches via 1b's `WatchTriple`; `monitorSession` via 1d's `NewSession` (over `clientRest`; `effIn` ⊆ `ProtoStep`).
Requests: to 1e (`req/..._leasing.md` W0 items 1-2) met; from 1e (client_v3 "from 1e" 1-4, "from 1e (round 1)" item 5 per-request principal, concurrency 1-3) met.
Found for 1d (fixed by I1): `Concurrency.grantEff` did not append to `leaseHist`, so W0's real grant was not a `grantEff` step and `NewSession`'s `effIn` permission did not cover the grant it fires. I added `leaseHist := σ.leaseHist ++ [σ.leases]` to `grantEff` (`concurrency/Api.lean`).

## 1f (recipes, `SpecPlan/Spec/fmt`)

Build: `etc/specs-build.sh --dir SpecPlan/Spec/go_etcd_io/etcd/client/v3/experimental/recipes SpecPlan/Spec/fmt` OK (41 modules); `go vet ./specreq/recipes/` clean, gofmt clean.

Main finding (soundness): since 1b's round 3, `watchStep` gives a response's events only under `exactFrom σ.kv lo`; the recipes claimed them unconditionally. Watch-derived facts are now conditional; read-derived facts unchanged.

Changed (under `client/v3/experimental/recipes/`):
- `Api.lean`: imports `concurrency.Api`; slot `sessionAt` removed (and its `handles_persistent` conjunct); header: sessions are 1d's `Concurrency.isSession s c γ id` with `isClient c γ who` beside; contexts/principals rewritten for W0 round 3 (`ctxPrin_todo`/`_background`/`_child` give `ctxPrin who ctx who`); reads at `lo = 0`; new bullet: watch facts under `EtcdModel.exactFrom`.
- `newEphemeralKV`, `newUniqueEphemeralKV`, `newUniqueEphemeralKey`, `NewRWMutex`, `NewDoubleBarrier`: new binder `c`; `sessionAt s γ who id` → `Concurrency.isSession s c γ id ∗ isClient c γ who`.
- Under `exactFrom` (lo): `waitEvents`/`WaitEvents`/`WaitPrefixEvents` prefix claim (`rev`); `Barrier.Wait` `goneAt` (`σ0.kv.rev`); `DoubleBarrier.Enter` `readyPutAt` (`σ0.kv.rev`); `Queue.Dequeue` front condition and `v = kr.value` (`1`); `PriorityQueue.Dequeue` the same (`σ0.kv.rev`).
- Sketch wording: `deleteRevKey`, `putNewKV`, `DoubleBarrier.enteredClients` (`ctxPrin who ctx who`, `lo = 0`); `waitEvents`' loop invariant under `exactFrom`.
- Snippets: `barrier.go` package comment adds the compaction condition; `watch.go` `ReqWaitFirstDelete` assumes it, stale `watchHist`/`watchEvOwn_unfold` → `watchEvents`/`eventOwn_unfold`.

Provisional names: `sessionAt` resolved (→ `isSession` + `isClient`); `etcdPeek`, `dbPerm` (= W0 `etcdPerm` over `dbWrite`), watch slots already resolved. None left.
Sketches checked and fitting: `Watcher.WatchTriple`, `watchChAt_recv`, `WatchResponse.Err.spec`, `eventOwn_unfold` (Wire.lean), `Session.Client/Lease`, `KV.GetTriple`/`Txn.CommitTriple` at `lo = 0`, `pfxRange` (through `OpM.rangeReq`, so `endReq`), `etcdLb_init`, `etcdLb_revFits`, `putOnce`, `callErr_errorsNew`. The gating rests on a pure lemma clients prove: `exactFrom` at a later state implies it at an earlier one.
Requests to 1f: W0 round 2 (`Watch` non-nil channel) met. Requests 1f made: client_v3 "from 1f" items 1-5 met (item 2 only under `exactFrom`, 1b's form); concurrency "from 1f" met (different signature, restated); api_v3 "from 1f" met.
Needs (optional, 1b): an unconditional weak fact in `watchStep`'s events case (each delivered event is the last change of its key at its revision) would make `goneAt`/`readyPutAt` unconditional; the queues' front would stay conditional.

## 1g (cache, B-tree)

Build: `etc/specs-build.sh --dir SpecPlan/Spec/go_etcd_io/etcd/cache/v3 SpecPlan/Spec/k8s_io/utils/third_party/forked/golang/btree` OK (161 modules) — the cache was FAILED (`Cache__Get.lean:84`, `Cache__serverRevision.lean:33`, `Cache__get.lean:36`: `ctxPrin` arity); `go vet ./specreq/cache/ ./specreq/btree/` clean, gofmt clean.

Changed (B-tree: none):
- `cache/v3/Api.lean`: header paragraphs (compaction condition, principals, why the cache is not a `Watcher`); `deliv`, `quiet`, `getOk`: their exactness claims now under `EtcdModel.exactFrom h 0` at the fact's state; `eventOwn` now over W0's `EtcdWire.eventOwn p DFrac.discard m` (`m.del = e.del`, `m.prevKv = none`, `kvMatches e m.kv`), `evType` → `RevEvent.del`; `Cache.evKey` → W0's `Event.key`; `cacheRange` docstring: the cache treats `nil` and non-`nil` empty ends alike (one key: `len(endKey) == 0`), unlike W0's `OpM.endReq` — right for the cache's code.
- `Cache__Get.lean`, `Cache__serverRevision.lean`: binder `p`, premise `ctxPrin who ctx p`; `serverRevision`'s sketch: `KV.GetTriple` at `lo = 0`, `authLb γ 0`.
- `Cache__get.lean`: `ctxPrin who ctx who` (its only caller passes the cache's `WithCancel(Background())`, `cache.go:79, :332`); sketch: `lo = 0`, `etcdPeek` covers every range step, `endReq`.
- `Cache__watchEvents.lean`: sketch cited a `req/` note; now 1b's names (`watcherAt_methods`, `Watcher.WatchTriple` at `ctxPrin who ctx who`, `watchChAt_recvAu`, `watchStep`, `watchRespAt_persist`, `watchRespRO`, `EventM.isOf`, `WatchResponse.Err`, `exactFrom`).
- `Internal.lean` (header; `snapCert`'s content claim under the condition), `store__Get.lean` (same).
- `examples/specreq/cache/get.go`: package comment assumes `exactFrom σ.kv 0` at every reached state (an invariant clause the owner keeps).

Sketches that did not fit: (1) `ctxPrin` arity; (2) the compaction condition: the cache's events, progress and snapshots come from its upstream client watch, which 1b's `watchStep` states exact only under `exactFrom`; the cache claimed them unconditionally (unprovable). Now a condition at each fact's state (sound: the proof takes the latest combined state, `etcdLb_ord`, and the condition at a later state implies it at earlier ones). `0` is stronger than needed (users cannot see the upstream watch's start). Margin: the store's contents are right without it, but 1b's contract does not give that. (3) `watchEvents` cited a `req/` note.

Watch vocabulary (1g open question 1): recorded, not unified. The cache's `Watch` cannot meet 1b's `Watcher.WatchTriple`/`watchChAt`: (1) 1b's response owns events in full, the cache shares them read-only; (2) the cache's compaction cancel reports its own window, not a cluster compaction (`cr ≤ σ.kv.compacted` false); (3) a rejected request's lone cancel is no `watchStep` response; (4) `watchChAt` claims the call's principal was admitted, the cache checks no permission and serves its own principal's view; (5) no `Created`, fabricated headers. Unifying would need in 1b's `ApiWatch.lean`: an ownership index on `watchRespAt`; a `watchStep` case for a source-local cancel; one for a rejected request's lone cancel; the channel at the handle's principal. Done: the cheap part (events are W0's `EtcdWire.eventOwn`, one `eventOwn_unfold`).

Requests: to 1g (api_v3 "from 1g" 1, 2, 4) met; no other `req/` asks of cache/btree (mvcc cites `BTree.New`, `BTree.ItemOrder`: exist). Made by 1g (client_v3 "from 1g" 1-5): met (1 behind `exactFrom`), 5 decided above.
Need from W0 (`Wire.lean`): persistence at `DFrac.discard` of `protoRest`, `eventOwn`, `keyValueOwn`, `respHeaderOwn`, `rangeRespOwn` (the cache shares events and returns a read-only response; no law states it).
