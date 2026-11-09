# Batch 1c: the client's lease, lifecycle, auth, cluster, maintenance APIs and interceptors

Author's report (round 0, before review). Built with `etc/specs-build.sh --dir` on every directory
below; snippets vet (`cd examples && go vet ./specreq/clientv3lease/ ./specreq/clientv3client/`,
gofmt-clean). Built against W0's round-1 names (`ctxPrin` in every triple, the new `EtcdErr`
constructors: the learner refusal is `.etcd .notSupportedForLearner`, `authFailed` a refusal).

## Files (≈160 modules)

| path | what |
|---|---|
| `Spec/go_etcd_io/etcd/client/v3/ApiClient.lean` (`ClientV3`) | the non-KV call shape (`CallTriple`, `CheckedCallTriple`, `RemoteCallTriple`), the retry interceptor's contract (`AttemptTriple`, `uiOk`, `siOk`), the configuration (`cfgOk`, `cfgPrincipal`, `idUpd`), the auth/cluster/maintenance bundles, the client's internal handles |
| `Spec/go_etcd_io/etcd/client/v3/ApiLease.lean` (`ClientV3`) | the lease bundle (`Lease.methods`), replies, `kaChan`, the keep-alive stream slots |
| `Spec/go_etcd_io/etcd/client/v3/*.lean` (125 files) | `lessor.*` (16), `keepAlive.close`, `NewLease`, `NewLeaseFromLeaseClient`, `RetryLeaseClient`, `retryLeaseClient.*` (5); `authClient.*` (18), `retryAuthClient.*` (17), `NewAuth`, `NewAuthFromAuthClient`, `RetryAuthClient`; `cluster.*` (7), `retryClusterClient.*` (5), `NewCluster`, `NewClusterFromClusterClient`, `RetryClusterClient`; `maintenance.{AlarmList,AlarmDisarm,Status}`, `retryMaintenanceClient.Alarm`, `NewMaintenance`, `NewMaintenanceFromMaintenanceClient`, `RetryMaintenanceClient`; `client.go`: `New`, `newClient`, `NewFromURL(s)`, `Client.{Close,Ctx,GetLogger,WithLogger,Endpoints,SetEndpoints,Sync,autoSync,dialSetupOpts,dial,dialWithBalancer,Dial,credentialsForEndpoint,getToken,roundRobinQuorumBackoff,checkVersion,ActiveConnection}`, `authority`, `isHaltErr`, `isUnavailableErr`, `canceledByCaller`, `IsConnCanceled`; `retry_interceptor.go`: `Client.{unaryClientInterceptor,streamClientInterceptor,shouldRefreshToken,refreshToken}`, `isSafeRetry`, `isContextError`, `contextErrToGRPCErr`, `waitRetryBackoff`, `withRepeatablePolicy`, `withMax`, `withBackoff`, `reuseOrNewWithCallOptions`, `filterCallOptions`, `backoffLinearWithJitter`; `logger.go`: `ClientLogLevel` |
| `Spec/go_etcd_io/etcd/client/v3/kubernetes/` (`Kubernetes`) | `Api.lean` (requests, replies, `Kube.*Triple`, `kubeAt`), `New`, `Client.{Get,List,Count,OptimisticPut,OptimisticDelete}`, `kvFromTxnResponse` |
| `.../client/v3/credentials/` (`Credentials`) | `Api.lean` (`tokFor`, `rpcCredsAt`, `tokenMd`, `bundleAt_unfold`), 7 specs |
| `.../client/v3/internal/{endpoint,resolver}/` (`Endpoint`, `Resolver`) | `RequiresCredentials`, `Interpret`; `Api.lean` (`resolverAt`), `New`, `SetEndpoints`, `Close` |
| `.../client/pkg/v3/{types,verify,transport,logutil}/` (`Types`, `Verify`, `Transport`, `Logutil`) | `NewURLs`, `IDFromString`, `ID.String`, `URLs.StringSlice` (`urlsValid`, `idStr`); `Verify`, `Assert` (`verifyOff`); `IsClosedConnError` (`errStrOk`); `CreateDefaultZapLogger` |
| `examples/specreq/clientv3lease/{grant,session,reads}.go` | 7 snippets |
| `examples/specreq/clientv3client/{lifecycle,auth,cluster,maint,kubernetes}.go` | 13 snippets |

New namespaces: `Kubernetes`, `Credentials`, `Endpoint`, `Resolver`, `Types`, `Verify`, `Transport`,
`Logutil`.

## Exported vocabulary

Pure: `errRetryAuth` (the token refusals), `reqRpc` (a request's gRPC method), `reqRetryRep` (the
retry wrappers' repeatable RPCs), `permTypeM`, `alarmKindM`, `RetryOptsM`/`applyRetry` (the
interceptor's options), `reqIsLease/Auth/Cluster/Maint`; Kubernetes' `getReqM`, `listReqM`,
`countReqM`, `optPutTxnM`, `optDeleteTxnM`; `Types.urlsValid` (opaque Prop), `Types.idStr`.

Shapes: `CallTriple e P B γ who rq rep reply` (the caller's update, persistent iff `rep`; the reply
or `indefCall`), `CheckedCallTriple` (a local check's failure gives the update back),
`RemoteCallTriple m P γ who rq` (wire level), `AttemptTriple inv cc P γ who` (one grpc attempt:
fired, fired with a definite error, **given back unfired** for not-sent/token/learner refusals, or
lost), `callAU`; the bundles `Auth.methods`, `Cluster.methods`, `Maint.methods`, `Lease.methods`,
`Kube.methods`/`Kube.*Triple`; replies `ansReply`, `authReply`, `leaseGrantReply`, `leaseTTLReply`,
`leaseLeasesReply`, `kaRespAt` (def), `kaRespOwn`, Kubernetes' `getReply`/`listReply`/`countReply`/
`txnReply`.

Predicates (opaque unless said): `replyOwn`, `reqOwn`, `statusRespOwn`, `userAddOptsAt` (3h);
`tokenOf` (3d), `tlsPrincipal` (2e), `tlsCfgOk`, `dialOptsOk`, `dialTargetOk`, `transportCredsOk`,
`grpcCallOptsOk`, `unaryArgs`, `kaSendAt`, `kaRecvAt` (2a slots); `cfgPrincipal`, `cfgOk` (def),
`idUpd` (def: the identity update), `clientPre`, `clientCore`, `clientDialOpts`, `bundleAt`,
`uiOk`, `siOk`, `retryOptAt` (and defs `repOptAt`, `maxOptAt`, `backoffOptAt`, `retryOptsAt`),
`optionsAt`, `backoffOk`; handles `authHandle`, `clusterHandle`, `maintHandle`, `lessorHandle`,
`remoteAuthAt`, `remoteClusterAt`, `remoteMaintAt`, `remoteLeaseAt`, `retry*Handle`, `kaChan`,
`kaEntry`, `kaDonec`, `kubeAt`, `Credentials.rpcCredsAt`, `tokenMd`, `Resolver.resolverAt`,
`Verify.verifyOff`, `Transport.errStrOk`.

Laws: `handles1c_persistent`, `handles1cLease_persistent`, `kubeAt_persistent`,
`cfgPrincipal_{user,token,tls,none}`, `dialOptsOk_nil`, `replyOwn_authenticate`, `callOptsOk_nil`,
`callOptsOk_full`, `callOptsOk_append`, `isClient_core`, `clientMut_core`, `clientCore_pre`,
`clientConnOk_core`, `clientMut_fields`, `uiOk_call`, `siOk_call`, `authAt_methods`,
`clusterAt_methods`, `maintAt_methods`, `leaseAt_methods`, `kubeAt_methods`, `*Handle_*At`,
`remote*At_call`, `remoteLeaseAt_keepAlive`, `kaSendAt_{send,closeSend,context}`, `kaRecvAt_recv`,
`kaChan_recv`, `kubeClient_kubeAt`, `Credentials.bundleAt_unfold`.

## Main decisions and changes from the old specs

1. **Repeatable RPCs take a persistent update even when they write.** `retry.go` marks `LeaseGrant`
   and `LeaseRevoke` (and `Alarm`, `MoveLeader`) repeatable: the interceptor resends them after
   `Unavailable`, which may follow an applied attempt. So `Grant` may grant two leases, and a
   `Revoke` may answer `ErrLeaseNotFound` for a lease it revoked. The old specs took exclusive
   updates (unsound against the resend). W0's "writes at most once" holds for every non-repeatable
   RPC (all KV writes, all auth/cluster writes).
2. **At-most-once is the interceptor's contract** (`AttemptTriple` → `uiOk_call`): a
   non-repeatable call is resent only after an attempt that grpc/the server report as unfired (not
   sent, a token refusal, a learner refusal); a token refusal it gives up on, or a failed refresh
   (`ErrAuthFailed`), it fires itself as a refusal. Needs 2a: those refusals give the update back.
3. **A keep-alive takes no update and says nothing of the lease** (`kaChan`: values about `id` with
   a positive TTL, read-only; closing is liveness). `KeepAlive` takes no thread token (1d's need).
4. **`TimeToLive` of an unknown lease is a reply** (TTL `-1`, GrantedTTL `0`), as the handler maps it.
5. **`New` takes any configuration `cfgOk` admits**: TLS, user/password or token (`cfgPrincipal`),
   Kubernetes' dial options (`dialOptsOk`), auto-sync with `ETCD_VERIFY` off, `RejectOldCluster`;
   old: plain endpoints, nothing else. The principal is derived from the configuration.
6. **`idUpd γ`**: the program grants the client an identity update for its own read-only calls
   (token refresh's `Authenticate`, auto-sync's `MemberList`); same as 1d's `etcdPerm γ readEff`.
7. **`Close` takes `isClient`** (persistent: idempotent, concurrent-safe) and gives nothing back:
   the client takes no counted resource. Calls after it fail indefinitely.
8. **Maintenance**: `Status` is member-local (no step, the reply's fields unconstrained);
   `AlarmDisarm` of one model alarm only.

## Left out (no old spec, no user in scope)

`serverStreamingRetryingStream.*` (never built: every stream's retry limit is `0`, `siOk`'s
premise), `maintenance.{Defragment,HashKV,Snapshot,SnapshotWithVersion,MoveLeader,Downgrade,save,
logAndCloseWithError}`, `snapshotReadCloser.Read`, `AlarmDisarm` of every alarm (`(0, NONE)`),
`NewCtxClient`, `WithZapLogger`, `SetLogger`, `minSupportedVersion`, `config.go`
(`NewClientConfig`, `newTLSConfig`, `ConfigSpec.Clone`, `AuthConfig.Empty`: etcdctl's),
`StrToPermissionType`, `ErrKeepAliveHalted.Error`, `endpoint.{translateEndpoint,mustSplit2,
schemeToCredsRequirement,extractHostFromHostPort}` (internal to the two specified),
`resolver.{Build,updateState,state,getCC}` (grpc calls `Build`; 2a). **`block_logger.go`**
(`newBlockLogger`, `blockLogger.recordWait`, old specs exist): the watch's helpers, left to 1b
(their closures' contracts are the watch stream's).

## Go findings (filed in round 1)

`issues/etcd-client-dial-empty-endpoints.md` (with a failing test), `nonissues/etcd-client-lessor-nil-logger.md`,
`nonissues/etcd-client-keepalive-close-never-closed.md`; `nonissues/etcd-client-dialoptions-unary-interceptor.md`
updated (the gRPC proxy).

## Open questions for the user

1. **The readiness gap** (W0's `clientConnOk`): `newClient` builds the members before `c.Auth` is
   set; a call through a member then would panic in a token refresh. None is made, but a
   persistent `clientConnOk` cannot express it. Proposal to W0 (req, item 1): a `clientReady c`
   witness in `kvHandle_kvAt` and the other bundle introductions. Your call whether to change W0's
   statements or accept the step as unprovable.
2. **Repeatable writes** (decision 1): the lease grant/revoke contract is weaker than "at most
   once". Acceptable, or should the fork make `LeaseGrant`/`LeaseRevoke` non-repeatable (an upstream
   question: etcd treats them as idempotent)?
3. **Scope premises**: `RoleGrantPermission`'s type among the three (`permTypeM`); `AlarmDisarm` of
   a model alarm; `LogConfig` without `Logger` out of scope; auto-sync only with `ETCD_VERIFY` off.
4. **`idUpd`** in `New`'s precondition: one shared read permission in W0's `State.lean` (1d/1f/1g
   ask the same).

## `req/` sections written (`## from 1c`)

`google_golang_org_grpc.md` (the attempt contract, the dial, status classification, the keep-alive
stream, credentials/resolvers, a stream's open refusal); `go_etcd_io_etcd_server_v3_etcdserver_api_v3rpc.md`
(lease/auth/cluster/maint answers, unfired refusals, TimeToLive's not-found reply, keep-alive ids,
`tokenOf`); `go_etcd_io_etcd_api_v3_etcdserverpb.md` (`replyOwn`/`reqOwn`, translate `Member`,
`MemberListResponse`, `StatusResponse`; stubs); `go_etcd_io_etcd_server_v3_etcdserver.md`
(`memberServes`, `tlsPrincipal`, `tokenOf`); `go_etcd_io_etcd_client_v3.md` (`## from 1c (to W0)`:
the readiness gap, `clientMut` only `KV` writable, `callOptsOk` full, stream open refusals, one read
permission, the lease model). Other batches' needs of 1c (1d, 1e) are met: `Ctx`/`GetLogger` under
`clientPre` (from `isClient`/`clientMut`), `KeepAlive` without a thread token, `Grant` with a
persistent update, `clientMut_fields`.

## Round 1 repairs (2026-11-09)

Reviews: `reviews/1c-provability-1.md` (P), `reviews/1c-completeness-1.md` (C), and W0's round-3 names
(the principal per call: `ctxPrin who ctx p`, `Step p`; `tokenUser`; `leaseViewLb`; the model's
int64 lease ids and TTLs, positive granted TTL, uint64 member ids: W0's "Round 3, second part").
Everything rebuilds (`etc/specs-build.sh --dir`: 348 + 31 modules); the snippets vet.

**First tier.**

| finding | repair |
|---|---|
| P-F1 `AttemptTriple` lost a not-sent update | case 4 is `∃ k, callErr err k ∗ ⌜k.indefinite ∧ k ≠ .notSent⌝`; req to 2a updated |
| P-F2 `cc` dereferenced | new slot `grpcConnAt cc` (2a) in `AttemptTriple`'s and `uiOk_call`'s pre |
| P-F3 `siOk_call`'s options | pre `callOptsOk opts rep` (no per-call option raises the limit: `callOptsOk_append`) |
| P-F4 readiness gap | `clientReady c` (persistent), minted by `newClient` once `c.Auth` is set (`isClient_ready`, `clientMut_ready`, `clientRest_ready`; `clientReady_null` for handles over a caller's remote); `uiOk_call`, `siOk_call`, `getToken`, `refreshToken`, `Sync`, `autoSync`, `checkVersion` take it; the handles record their client (`authHandle a c`, `clusterHandle`, `maintHandle`, `lessorHandle`, `retry*Handle`) and meet their bundles only with it; the constructors do not need it; `streamClientInterceptor` now over `clientPre` (its `getToken` runs only at a call, under `siOk_call`'s `clientReady`). W0's `kvHandle_kvAt` needs the same (req, "from 1c (round 1, to W0)", item 1) |
| P-F5 `dial` reads `c.endpoints[0]` unlocked and unchecked | `epsTok c dq eps` (fractional): `dial`, `dialWithBalancer`, `Dial`, `checkVersion`, `Maint.StatusTriple` take a fraction at a non-empty list, `SetEndpoints`/`Sync` the whole token; `New` gives it with auto-sync off (`epsTok_persist`, `clientVia`); `issues/etcd-client-dial-empty-endpoints.md` with a failing Go test (`SetEndpoints()` then `Maintenance.Status`: index out of range), the race in its text |
| P-F6 `cfgPrincipal_user` under client-cert auth | premise `⌜cfg.TLS' = null⌝ ∨ tlsPrincipal γ cfg.TLS' none` |
| P-F7/F8 integer ranges, `GrantedTTL > 0` | W0's model (round 3, second part): `leaseStep .leaseGrant` (int64 id, `0 < ttl' ≤ maxLeaseTTL`), `.leaseTimeToLive` (`0 < gttl < 2^63`), `EnvStep.alarm` (member id `< 2^64`); the snippets `ReqGrantTTL`, `ReqLeasesNoDup`, `ReqTimeToLiveAbout`, `ReqAlarmDisarm` follow |
| P-F9 / C-F8 `New` with no endpoint | post `⌜cfg.Endpoints'.len = 0 → c = null ∧ err ≠ nil⌝` (`New`, `newClient`) |
| C-F1 per-member lease reads | `Lease.GrantTriple` (through a frozen endpoint `ep`: `leaseViewLb γ ep` of the table it created) and `LeaseRead.Triple` (`TimeToLive`, `Leases`: from `leaseViewLb γ ep i`, answered at a table `j ≥ i`, `State.leaseAnsAt`, giving `leaseViewLb γ ep j`), over `leaseOf v c ∗ clientVia c ep` (`clientCore_leaseOf`); snippets `clientv3lease/member.go` (`ReqGrantThenListOneMember`, `ReqGoneNotListed`); `lessor__Leases.lean`'s users fixed |
| C-F2 `clientRest` | `clientRest_core` (hence `clientPre`, `clientBase`); `Client.Close` over `clientRest`; `Ctx`, `GetLogger`, `WithLogger` over `clientBase` |
| C-F3 in-process client | `NewCtxClient.spec`, `WithZapLogger.spec`, `clientBare`, `clientBare_base`, `clientBare_assemble` (→ `isClient c γ none ∗ clientReady c`, the principal per call); the `From*Client` constructors over `clientBase` (a bare client's); snippet `inproc.go`; req to W0 (item 2: `isClient_conn` is false for it) and to the server batch (the adapters' wire contracts) |
| C-F4 the gRPC proxy's client | `dialOptsOk` admits `WithUnaryInterceptor`/`WithStreamInterceptor` of interceptors calling the invoker at most once with the call's principal (the post of `uiOk_call` holds of any such: the unsettled refusals fired by a ghost step); req to 2a item 3; the nonissue names the proxy |
| C-F5 TLS | `Transport.tlsCfgOk` moved to `client/pkg/v3/transport` with `TLSInfo.ClientConfig.spec`; snippet `tls.go` (`ReqNewTLS`) |
| C-F6 promoted methods | `Client.{Grant,Revoke,TimeToLive,Leases,KeepAlive,KeepAliveOnce}`, the 18 `Client.<Auth method>`, `Client.{MemberAdd,MemberAddAsLearner,MemberRemove,MemberUpdate,MemberList,MemberPromote}`, `Client.{AlarmList,AlarmDisarm,Status}` over `clientRest`; the bundles restated per method over a method function `m` (`Call.Triple`, `Lease.*Triple`, `Cluster.*Triple`, `Maint.*Triple`); snippets use `cli.Status` |
| C-F7 refused principals | snippet `ReqRefusedPrincipals` (anon, foreign token); req to W0 item 3 (`ctxPrin` of an unissued token) |

**Second tier done.** P-S3 (the repeatable writes: req to W0 item 4; W0 already changed `top.md`),
P-S4 (findings filed), P-S5 / C-S4 / C-S6 (duplicated `ctxPrin`, `Status`'s subsumed disjunct,
`once.go`, `ReqCloseThenCalls`, `ReqLeasesGranted`, `ReqRefreshAtMostOnce` marked a ghost assertion),
C-S2 (`ReqEndpoints`' header), C-S5 (`Close` over `clientRest`). Also: `AlarmList` was applied to an
extra `#()` argument (fixed). **Not done**: P-S1 (`kaRecvAt` tracking the ids sent: `keepAliveOnce`'s
"about `id`" rests on 2a's handler copying `req.ID`, req item 4 of the v3rpc section), P-S2 (the
peer holder: requested of 2a, round 1 item 4), C-S1 (`ActiveConnection`'s `GetState`/`Connect`:
grpc's), C-S3 (Kubernetes `OptimisticDelete`/`Count` snippets).

**Renamed or changed names (for 1d, 1e, 1g).** `tokenOf` → W0's `tokenUser`; `Auth.Triple` →
`Call.Triple`; the bundles take a method function `m` (`Auth.methods m`, `Cluster.methods m`,
`Maint.methods m v`, `Lease.methods m v`); every triple takes the call's principal `p` with
`ctxPrin who ctx p`; handles take their client (`authHandle a c γ who`, ...); `Client.Ctx.spec` and
`Client.GetLogger.spec` take `clientBase c who` (from `isClient`/`clientRest` by `clientRest_core`,
`clientCore_pre`, `clientPre_base`); `NewLeaseFromLeaseClient` takes `clientBase c who`.

**Open questions left.** 1: W0's `kvHandle_kvAt` readiness (req). 2: `isClient_conn` for in-process
clients (req). 3: the per-call principal of an unissued token (req). 4 (from round 0): repeatable
lease writes stay weaker than at-most-once; the scope premises (`permTypeM`, `alarmKindM`,
`LogConfig`, auto-sync with `ETCD_VERIFY` off, `Status` only with the endpoints token).

## W0 round 4 (2026-11-09)

`RespBody.authenticate` has no token now: `authReply`'s success gives `∃ tok, authTokenAt resp tok ∗
tokenUser γ tok name` (`authTokenAt`, new, persistent, 3h's), and `replyOwn_authenticate` takes
`authTokenAt p tok` to expose the `Token` field. The read contracts' `lo` binder is W0's KV only:
1c's reads (lease, auth, member lists, Kubernetes' ranges) use `Step`'s default `lo = 0` (the
weakest, "any auth state"), which is sound and asks nothing of callers. Rebuilt: 1c's directories
(348 + 31 modules) and `Spec/go_etcd_io/etcd/api/v3/etcdserverpb` (85 modules) pass.

## W0 rounds 5–6 (2026-11-09)

`Req.alarmActivate` covered: `reqRpc` (`"Alarm"`), `reqRetryRep` (repeatable: the wrapper's `Alarm`),
`reqIsMaint` (so `remoteMaintAt_call` and `retryMaintenanceClient.Alarm.spec` cover a stub's
`Alarm(ACTIVATE)`; the `Maintenance` interface has no method for it). `AlarmKind.other`:
`alarmKindM` replaced by the total `alarmKindOf` (`NONE` and unknown types as `other`), so
`AlarmDisarm`'s scope premise is only "not `(0, NONE)`" (the disarm-all loop). Compact's `lo`
and `endReq` touch no 1c statement (1c issues no compaction; the Kubernetes ranges' requests are
`OpM.rangeReq`). Rebuilt: 1c's directories (348 + 31) pass. `--dir .../etcdserver/apply` and
`--dir .../etcdserver` both FAIL on another batch's file (2c's): `ApiReq.lean:235: Missing cases:
Req.alarmActivate` (its match over `Req` lacks the new constructor).
