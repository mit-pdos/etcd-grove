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

## Go findings (for `nonissues/`; not filed: outside my paths)

* **`NewLeaseFromLeaseClient(remote, nil, t)` leaves `l.lg` nil**; the receive and send loops call
  `l.lg.Warn` on a stream error (zap's `Logger.Warn` dereferences the receiver): a panic for a lessor
  made without a client once its keep-alive stream fails. `recvKeepAlive` guards its `Warn`, the
  loops do not. By code reading; `blocks-proof: no` (the spec takes a client).

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
