# Which etcd axioms can be proved now (2026-11-18, branch `axiom-triage`)

The user's goal: "if there were any axioms which we wrote for expediency, it's now time to just prove
them and get rid of them from our TCB". This file is the triage. It covers every axiom declared under
`Proof/go_etcd_io/etcd/**` that a top-level etcd theorem rests on: the union of the `axiom` lines of
the 23 collections `etc/tcb-collections/{auth3,authN,authkv,cachekv,compactkv,leaseN,leasecatchup,
leaseexpiry,leaseexpiryN,leasekv,linkv3p,linkvtxn,m2,putget,putget3,putgetN,restart1,restart3,
restartN,txnlinfaultsN,wal-tester,watchkv,k8setcd3}.txt` at `origin/lean` `058f91f219`. That is 317
axioms: 196 outside the package initializers and 121 `<X>_init`/`errorsNewVarsInit` axioms in
generated `Init.lean` files. Each package's `opaqueInitsOk`/`initFuncsOk` (54 etcd packages) is
treated in aggregate below.

Each axiom was checked against the Go source at the pin (`.lake/go-src/etcd`), its Goose
configuration (`Code/**/*.toml`), Perennial at the pin (`6d365ee1a`: `Code/*.toml`, `Spec/`,
`Proof/`), and its own spec's precondition and postcondition. File headers were not trusted. Several
are stale: `pbutil.MustUnmarshalMessage`'s says pbutil is names-only, but it is translated;
`URLs.StringSlice`'s says `URLs` is axiomatized, but it is a `GoSlice`; `snap/Defs.lean` calls
`snap.Message` axiomatized, but it is a translated struct; `errMemberNotFound_init` says
`errors.New`, but the code is `fmt.Errorf`.

## Classes

- **A**: provable now as stated. The body and every callee translate, and every callee has a spec
  (or gets one from code that already translates). The table says what to add to which
  `Code/**/*.toml`.
- **A\***: provable now, but the axiom's spec cannot be proved as it stands, so the proof forces a
  spec or invariant change. Usually the precondition lacks the ownership the body needs (a lock's
  invariant, a points-to). Sometimes the postcondition is an opaque predicate that would have to be
  defined. The importer count says how far the change reaches.
- **A-swap**: provable, but only over a new leaf axiom of the same strength (for example a
  `semver.NewVersion` spec, or `proto.Unmarshal` at a new message type). The trust base gets no
  smaller, so it is not a target.
- **B**: blocked by a gap in Perennial's model. The gap is named.
- **C**: blocked by Goose.
- **D**: not a function. It is an opaque predicate or a fact; the table says what would discharge it.
- **E**: assigned elsewhere. `lessor-noax` has `lease.NewLessor`, `lessor.Stop`, `lessorStopTok`,
  `lessor.Demote` and `schema.UnsafeDeleteLease`. `authstore-noax` has `auth.NewAuthStore`.
  `bbolt-integrate` has the backend's bbolt model: `backend.*` in `InvBbolt.lean`,
  `backend.optsAt` (its S2), `backend.Snapshot`, `snapshot.*`, `storage.OpenBackend`,
  `storage.storage.Release` and `snap.Snapshotter.*`.

"Importers" counts the modules that import the axiom's `Spec` module (`[n]` below). "Uses" counts the
collections, out of 23, whose trust base holds the axiom. Proof sizes are estimates in Lean lines.

## Summary

The 196 axioms outside the initializers:

| class | count |
|---|---|
| A (provable as stated) | 23 |
| A\* (provable with a spec change) | 23 |
| A-swap (no net gain) | 2 |
| B (Perennial model gap) | 50 |
| C (Goose) | 4 |
| D (not a function) | 57 |
| E (assigned elsewhere) | 37 |

D includes the 33 `pb*_reg` registrations (28 in the client's `PerType*`, 2 in v3rpc's, 1 in
rafthttp's, 2 in walpb's).

The 121 initializer axioms: 26 A (literal or `errors.New` initializers), 27 B-grpc-status, 62
B-prometheus, 2 B-float, 1 B-grpc options, 1 B-otel, 1 B-protobuf, 1 E (`boltOpenOptions`). See
"Package initializers" below.

### Blockers, ranked by how many axioms each would unblock

| blocker | axioms (non-init + init) | notes |
|---|---|---|
| prometheus metrics (`New*` initializers, `Set/Add/Observe(float64)`) | 6 + 62 | Each metric would become a translated call over `prometheus` trust specs (the `leaseExpired` precedent). That moves axioms rather than removing them, unless prometheus itself is modeled. Usually floats as well. |
| a protobuf-go model (marshal/unmarshal/size; reflection-based `String`) | about 18 + 1, plus the 33 `_reg` (D) | `AlarmType.String`, `RangeRequest.String`, `Event_EventType.StringPtr`, `NewLoggableTxnRequest`, `MustUnsafeGetAllLeases`/`PutLease` (A with a per-type leaf spec, as `UnmarshalUser`), `msgEncC_ok`, `recEncC_ok`, `snapEncC_ok`, `irrDecode_utf8`, `codec_proto`, `logUnaryRequestStats`, `WarnOf*`, `linkHeartbeatSize_init`. The `_reg` family needs a concrete registry definition (see D). |
| grpc `status` (names-only) | 27 init (`ErrGRPC*`, `Err* = Error(ErrGRPC*)`, `errStringToError`) + `errDesc_etcdError` (D) | `status.Error`/`FromError` modeled from grpc's code would discharge them all. |
| floats (arithmetic, float to int conversion) | 9 + 2 | `lessor.Promote`, `scheduleCheckpointIfNeeded`, `leaseTimeToLive`, `FollowerStats.Succ`, `roundRobinQuorumBackoff`, `txn.*SecObserve`, `NewBackendQuota`, `addFeatureGateMetrics` (with prometheus), `defaultBackoffJitterFraction`, `defaultOptions` |
| `encoding/json` | 5 | `MustSaveMemberToBackend`, `MustReadMembersFromBackend`, `MustUnsafeSaveConfStateToBackend`, `membersOf_decode`, `memberEnc_id_learner`; also part of `RaftCluster.Recover` and `clusterImageOk_restModel` |
| grpc internals (ClientConn, `manual.Resolver`, metadata) | 6 + D 2 | `Client.Close`, `resolver.{New,SetEndpoints,Close}`, `etcdResolverOwn`/`_grpc`; grpc `metadata` is plain Go and would translate (it unblocks the A\* `withVersion`/`WithRequireLeader`, which also need `outgoingOf` turned into a heap predicate) |
| `fmt` `%v`/`%+v` of non-strings | 5 | `adjustTicks` (`tickToDur`), `publishV3`, `streamKeyFromCtx` (+2 D `streamKeyOf_*`), `LogWithStepThreshold`, `RaftCluster.String` |
| crc32 | 3 | `newKVHasher`, `kvHasher.WriteKeyValue`, `kvHasher.Hash` |
| crypto / bcrypt / base64 / hex / jwt / x509 | 4 | `redactToken`, `selectPassword`, `newTokenProviderJWT`, `AuthInfoFromTLS` |
| `strconv.FormatUint` names-only in Perennial | 0 directly | `strconv.FormatUint.wp_proof` is already a repository trust-boundary axiom in all 23 trust bases, so `types.ID.String` can be proved over it (A). A Perennial `FormatUint` would remove that axiom too. `strconv.NumError.Error`/`Quote` (names-only) block `IDFromString` as stated. |
| semver (regexp) | 2 + A-swap 1 | `monitorClusterVersions`, `monitorStorageVersion`, `version.Cluster` |
| net/http, `io.Copy`, net transports | 4 | `GracefulClose`, `NewRoundTripper`, `newStreamRoundTripper`, `addPeerToProber` |
| `sort.Slice` (reflectlite) | 1 | `hashStorage.Store` |
| `sync/atomic.Value` | 1 | `NewDefaultServerFeatureGate` |
| otel | 1 + 1 | `Tracer.Start`, `Tracer_init` |
| reflect | 2 | `WarnOfExpensiveRequest`, `WarnOfFailedRequest` (`isNil`) |
| `runtime.FDUsage` | 1 | `monitorFileDescriptor` |
| Goose: anonymous struct field | 4 | `serverStats.LeaderInfo`: `NewServerStats`, `BecomeLeader`, `RecvAppendReq`, `SendAppendReq` (a fork change naming the struct would make them A) |

### Class A, by downstream impact

Every one is in all 23 trust bases unless "uses" says otherwise.

| axiom | importers | toml change | est. lines | spec change? |
|---|---|---|---|---|
| `types.ID.String_ptr` | [29] | `client/pkg/v3/types.toml`: `ID.String`, imports `strconv` | 10 (given `ID.String`) | no |
| `types.ID.String` | [18] | same | 50, mostly the pure lemma `fmtUint id 16 = idStr id` | no; it rests on the existing `strconv.FormatUint` axiom |
| `verify.Verify` | [7] | `client/pkg/v3/verify.toml`: `Verify`, `IsVerificationEnabled`, `getEnvVerify`, `verifier`, the `envVerify*` constants; imports `os`, `strings` | 40 | no; but `os.Getenv`'s and `strings.ToLower`'s axioms, in 1 trust base today, would then be reached by 22: a swap, not a gain, until they are proved |
| `backend.VerifyBackendConsistency` | [3] | `backend.toml` | 15 | no, but it needs an "env off" spec of `verify.IsVerificationEnabled` (below) |
| `backend.ValidateCalledInsideApply`, `ValidateCalledOutSideApply` | [2] each | `backend.toml`: these, `verifyLockEnabled`, `insideApply`, `EnvVerifyValueLock` | 15 each | no; with one shared trust spec "`IsVerificationEnabled(_)` returns false under `verifyEnvOff`", which replaces 4 axioms by 1 (`os.Getenv`'s spec says only "some string", so it cannot be derived) |
| `transport.IsClosedConnError` | [2] | `client/pkg/v3/transport.toml`: `IsClosedConnError`, imports `strings` | 20 | no; but over `strings.Contains`'s axiom, which only 1 of the 23 trust bases has: no net gain until `strings.Contains` is proved (it was translated and reverted on this branch for that reason) |
| `version.LessThan` | [2] | `api/v3/version.toml`: `LessThan`, imports semver | 15 | no (over the existing `semver.Version.LessThan` axiom) |
| `NewCluster` (client) | [2], 19 uses | `client/v3.toml`: `NewCluster`, `RetryClusterClient`; `etcdserverpb.toml`: `NewClusterClient`, `clusterClient` | 25 | no |
| `NewMaintenance` (client) | [2], 19 uses | `client/v3.toml`: `NewMaintenance`, `RetryMaintenanceClient`; `etcdserverpb.toml`: `NewMaintenanceClient`, `maintenanceClient` | 30 | no |
| `config.ServerConfig.PeerDialTimeout` | [2] | `config.toml`: `ServerConfig.PeerDialTimeout` | 10 | no |
| `newCorruptionChecker` | [2] | `etcdserver.toml`: `newCorruptionChecker` (the types are translated) | 15 | no |
| `EtcdServer.monitorKVHash` | [2] | `etcdserver.toml`: `EtcdServer.monitorKVHash` | 10 | no (the spec covers only `CorruptCheckTime = 0`: one load, return) |
| `RaftCluster.SetVersionChangedNotifier` | [2] | `membership.toml`: it | 10 | no |
| `waitRetryBackoff` | [2], 19 uses | `client/v3.toml`: `waitRetryBackoff`, `contextErrToGRPCErr` | 200 | no |
| `endpoint.RequiresCredentials` | [2], 19 uses | `client/v3/internal/endpoint.toml`: it, `translateEndpoint`, `mustSplit2`, `schemeToCredsRequirement` | 80, plus specs for `url.Parse` and an exact `strings.SplitN` | no |
| `auth.tokenSimple.genTokenPrefix` | [2], 3 uses | `auth.toml`: it, `letters`, `defaultSimpleTokenLength`; imports `crypto/rand`, `math/big` (Perennial models `rand.Int`, `big.NewInt`, `Int.Int64`) | 70 | no |
| `RaftCluster.SetBackend` | [2] | `membership.toml`: it; `schema.toml`: `membershipBackend.MustCreateBackendBuckets` and the buckets `Members`, `MembersRemoved`, `Cluster` (with init facts like `Lease`'s) | 150 | no |
| `schema.membershipBackend.MustDeleteMemberFromBackend` | [4] | `schema.toml`: it, `BackendMemberKey`, the member buckets; imports `client/pkg/v3/types` | 120 (bridging the backend's predicates to `rbPart`/`rbOwnIn`) | no; pairs with defining `memberKey := idStr` (`memberKey_inj`, D) |
| `v3alarm.AlarmStore.restore` | [2] | `v3alarm.toml`: it, `addToMap`; `schema.toml`: the alarm backend's `CreateAlarmBucket`, `GetAllAlarms`, `unsafeGetAllAlarms`, `ForceCommit`, `Alarm` | 200, plus a read transaction `UnsafeForEach` spec over an empty bucket | no |
| `v3alarm.NewAlarmStore` | [2] | the above plus `NewAlarmStore`, `Activate`, `Deactivate` and the schema alarm writers | 400+ | no, but `MustPutAlarm` needs `proto.Marshal` of `AlarmMember` (a per-type leaf: partly A-swap) |
| `v3rpc.NewMaintenanceServer` | [2] | `etcdserver/version.toml`: imports `context`, semver, `api/v3/version`; `etcdserver.toml`: `NewServerVersionAdapter` | 60 | no (it changes the version package's init chain) |
| `types.NewURLs` | [4] | types: `NewURLs`, `URLs.Sort/Less/Swap`; net/url: `Parse`, `URL.String` (names-only, translatable); `net.SplitHostPort` | 1000+ | no |

### Class A\*, provable with a spec change

| axiom | importers | the change | est. lines |
|---|---|---|---|
| `Client.Endpoints` | [7] | `retryClientOk` gets an `epMu` RWMutex invariant over `endpoints`, and the call takes a reader or thread token (the toml says so) | 40 |
| `credentials.perRPCCredential.GetRequestMetadata`, `.UpdateAuthToken` | [2] each, 8 files use `credTokInv` | `credTokInv` (a bare `inv`) becomes the `authTokenMu` lock's invariant, and the client's call specs thread `threadTok` (c1-plan finding 2, option 2) | 40 + 25 |
| `types.IDFromString` | [3], 12 uses | drop `http.errStrOk err` from the post (`NumError.Error`, names-only in Perennial, would be needed). Both callers (`addRemoteFromRequest`, `streamHandler.ServeHTTP`) use only the `idStr` conjunct | 80 (Perennial's `ParseUint` spec plus `parseUint (idStr x) 16 64 = ok x`) |
| `types.URLs.StringSlice` | [2] | the precondition `p ≠ null` gains `p ↦{dq} us ∗ us ↦* uvs`; needs a `url.URL.String` spec | 40 + URL.String |
| `config.ServerConfig.BackendPath` | [3] | a new `storage/datadir.toml` (`ToBackendFileName`, `ToSnapDir`, `ToMemberDir`); define `backendPathOf` over `filepath`'s `joinModel`; the spec gains `isPkgInit config` and a length bound on `d` (`Spec/path/filepath/Join.lean` needs it) | 50 |
| `EtcdServer.ensureLeadership` | [2], 2 uses | translate `isActive`, `raftStatus`. `getLatestTickTs`'s spec needs `tickMu`'s reader slots, which the invariant dropped at NodeStart (a thread pool for them); `zap.Time` needs a spec; `LinearizableReadNotify`'s premises must be derived from the `WithTimeout` context | 150 |
| `EtcdServer.monitorCompactHash` | [2] | the spec gains `isFeatureGate fg` (`FeatureEnabled` needs it); translate `features.CompactHashCheck` | 15 |
| `EtcdServer.monitorDowngrade` | [2] | the spec gains `zapLoggerOk l`; translate `version.NewMonitor`/`Monitor` with their imports, and `NewServerVersionAdapter` | 30 |
| `EtcdServer.purgeFile` | [2] | needs a spec of `fileutil.PurgeFileWithDoneNotify` (translated) over `fsExt`, and a WAL-directory sharing protocol with the WAL's locks | several hundred |
| `api.IsCapabilityEnabled` | [3], 19 uses | translate `enableMapMu`, `enabledMap`, `init`; the package fact (today `True`) gets the lock with an invariant (`enabledMap` nil or a read-only map). `UpdateCapability`, passed as a value to `RaftCluster.Recover`/`SetVersion`, needs a spec; the call needs a reader token | 60 |
| `storage.BackendQuota.Cost` | [2] | no `proto.Size` at this pin: `len(Key)+len(Value)` and a recursive `costTxn`. The spec's `r ≠ null` gains read ownership of the request tree; translate `RequestOp.GetRequestPut/GetRequestTxn` | 120 |
| `rafthttp.Transport.ActiveSince` | [3] | it is already translated; the spec needs `t.mu`'s reader token (its docstring says so); `peer.activeSince`/`peerStatus.activeSince` need specs | 80 |
| `rafthttp.waitSchedule` | [2] | `runtime.Gosched` has a Perennial spec; the precondition `True` becomes `isPkgInit rafthttp` (the caller has it); drop `!waitSchedule` and import `runtime` | 15 |
| `snap.Message.CloseNotify`, `.GetTo`, `.CloseWithError`, `snap.NewMessage` (+ `snap.Message.fields`, D) | [2] to [4] | define the opaque `msgRO`/`msgCloseRO` from `NewMessage`'s translation; `CloseWithError` gains the `closeC` channel; `NewMessage` needs `ioutil.NewExactReadCloser` translated and its reader proved | 15 + 20 + 40 + 230 |
| `v2stats.FollowerStats.Fail` | [2] | the spec has only `fs ≠ null`; it needs `isFollowerStats fs` (the mutex owning `Counts`), so `LeaderStats.Follower`'s post and `lsFollowers` carry it | 30 |
| `v3rpc.isClientCtxErr` | [4] | `status.FromError`'s spec needs `statusErrOk err ∗ errorMsgIs e m`, which the spec lacks | 40 |
| `Client.streamClientInterceptor` | [2] | the post `etcdStreamInterceptor` (axiomatized) must be defined as what grpc's `NewStream` needs; `serverStreamingRetryingStream`'s methods proved | hundreds |
| `withVersion`, `WithRequireLeader` | [2] each, 32 files mention `outgoingOf` | translate grpc `metadata`; `outgoingOf` (heap-independent, opaque) becomes a heap predicate; an exact `strings.ToLower` spec | hundreds |

These also count as A\*: `httputil.GracefulClose` and `Client.Close` are B first (`io.Copy`, grpc
`ClientConn.Close`), and their specs also lack ownership (`respCloser`; the client's `cancel`,
`Watcher`, `Lease`). `mvcc.hashStorage.Store` is B (`sort.Slice`), and its spec also lacks `hashMu`.

### A-swap (no net gain)

Two axioms, plus part of `NewAlarmStore`'s work:


- `version.Cluster`: needs a `semver.NewVersion` leaf spec (semver uses `regexp`).
- `pbutil.MustUnmarshalMessage`: already translated; needs a `proto.Unmarshal` leaf spec at
  `InternalRaftRequest` giving `irrDecode`.
- `v3alarm.NewAlarmStore`'s alarm writers: a `proto.Marshal` leaf at `AlarmMember` (listed under A
  for the rest of its work).

## Every axiom

Paths are relative to `Proof/go_etcd_io/etcd/`; Go locations are under `.lake/go-src/etcd`.

### api/v3, client/pkg/v3, pkg/v3

| axiom | class | Go | reason |
|---|---|---|---|
| `etcdserverpb.AlarmType.String` | B | `api/etcdserverpb/rpc.pb.go:58` | `protoimpl.X.EnumStringOf` (protobuf reflection) |
| `NewLoggableTxnRequest` | B | `raft_internal_stringer.go:81` | the body is trivial, but the post `stringerOk` needs `txnRequestStringer.String`, i.e. `MessageStringOf` of the ops |
| `RangeRequest.String` | B | `rpc.pb.go:578` | `MessageStringOf` (reflective text format) |
| `mvccpb.Event_EventType.StringPtr` | B | `api/mvccpb/kv.pb.go:50` | `EnumStringOf` |
| `rpctypes.errDesc_etcdError` | D | `api/v3rpc/rpctypes/error.go` | a fact about the opaque `errDesc`; discharged by a model of grpc `status.FromError` |
| `version.Cluster` | A-swap | `api/version/version.go:69` | `semver.NewVersion` (regexp) as a new leaf; `Sprintf %d/%s`, `strings.Split` have specs |
| `version.LessThan` | A | `version.go:84` | `semver.Version.LessThan`'s spec exists |
| `transport.IsClosedConnError` | A | `client/pkg/transport/listener.go:617` | `err.Error()` from `errStrOk`; `strings.Contains` spec exists |
| `types.IDFromString` | A\* | `client/pkg/types/id.go:32` | Perennial's `ParseUint` is verified; `NumError.Error` is names-only, so `errStrOk` must go |
| `types.ID.String` | A | `id.go:27` | over `strconv.FormatUint`'s existing axiom and a pure lemma |
| `types.ID.String_ptr` | A | (wrapper) | follows from `ID.String` |
| `types.NewURLs` | A (heavy) | `urls.go:28` | net/url `Parse`, `net.SplitHostPort`, `TrimSpace`, `sort.Sort` with `URL.String` |
| `types.URLs.StringSlice` | A\* | `urls.go:79` | needs `p ↦ us` and `url.URL.String` |
| `envVerifyOffTok`, `verifyEnvOff` (verify/Env.lean) | D | `client/pkg/verify/verify.go` | an environment fact; discharged only by an environment model (ghost env map, `Getenv` returning its value) |
| `verify.Verify` | A | `verify.go:69` | `os.Getenv` (an existing axiom), `strings.ToLower`; the panic branch is unreachable since `f` returns true |
| `httputil.GracefulClose` | B | `pkg/httputil/httputil.go:32` | `io.Copy` names-only in Perennial; the spec also lacks `respCloser` |
| `pbutil.MustUnmarshalMessage` | A-swap | `pkg/pbutil/pbutil.go:61` | translated already; `proto.Unmarshal` at the IRR needs a leaf |
| `traceutil.Trace.LogWithStepThreshold` | B | `pkg/traceutil/trace.go:192` | `Sprintf("%v", any)`, `Duration.String`, `rand.Int31` |
| `traceutil.Tracer.Start` | B | `trace.go:32` | otel interface on a swappable package variable |

### client/v3

| axiom | class | Go | reason |
|---|---|---|---|
| `Client.Close` | B | `client.go:147` | grpc `ClientConn.Close` (names-only); the spec also lacks the fields |
| `Client.Endpoints` | A\* | `client.go:167` | no `epMu` invariant in `retryClientOk` |
| `Client.roundRobinQuorumBackoff` | B | `client.go:491` | `jitterUp`: floats, `rand.Float64` |
| `Client.streamClientInterceptor` | A\* (heavy) | `retry_interceptor.go:117` | opaque `etcdStreamInterceptor` |
| `etcdResolverOwn`, `etcdResolver_grpc` (InvClientNew.lean) | D | `internal/resolver/resolver.go` | opaque grpc resolver ownership; needs grpc's `manual.Resolver` modeled |
| `NewCluster` | A | `cluster.go:60` | allocations |
| `NewMaintenance` | A | `maintenance.go:114` | allocations; the `dial` closure is only built |
| `WithRequireLeader` | A\* (heavy) | `ctx.go:28` | grpc metadata translatable; `outgoingOf` opaque |
| `withVersion` | A\* (heavy) | `ctx.go:41` | same |
| `streamKeyFromCtx` | B | `watch.go:1102` | `Sprintf("%+v", map)` |
| `streamKeyOf_none`, `streamKeyOf_single` (StreamKey.lean) | D | — | laws of the opaque `streamKeyOf`; needs a finite sorted `GrpcMd` and fmt's `%+v` of maps |
| `waitRetryBackoff` | A | `retry_interceptor.go:317` | timers modeled; `status.Error` spec exists |
| `credentials.perRPCCredential.GetRequestMetadata` | A\* | `credentials/credentials.go:69` | `authTokenMu` not in `credTokInv` |
| `credentials.perRPCCredential.UpdateAuthToken` | A\* | `credentials.go:79` | same |
| `endpoint.RequiresCredentials` | A | `internal/endpoint/endpoint.go:122` | needs `url.Parse` and an exact `SplitN` spec |
| `resolver.EtcdManualResolver.Close` | B | (promoted, grpc) | grpc internals |
| `resolver.EtcdManualResolver.SetEndpoints` | B | `resolver.go:52` | grpc `manual.Resolver.CC/UpdateState` |
| `resolver.New` | B | `resolver.go:37` | grpc `manual.NewBuilderWithScheme` |
| `pb*T_reg` (28: PerTypeAuth 12, PerTypeKV 2, PerTypeKVRest 7, PerTypeLease 6, PerTypeTxn 1) | D | — | registrations of per-message models in the opaque `grpcReqModelOf`/`grpcRepModelOf` (`grpc/InvGrpc.lean`). Discharged by defining the registries as one concrete match over all registered types, in a module importing every `PerType*` (each `_reg` then by computation, given the types are distinct): a repository-wide refactor, no Go |

### server/v3: auth, config, features, lease, etcdserver

| axiom | class | Go | reason |
|---|---|---|---|
| `auth.NewAuthStore` | E | | `authstore-noax` |
| `auth.authStore.AuthInfoFromTLS` | B | `server/auth/store.go:1025` | `credentials.TLSInfo`, x509 axiomatized; `peer.FromContext` |
| `auth.authStore.selectPassword` | B | `store.go:420` | bcrypt, base64 |
| `auth.newTokenProviderJWT` | B | `jwt.go:127` | golang-jwt, crypto key types |
| `auth.redactToken` | B | `store.go:1250` | sha256, hex |
| `auth.tokenSimple.genTokenPrefix` | A | `simple_token.go:110` | Perennial models `crypto/rand.Int` and `math/big` |
| `config.ServerConfig.BackendPath` | A\* | `config.go:352` | see the A\* table |
| `config.ServerConfig.PeerDialTimeout` | A | `config.go:326` | the shape of the proved `ElectionTimeout` |
| `features.NewDefaultServerFeatureGate` | B | `server/features/etcd_features.go:112` | featuregate's `atomic.Value` of maps |
| `lease.NewLessor`, `lease.lessor.Stop`, `lease.lessorStopTok`, `lease.lessor.Demote` | E | | `lessor-noax` |
| `lease.lessor.Promote` | B | `lessor.go:480` | float `rateDelay` |
| `lease.lessor.scheduleCheckpointIfNeeded` | B | `lessor.go:753` | `int64(Duration.Seconds())` |
| `EtcdServer.adjustTicks` | B | `server.go:464` | `tickToDur` = `Sprintf("%v", Duration)`; `ActivePeers` needs a spec |
| `EtcdServer.ensureLeadership` | A\* | `server.go:912` | see the A\* table |
| `EtcdServer.leaseTimeToLive` | B | `v3_server.go:636` | float conversion; `leasehttp` |
| `EtcdServer.monitorClusterVersions` | B | `server.go:2247` | serverversion over HTTP/JSON, semver |
| `EtcdServer.monitorCompactHash` | A\* | `server.go:2316` | needs `isFeatureGate fg` |
| `EtcdServer.monitorDowngrade` | A\* | `server.go:2373` | needs `zapLoggerOk l`; version `Monitor` translated |
| `EtcdServer.monitorKVHash` | A | `server.go:2285` | the spec's case returns at once |
| `EtcdServer.monitorStorageVersion` | B | `server.go:2270` | schema migration, semver |
| `EtcdServer.publishV3` | B | `server.go:1834` | `Sprintf("%+v", struct)` |
| `EtcdServer.purgeFile` | A\* (heavy) | `server.go:608` | file-system ownership of the WAL directory |
| `membership.membersOfBk_empty` (InvRest.lean) | D | `schema/membership.go:91` | define `membersOf` as a fold of the bucket entries with an opaque per-entry decoder; then pure, about 30 lines |
| `membership.membersOf_decode` (InvRest.lean) | D (B) | same | a JSON round trip |
| `addFeatureGateMetrics` | B | `server.go:2502` | prometheus, float; featuregate `GetAll` |
| `api.IsCapabilityEnabled` | A\* | `api/capability.go:85` | see the A\* table |
| `apply.irrDecode_utf8` (InvRequest.lean) | D (B) | | a protobuf unmarshal fact |
| `apply.memberEnc_id_learner` (RestModel.lean) | D (B) | `membership/member.go` | `json.Marshal` |
| `apply.memberKey_inj` (RestModel.lean) | D (cheap) | `schema/bucket.go:106` | define `memberKey := types.idStr` (what `BackendMemberKey` computes through `ID.String`) and prove `hexNatF` injective: pure, about 40 lines |
| `monitorFileDescriptor` | B | `metrics.go:215` | `runtime.FDUsage`, prometheus |
| `newCorruptionChecker` | A | `corrupt.go:63` | a struct literal |
| `txn.ApplySecObserve`, `txn.RangeSecObserve` | B | `txn/metrics.go:59,63` | floats, prometheus, `FormatBool` |
| `txn.WarnOfExpensiveRequest`, `txn.WarnOfFailedRequest` | B | `txn/util.go:29,40` | `reflect` (`isNil`), `proto.Size`, stringers |

### server/v3/etcdserver/api

| axiom | class | Go | reason |
|---|---|---|---|
| `membership.RaftCluster.Recover` | B | `membership/cluster.go:262` | semver `MustParse`, JSON, prometheus, `ID.String` |
| `membership.RaftCluster.SetBackend` | A | `cluster.go:247` | backend specs exist (`lessor.initAndRecover`'s pattern) |
| `membership.RaftCluster.SetVersionChangedNotifier` | A | `cluster.go:252` | a field store the spec owns |
| `membership.RaftCluster.String` | B | `cluster.go:213` | `fmt.Fprintf`, `%+v` |
| `membership.RaftCluster.updateMembershipMetric` | B | `cluster.go:861` | prometheus, float |
| `membership.clusterImageOk_restModel` | D | | a rest-model fact; needs a JSON model of `Member` and semver |
| `membership.setIsLearnerMetric` | B | `metrics.go:46` | prometheus gauge |
| `rafthttp.netErrNotRemoved_ok` (NetErr.lean) | D | | net/http errors are not rafthttp's; needs a provenance model of net/http errors |
| `rafthttp.NewRoundTripper`, `rafthttp.newStreamRoundTripper` | B | `rafthttp/util.go:47,59` | `http.Transport`, TLS, dialer |
| `msgEncC_ok` (PerTypeMessage.lean) | D (B) | | protobuf `Marshal`/`Size` of `raftpb.Message` |
| `pbMessageC_reg` | D | | registry (as the client's `_reg`) |
| `rafthttp.Transport.ActiveSince` | A\* | `transport.go:400` | a reader token |
| `rafthttp.addPeerToProber` | B | `probing_status.go:41` | floats, prometheus, `xiang90/probing` |
| `rafthttp.waitSchedule` | A\* | `pipeline.go:179` | `isPkgInit rafthttp` |
| `snap.Message.CloseNotify`, `.CloseWithError`, `.GetTo`, `snap.NewMessage` | A\* | `snap/message.go` | define `msgRO`/`msgCloseRO` |
| `snap.Message.fields` | D | | a fact of the opaque `msgRO`; goes with the four above |
| `snap.Snapshotter.DBFilePath`, `.SaveDBFrom` | E | | `bbolt-integrate` |
| `v2stats.FollowerStats.Fail` | A\* | `v2stats/leader.go:131` | no lock ownership in the spec |
| `v2stats.FollowerStats.Succ` | B | `leader.go:104` | floats, `math.Sqrt` |
| `v2stats.NewServerStats`, `ServerStats.BecomeLeader`, `.RecvAppendReq`, `.SendAppendReq` | C | `v2stats/server.go` | the anonymous struct field `serverStats.LeaderInfo` (confirmed: `serverStats.underlying` is an axiom of the translation) |
| `v3alarm.AlarmStore.restore` | A | `v3alarm/alarms.go:112` | see the A table |
| `v3alarm.NewAlarmStore` | A (large) | `alarms.go:44` | see the A table |
| `v3rpc.ctxCauseOk_cancellable` (InvCancellable.lean) | D | | a fact about `context`'s causes; needs a cause invariant in Perennial's context model |
| `v3rpc.codec_proto` (InvGrpcStart.lean) | D (B) | `v3rpc/codec.go` | golang/protobuf v1 marshal, prometheus |
| `v3rpc.NewMaintenanceServer` | A | `maintenance.go:97` | see the A table |
| `etcd_noRefusal` (NoRefusal.lean) | D | | a whole-system fact; needs server specs that track error identity, and a "voter for life" invariant |
| `v3rpc.pbWatchRequestT_reg`, `v3rpc.pbWatchResponseT_reg` | D | | registry |
| `v3rpc.incomingOf_cancellableContext` (WrapperMd.lean) | D | | grpc metadata's opaque `incomingOf`; needs metadata modeled |
| `v3rpc.isClientCtxErr` | A\* | `v3rpc/util.go:110` | `FromError`'s premises |
| `v3rpc.logUnaryRequestStats` | B | `interceptor.go:91` | prototext `String()`, `peer`, zap `Core().Enabled` |

### server/v3/storage

| axiom | class | Go | reason |
|---|---|---|---|
| `storage.BackendQuota.Cost` | A\* | `storage/quota.go:136` | request-tree ownership |
| `storage.NewBackendQuota` | B | `quota.go:75` | prometheus `Set(float64)`, `humanize.Bytes` |
| `storage.OpenBackend`, `storage.storage.Release` | E | | `bbolt-integrate` |
| `dataDirFresh` (WalDir.lean) | D | | an opaque file-system token. Discharged by defining it over `fsExt`'s directory ownership (absent or empty) and giving it to adequacy from the initial file state (`bbolt-integrate`'s "Open" item) |
| `walFiles` (WalRecs.lean) | D | | an opaque token of a closed WAL's files. Discharged by defining it over `fsExt` points-tos and the WAL encoding (now proved over `fsExt`): `Close` makes it, bootstrap consumes it |
| `backend.optsAt` (BboltOptsDefs.lean) | E | | `bbolt-integrate` S2 (translate bbolt's `Options`) |
| the 22 `backend.*` of InvBbolt.lean | E | | `bbolt-integrate` |
| `backend.ValidateCalledInsideApply`, `ValidateCalledOutSideApply`, `VerifyBackendConsistency` | A | `backend/verify.go:31,40,73` | see the A table |
| `backend.backend.Snapshot`, `backend.snapshot.{Close,Size,WriteTo}` | E | | `bbolt-integrate` |
| `mvcc.ReportEventReceived` | B | `mvcc/metrics.go:318` | prometheus, float |
| `mvcc.hashStorage.Store` | B | `mvcc/hash.go:156` | `sort.Slice` (reflectlite); the spec also lacks `hashMu` |
| `mvcc.kvHasher.Hash`, `.WriteKeyValue`, `mvcc.newKVHasher` | B | `hash.go:49-92` | crc32 |
| `schema.MustUnsafeGetAllLeases` | B | `schema/lease.go:31` | `proto.Unmarshal` of `leasepb.Lease` (A-swap with a per-type leaf, as `UnmarshalUser`) and `UnsafeForEach` |
| `schema.MustUnsafePutLease` | B | `lease.go:48` | `proto.Marshal` of `leasepb.Lease` (A-swap with a leaf) |
| `schema.MustUnsafeSaveConfStateToBackend` | B | `confstate.go:29` | `encoding/json` |
| `schema.UnsafeDeleteLease` | E | | `lessor-noax` |
| `schema.membershipBackend.MustDeleteMemberFromBackend` | A | `membership.go:73` | see the A table |
| `schema.membershipBackend.MustReadMembersFromBackend`, `.MustSaveMemberToBackend` | B | `membership.go:83,50` | `encoding/json` |
| `pbRecordC_reg`, `pbSnapC_reg` (walpb) | D | | registry |
| `recEncC_ok`, `snapEncC_ok` (walpb) | D (B) | | a round trip of the opaque protobuf decoders; discharged by defining them as Lean wire decoders (the link to `proto.Unmarshal` stays trusted) |

## Package initializers

121 `<X>_init`/`errorsNewVarsInit` axioms, in 21 generated `Init.lean` files, by kind:

- **A (26)**: initializers that are literals, `errors.New` or `fmt.Errorf` calls, maps or slices of
  those, or other packages' variables: rpctypes' `TokenFieldNameGRPC`, `TokenFieldNameSwagger`,
  `MetadataClientAPIVersionKey`, `MetadataRequireLeaderKey`, `MetadataHasLeader`; version's
  `Version`, `MinClusterVersion`; the client's `LeaseResponseChSize`, `defaultBackoffWaitBetween`,
  `defaultUnaryMaxRetries`; leasehttp's `LeasePrefix`; mvcc's `defaultCompactionBatchLimit`,
  `defaultCompactionSleepInterval`; schema's `ScheduledCompactKeyName`, `FinishedCompactKeyName`,
  `AllBuckets` (once the bucket variables translate); rafthttp's `snapResponseReadTimeout`,
  `supportedStream`, `errMemberNotFound` (`fmt.Errorf`, trusted in Perennial); etcdserverpb's
  `RangeRequest_SortOrder_name`, `RangeRequest_SortTarget_name` (map literals); v3rpc's
  `toGRPCErrorMap` (a map keyed by interfaces, from other packages' facts: check that Goose's map
  handles interface keys); and the four `errorsNewVarsInit` (etcdserver/errors, membership,
  rafthttp, k8s etcd3 metrics), `errors.New` being translated in Perennial (the precedent is
  bbolt's errors). Each needs its variable in the package's toml `translate`, and an
  `etc/gen-init.py` `SPECIAL` entry whose generated proof runs the translated initializer. Cheap,
  but each touches a generated, widely imported `Init.lean`, so it rebuilds most of the server.
- **B-grpc-status (27)**: `ErrGRPC* = status.Error(...)`, `Err* = Error(ErrGRPC*)`,
  `errStringToError`.
- **B-prometheus (62)**: the metrics of etcdserver, rafthttp, v3rpc, mvcc, backend, lease, txn,
  apply, membership and wal.
- **B-float (2)**: `defaultBackoffJitterFraction`, `defaultOptions` (`backoffLinearWithJitter(...,
  0.10)`). **B-grpc (1)**: `defaultCallOpts`. **B-otel (1)**: `Tracer`. **B-protobuf (1)**:
  `linkHeartbeatSize = proto.Size(...)`. **E (1)**: `boltOpenOptions` (bbolt's `Options`).

`opaqueInitsOk`/`initFuncsOk` (one each per package; 54 in etcd packages) say that the package's
remaining untranslated initializers and `init()` functions return. They are discharged only when
every opaque initializer of the package is translated. In practice they hold protobuf's generated
`file_*_init` registrations (B-protobuf), prometheus `MustRegister` calls in `init()` (B), and
expvar/capability registrations (`api`'s `init` writes `enabledMap`: needed for
`IsCapabilityEnabled`, A\*). None goes away before the B gaps of its package are closed.

## Done on this branch (Part 2, 2026-11-18)

Ten axioms are gone: eight in every one of the 22 server collections, and the two client
constructors in the 19 that build a client.

| axiom | how |
|---|---|
| `types.ID.String` | translated; over `strconv.FormatUint`'s (existing) spec and `types.idStr_fmtUint` (`IDStr.lean`) |
| `types.ID.String_ptr` | translated (the wrapper); over `ID.String` |
| `version.LessThan` | translated; over semver's `Version.LessThan` (existing) |
| `config.ServerConfig.PeerDialTimeout` | translated (as `ElectionTimeout`) |
| `newCorruptionChecker` | translated (a struct literal) |
| `membership.RaftCluster.SetVersionChangedNotifier` | translated (a field store) |
| `rafthttp.waitSchedule` | translated; over Perennial's `runtime.Gosched`; the spec's precondition gained `isPkgInit rafthttp` (ledger, 2026-11-18) |
| `apply.memberKey_inj` | `memberKey` defined as `types.idStr` (what `BackendMemberKey` computes), so injectivity is `types.idStr_inj` |
| `NewCluster`, `NewMaintenance` (client) | translated with `RetryClusterClient`/`RetryMaintenanceClient` and the stubs' `New*Client`: four new specs, all proved |

Tried and reverted: `transport.IsClosedConnError`, which would rest on `strings.Contains`'s axiom (a
swap). Left: `monitorKVHash` (A), whose body needs `schema` imported into etcdserver; that changes
the package's initializer and its fact.

## Order of work (Part 2)

The cheapest leaves first, then by impact. None overlaps the assigned work: the `ID.String` pair,
`verify.Verify`, `PeerDialTimeout`, `newCorruptionChecker`, `monitorKVHash`,
`SetVersionChangedNotifier`, `IsClosedConnError`, `version.LessThan`, `NewCluster`/`NewMaintenance`,
then the three backend `Validate*`/`Verify*` (one new trust spec for four axioms), and the pure D
`memberKey_inj`. What was done is in `notes/STATUS.md`'s entry for this branch.
