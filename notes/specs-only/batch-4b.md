# Batch 4b: the storage schema, the pkg leaves, and their third-party boundaries

Author's report (2026-11-09). Everything builds: `etc/specs-build.sh --dir` of each directory below
(118 modules at the last full build, then the schema's 70 again after the last edits). Snippets:
`go vet ./specreq/pkgleaves/ ./specreq/schema/` clean, `gofmt -l` empty. The generator scripts are
scratch (`.lake/b4/`), not part of the branch.

## Files

| directory | namespace | files |
|---|---|---|
| `Spec/go_etcd_io/etcd/server/v3/storage/schema/` | `Schema` | `Api.lean` + 69 specs |
| `Spec/go_etcd_io/etcd/pkg/v3/traceutil/` | `TraceUtil` | `Api.lean` + 20 specs |
| `Spec/go_etcd_io/etcd/pkg/v3/pbutil/` | `PbUtil` | `Api.lean`, `MustMarshalMessage`, `MustUnmarshalMessage` |
| `Spec/go_etcd_io/etcd/pkg/v3/ioutil/` | `IoUtil` | `Api.lean` (2 laws), `NewLimitedBufferReader` |
| `Spec/go_etcd_io/etcd/pkg/v3/httputil/` | `HttpUtil` | `Api.lean`, `GracefulClose` (assumed) |
| `Spec/github_com/Masterminds/semver/v3/` | `Semver` | `Api.lean`, `MustParse`, `NewVersion`, `New`, `Version__{LessThan,Major,Minor,String}` (assumed) |
| `Spec/golang_org/x/time/rate/` | `Rate` | `Api.lean`, `Every`, `NewLimiter`, `Limiter__Wait`, `Limiter__Reserve`, `Reservation__Delay` (assumed) |
| `Spec/github_com/xiang90/probing/` | `Probing` | `Api.lean`, `NewProber`, `NewHandler` (assumed) |
| `Spec/go_opentelemetry_io/otel/trace/` | `OtelTrace` | `Api.lean`, `SpanFromContext`, `WithAttributes` (assumed) |
| `Spec/go_opentelemetry_io/otel/attribute/` | `OtelAttribute` | `Api.lean`, `String`, `Int64`, `Int`, `Bool` (assumed) |
| `examples/specreq/pkgleaves/` | | `trace.go` (5 snippets), `leaves.go` (10) |
| `examples/specreq/schema/` | | `schema.go` (6 snippets) |

otel was not named in the batch's row, but 2c's and 2b's sketches cite it as 4b's boundary
(`traceutil.Tracer.Start`, `trace.SpanFromContext`, `WithAttributes`, `attribute.*`), and no other
batch owns it.

Schema specs: `bucket.{ID,Name,String,IsSafeRangeBucket}`; the consistent index
(`UnsafeCreateMetaBucket`, `CreateMetaBucket`*, `UnsafeReadConsistentIndex`, `ReadConsistentIndex`,
`UnsafeUpdateConsistentIndex`, `UnsafeUpdateConsistentIndexForce`, `unsafeUpdateConsistentIndex`,
`MustUnsafeSaveConfStateToBackend`*); leases (`UnsafeCreateLeaseBucket`, `MustUnsafeGetAllLeases`*,
`MustUnsafePutLease`*, `UnsafeDeleteLease`*); auth (`NewAuthBackend`, `authBackend.{ReadTx,BatchTx,
ForceCommit,CreateAuthBuckets,GetUser,GetRole,GetAllUsers,GetAllRoles}`, `authBatchTx.{Lock,Unlock,
UnsafeSaveAuthEnabled,UnsafeSaveAuthRevision,UnsafeDeleteUser,UnsafeDeleteRole,UnsafePutUser,
UnsafePutRole}`, and the six reads `unsafeReadAuthEnabled`, `unsafeReadAuthRevision`,
`unsafeGetUser`, `unsafeGetAllUsers`, `unsafeGetRole`, `unsafeGetAllRoles` with their
`authBatchTx`/`authReadTx` methods, `UnsafeCreateAuthRolesBucket`); alarms (`NewAlarmBackend`,
`alarmBackend.{CreateAlarmBucket,MustPutAlarm,MustDeleteAlarm,GetAllAlarms,ForceCommit}`*);
membership (`NewMembershipBackend`, `membershipBackend.{MustCreateBackendBuckets,
MustSaveMemberToBackend,MustDeleteMemberFromBackend,MustReadMembersFromBackend,
MustSaveClusterVersionToBackend,MustSaveDowngradeToBackend,ClusterVersionFromBackend,
DowngradeInfoFromBackend}`*). (* translated names only: assumed specs, each saying why it is true.)

## The schema's design (the main decision)

**The schema is stated over what it needs of a transaction, not over the backend's predicates**
(PRINCIPLES, "An API is stated over the abstractions it builds on"; the shape of 3e's
`Mvcc.ApiStorage`). The functions take a `backend.UnsafeReader`/`UnsafeWriter`/`ReadTx`/`BatchTx`
and call its methods; their specs take the caller's bundle of those methods' triples:

* `txRd tx S R` (single-key `UnsafeRange`, `UnsafeForEach` in key order), `txRange tx S R` (interval
  `UnsafeRange` of a whole bucket: batch transactions only, or `key`; etcd's read transactions panic
  on another bucket), `txWr tx S R` (`UnsafePut`, `UnsafeDelete`, `UnsafeCreateBucket`), at the
  **caller's** view family `R : View → IProp` and its scope `S` (whole buckets, or keys of a shared
  bucket: the consistent index owns two keys of `Meta`, mvcc two others and `Meta`'s existence);
* for the struct methods that lock (`authBackend.*`, `authBatchTx.Lock/Unlock`,
  `ReadConsistentIndex`, `CreateMetaBucket`): the backend calls' triples as premises (`retOk`,
  `callOk`, `rdSect`, `wrSect`), so the caller's own contract (lock invariant, post-lock hook,
  reader slot) passes through unchanged;
* the values are pure encodings: `ciOf`/`ciPut`/`ciWf` (big-endian `uint64`s), `leaseBktIs m L`
  (the lease table), `authEnabledOf`, `authRevOf`, `recsWf`/`recRes`/`recsRes` (users and roles as
  `Proto` contents), `rangeOf`, `entsOf`.

The names-only alarm and membership backends lock internally and are assumed; they are stated over
two schema-owned resources, `alarmBkt be al` and `memberBkts be cb` (2e's `beAlarms`/`beMembers`),
with `applyHook be Pre Q` (provisional, 4a's) for the post-lock hook their writers run.

Consequence for the callers (a decision for the user, below): the per-concern slots they declared
as "4b's" (`Lease.beLeases be B`, `Auth.authBackendAt be a`, `Cindex.beStoredCI`/`txStoredCI`) are
not provided as opaque schema predicates; each is the caller's realization of `R` over 4a's part
ownership, with the schema's encodings (`req/` sections say how). 4a owes the laws producing the
bundles for its transactions (`req/go_etcd_io_etcd_server_v3_storage_backend.md`, "from 4b").

## Exported vocabulary

**Schema** (`storage/schema/Api.lean`): `Bkt` (`name`, `id`, `safe`, `var`), key names (`ciKey`,
`termKey`, `confStateKey`, `storageVersionKey`, `schedKey`, `finKey`, `authEnabledKey`,
`authRevKey`, `clusterVersionKey`, `downgradeKey`), `BData`, `View` (`put`, `del`, `set`,
`create`), `Scope` (`whole`, `has`, `reads`, `ofBkts`), `ciScope`, `rangeOf`, `entsOf`, `beU64`,
`u64Of`, `u64Ok`, `ciOf`, `ciWf`, `ciPut`, `LeaseRec`, `leaseModel` (opaque), `leaseEnc`,
`leaseBktIs`, `authEnabledOf`, `authRevOf`, `authRevWf`, `recsWf`, `userName`/`roleName`/
`alarmMemberIs` (opaque, provisional 3h's), `alarmsIns`, `alarmsDel`, `ClusterBkts`; resources
`bucketIs`, `bucketAt` (persistent), `bytesListAt`, `txRd`, `txRange`, `txWr`, `callOk`, `retOk`,
`rdSect`, `wrSect`, `leaseAt`, `recRes`, `recsRes`, `alarmBkt` (excl.), `memberBkts` (excl.),
`applyHook` (provisional 4a's). Laws: `bucketAt_persistent`, `bucketVars_init` (each bucket variable
holds a `bucketAt` value), `keyNames_init` (the key-name variables and `authEnabled`/`authDisabled`),
`leaseMsg_of_struct`, `leaseMsg_to_struct` (the `leasepb.Lease` message laws: no other owner),
`alarmBkt_{timeless,excl}`, `memberBkts_{timeless,excl}`.

**TraceUtil**: `traceOwn t` (exclusive, timeless, non-nil), `traceEmpty t e` (persistent: the
`isEmpty` flag, never written after creation), `ctxTraceIs ctx o` (persistent: the context's trace),
`fieldsOwn sl` (transparent: an owned slice of formattable fields), `fieldsFmt`, `traceOpt`,
`traceKey`, `tracerAt`. Laws: `traceOwn_{timeless,excl,ne_null}`, `traceEmpty_{persistent,agree}`,
`ctxTraceIs_{persistent,agree,background,todo,child,value}`, `tracer_init`.

**Semver**: `SemVer` (transparent), `parse` (opaque), `preLtb` (opaque), `render`, `SemVer.ltb`,
`verOf`, `verAt v sv` (transparent, persistent). Laws: `parse_render`, `parse_plain`,
`parse_version`.

**Rate**: `limiterOk`, `reservationOk` (persistent). **Probing**: `proberOk` (bundle).
**OtelTrace**: `spanOk` (bundle), `ctxSpanOk` (persistent) with `_background`, `_todo`, `_child`,
`_value`. **IoUtil**: `rcVal`, laws `ReaderAndCloser_reader`, `ReaderAndCloser_closer` (in 2f's
`Http.readerAt`/`readerCloser`). **PbUtil**, **HttpUtil**, **OtelAttribute**: none (`Proto`'s and
`Http`'s vocabulary).

## Main changes from the old specs

* Schema: every spec restated from the real backend's ghost state (`isBackend γ P W Pk b`,
  `batchLocked`, `rbOwnIn`, `metaReader`/`metaWriter`, put tokens) to the transaction contracts; the
  auth batch side (puts, deletes, lock, unlock: none before) and the cluster-version/downgrade
  membership methods are new. The CI update no longer needs `Meta` to exist at index `0` (the
  pre-commit hook of a commit before anything is applied returns first). `UnsafeUpdateConsistentIndex`'s
  check is `Verify.verifyOff ∨ i = 0 ∨ stored ≤ i`.
* Bucket values: no constant per bucket (the name slices are allocated at init): `bucketAt b bv`.
* Traces: one exclusive `traceOwn` with the emptiness split off as the persistent `traceEmpty`;
  `IsEmpty` needs only `traceEmpty`; `EnsureTrace` over any `Context.ctxOk` (was mvcc's `txnCtx`
  descriptor), its post giving W0's `ctxWithValues`/`ctxValueAt` at `traceKey` (each package's
  "another key" law carries its own fact, in place of listing grpc's metadata, otel's span, the
  start time); a context's trace is no longer owned through the context.
* pbutil over `Proto` (the old `PbType` record was unsound); semver with a value model (old: "some
  boolean"); rate's `Wait` over W0's `ctxOk`; probing's handler over 2f's `Http.handlerOk`.
* `GracefulClose` takes the reader owned (the old `respReadAny` shared a reader of no guarantee).

## Left out (no old spec, or names only with no translated caller)

schema: `MustUnsafeGetLease`, `leaseIDToBytes`, `bytesToLeaseID`, `mustParseMemberIDFromBytes`,
`TrimClusterFromBackend`, `TrimMembershipFromBackend`, `UnsafeConfStateFromBackend`, the migration and
storage-version files (`migration.go`, `version.go`, `schema.go`, `actions.go`, `changes.go`),
`DefaultIgnores`, `BackendMemberKey`, and the alarm/membership internals (`mustUnsafePutAlarm`,
`mustUnsafeDeleteAlarm`, `unsafeGetAllAlarms`, `readMembersFromBackend`: covered by their callers'
assumed specs). traceutil: `Init`, `Log`, `logInfo`, `writeFields`, `Field.format`. pbutil:
`MustMarshal`, `MustUnmarshal`, `MaybeUnmarshal`, `GetBool`, `Boolp`. ioutil: `NewExactReadCloser`
(its user `snap.NewMessage` is trusted whole), `exactReadCloser.*`, `limitedBufferReader.Read`
(covered by `NewLimitedBufferReader`'s post), `WriteAndSyncFile`, `PageWriter`. httputil:
`GetHostname`. semver: all but the seven. rate: `AllowN`, `ReserveN`, `DelayFrom`. probing: `Status`
and the status methods (2f's `addPeerToProber` is assumed whole).

## Open questions for the user

1. **The schema over transaction contracts** (above): the callers' per-concern slots (3c's
   `beLeases`, 3d's `authBackendAt`, 2d's `beStoredCI`/`txStoredCI`) become their realizations over
   4a's parts, not schema predicates. The alternative, opaque schema predicates over a backend, would
   need 4a's lock and part vocabulary in the schema's statements (4a's API does not exist yet).
2. **Traces are exclusive** (`traceOwn`), not 2c/3b/3a's persistent `traceAt`: a trace's methods
   race (`t.steps = append(...)` without a lock), so the persistent form is false. Their specs must
   thread `traceOwn`/`traceOpt` (as 3e's already does).
3. **Scope: no distributed tracing.** `TraceUtil.tracer_init` assumes `traceutil.Init` is never
   called (`embed` calls it with `--experimental-enable-distributed-tracing`); with it, the variable is
   rewritten once at start-up and the persistent `tracerAt` is false.
4. **The snapshot sender's timeout drain** (`snapshot_sender.go:169`): `GracefulClose` from a
   `time.AfterFunc` goroutine reads the body while the sender's `io.ReadAll` does, so neither sees a
   prefix of the response; 2f's sketch of `snapshotSender.post` assumes a shared closer only. Not a
   panic (Go's body reads are locked), so not an issue file; 2f needs a shared reader of trivial
   knowledge (requested).
5. **`Cindex.beStoredCI` (2d) is unsound as a persistent fact** (commits change the stored index);
   the read is `ReadConsistentIndex.spec` over the read section's triples.
6. **3e's `Mvcc.bucketVal` constants are unprovable**, and its contract's `KeyData.range` of `Meta`
   claims every non-compaction key is absent: both requested of 3e (`bucketAt`; restrict the asked
   keys).

## `req/` sections written (all "## from 4b")

* `go_etcd_io_etcd_server_v3_storage_backend.md` (4a): the bundles to prove for its transactions
  (batch with the lock held; read between `RLock`/`RUnlock`; the shared read transaction under the
  batch lock, `cindex.go:107`), per-part ownership, the lock triples, `applyHook`, the opener's parts
  for `alarmBkt`/`memberBkts`, bucket values via `bucketAt`.
* `go_etcd_io_etcd_server_v3_storage_mvcc.md` (3e): `traceOwn`, `bucketAt`, `keyNames_init`,
  `UnsafeCreateMetaBucket`, the `Meta` range row.
* `go_etcd_io_etcd_server_v3_etcdserver.md` (2c, 2d, 2e): traces, the consistent index, bootstrap.
* `go_etcd_io_etcd_server_v3_lease.md` (3c), `..._auth.md` (3d), `..._api_v3alarm.md` (2e),
  `..._api_membership.md` (2e): how each slot is realized and the specs to cite.
* `net_http.md` (2f): the drain, the probes' closed world, `semverAt`/`semverParses`.
* `google_golang_org_grpc.md` (2a): the per-call context's `ctxTraceIs ctx none`, `ctxSpanOk`.
* `context.md` (W0): name `TODO()`'s value (`context.todoCtxVal`).
* `go_etcd_io_etcd_api_v3_etcdserverpb.md` (3h): `userName`/`roleName` with a `Name`-field law,
  `alarmMemberIs` with `noMaps`, and the auth/alarm messages' `marshalOk`.
