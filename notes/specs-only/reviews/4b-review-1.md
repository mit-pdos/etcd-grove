# Batch 4b, review round 1 (provability and completeness)

Reviewer's report, 2026-11-09, at `242ebdf411`. Targets: `SpecPlan/Spec/go_etcd_io/etcd/server/v3/storage/schema/`
(Api + 69 specs), `SpecPlan/Spec/go_etcd_io/etcd/pkg/v3/{traceutil,pbutil,ioutil,httputil}/`, the
boundaries `SpecPlan/Spec/github_com/Masterminds/semver/v3/`, `SpecPlan/Spec/golang_org/x/time/rate/`,
`SpecPlan/Spec/github_com/xiang90/probing/`, `SpecPlan/Spec/go_opentelemetry_io/otel/{trace,attribute}/`, snippets
`examples/specreq/{schema,pkgleaves}/`, the `## from 4b` sections of `req/`. Go: the pinned sources in
`.lake/src/`, otel v1.47.0, semver v3.5.0, x/time v0.16.0, probing `a49e3df8f510` (the versions
`server/go.mod` pins). One run outside the repository (`/tmp/rv4b`, semver v3.5.0) to check F5.

## First tier (a hard rule broken)

### F1. `txRd`/`txRange`/the `ForEach` visitor hand out read-only-forever bytes that bbolt only lends (schema `Api.lean:334-380`)

`txRd`'s `UnsafeRange` gives `bytesListAt kl …`/`bytesListAt vl …` (`p ↦*□ b`, persistent, for good),
and its `UnsafeForEach` calls `f` with `ks ↦*□ k`, `vs ↦*□ v`. The backend's ranges return bbolt's
own slices (`batch_tx.go:206-226`, `unsafeRange` over `bucket.Cursor()`; `read_tx.go:120`), which
bbolt says are valid only while the transaction is live; 4c states exactly that
(`SpecPlan/Spec/go_etcd_io/bbolt/Api.lean:68`, `txBytes`, read through `txBytes_acc.spec` *with* `boltTx`,
`Api.lean:357-360`). The read transaction is rolled back at every batch commit and the mapping can
be replaced after that (a remap on growth), so a slice kept past the section is not readable. 4a
cannot prove `txRd` from 4c (its own draft, `baseReadTx__UnsafeRange.lean`, `batchTx__UnsafeRange.lean`,
makes the same claim and has the same problem, and so does 3e's `Mvcc.rangeOk`, `ApiStorage.lean:283`).
No schema function needs more: each one decodes the bytes inside the section (`Uint64`,
`proto.Unmarshal` (which copies by default), `bytes.Equal`; `unsafeGetAllUsers` keeps `vs` only until
it unmarshals them, before `RUnlock`).
**Fix**: lend the bytes against the view, e.g. `UnsafeRange`'s continuation gets
`∃ dq, bytesListAtQ kl dq … ∗ bytesListAtQ vl dq … ∗ ((bytesListAtQ … -∗ bytesListAtQ …) -∗ R V)`
in place of `R V ∗ bytesListAt …`, or one law `R V ∗ readOf … ⊢ …` that gives them while `R V` is
held. The same for `ForEach`'s visitor (`ks ↦*{dq} k` lent for the call). Tell 4a and 3e (their
drafts make the same claim).

### F2. `txRd`'s single-key range admits a non-`nil` empty end, on which etcd's read transaction panics (schema `Api.lean:344-352`)

`txRd`'s `UnsafeRange` row takes any `es ↦*{de} e` with `e = []`. `baseReadTx.UnsafeRange`
(`read_tx.go:78-88`) sets `limit = 1` only when `endKey == nil`; a non-`nil` empty end with
`limit = 0` becomes `MaxInt64`, and on any bucket but `Key` it `panic("do not use unsafeRange on
non-keys bucket")`. So 4a cannot prove `txRd` for a read transaction (its own draft's
`baseReadTx.UnsafeRange.spec` takes `bi.safe ∨ es = slice.nil ∨ limit = 1`; 3e's `rangeOk` takes
`e = [] → es = slice.nil`). On `Key` a non-`nil` empty end skips the buffer's single-key path and can
return a stale bolt value, so `txRange` for a read transaction of `key` has the same gap.
**Fix**: `⌜es = slice.nil⌝` in `txRd`'s single-key row (every schema caller passes `nil`), and
`⌜e = [] → es = slice.nil⌝` in `txRange`.

### F3. `txRd`'s `UnsafeForEach` "in key order" is false of etcd's read transaction; `GetAllUsers` and `authReadTx.UnsafeGetAllUsers` inherit it (schema `Api.lean:353-365`, `authBackend__GetAllUsers.lean`, `unsafeGetAllUsers.lean`, `MustUnsafeGetAllLeases.lean`)

`baseReadTx.UnsafeForEach` (`read_tx.go:54-76`) visits bolt's entries not in the buffer (in key
order), **then** the buffer's (`txr.buf.ForEach`, in key order): the concatenation is not sorted
when the read buffer holds a key below one of bolt's (a user added since the last commit:
`batchTxBuffered.Unlock` writes the batch buffer back, `batch_tx.go:328-360`; `authBatchTx.Unlock`'s
commit, `auth.go:115-119`, clears it again, so the window is short but real). The batch
transaction's `ForEach` is sorted (bolt's write transaction, `batch_tx.go:250-259`). `GetAllUsers`
goes through `ReadTx()` (`auth_users.go`, `GetAllUsers`), so its post `entsOf m l` ("in name
order") is false there, and 4a cannot prove `txRd` of a read transaction at all. No caller needs the
order: `UserList` copies the names as they come (`auth/store.go:601-608`; 3d's
`authStore__UserList.lean` says "the order is not stated"), `RoleDelete`/`refreshRangePermCache`
iterate, the lessor builds a map, the alarm and membership readers build sets and maps.
(Not a Go bug: `AuthUserList`'s order is not documented; no issue file.)
**Fix**: `ForEach` visits each entry of `m` exactly once in some order (`I` over a list `l` with
`l.Perm` of the entries, or a set), and the posts of `unsafeGetAllUsers`, `*.UnsafeGetAllUsers`,
`GetAllUsers` and `MustUnsafeGetAllLeases` say "each once" (`List.Perm` of `entsOf`'s list), not
sorted. Keep `txRange`'s key order (batch only).

### F4. `txWr`'s `UnsafePut` has no key/size premise; the backend `Fatal`s outside bbolt's limits (schema `Api.lean:386-393`)

`batchTx.unsafePut` calls `bucket.Put` and `lg.Fatal`s on its error (`batch_tx.go:183-189`); bbolt
refuses an empty key, a key above `maxKeySize`, and needs `kb.length + vb.length ≤ bboltEntryMax`
(`SpecPlan/Spec/go_etcd_io/bbolt/Bucket__Put.lean`; 4a's draft `batchTx.UnsafePut.spec` takes
`k.length + v.length ≤ Bbolt.bboltEntryMax`). `txWr` promises `R (V.put b k v)` for every `k`, `v`:
4a cannot prove it. The schema's writers whose sizes are the caller's choice
(`authBatchTx.UnsafePutUser`/`UnsafePutRole`: a name and a message of the client's;
`MustUnsafeSaveConfStateToBackend`: the JSON of a configuration) then promise success the code does
not give. 3d already carries the premise for it (`Auth.recordsFit`, its `req/` note, item 1).
**Fix**: `⌜k ≠ [] ∧ k.length ≤ Bbolt.maxKeySize ∧ k.length + v.length ≤ Bbolt.bboltEntryMax⌝` in
`txWr`'s put row (named constants), and the matching premise in `UnsafePutUser`/`UnsafePutRole`
(over `userName c`/`roleName c` and `encSize c`), `MustUnsafeSaveConfStateToBackend` (a bound on the
configuration), `MustUnsafePutLease`/the CI writes (8-byte keys and small values: provable, state it
in the sketch).

### F5. `Semver.parse_render` is false (semver `Api.lean`, law `parse_render.spec`)

`NewVersion` refuses a string longer than `MaxVersionLen = 256` (`version.go:60,106`), and `String()`
can be longer than the string parsed: the lenient parser accepts `1-<254 a's>` (256 bytes), whose
`String()` is `1.0.0-<254 a's>` (260 bytes), which does not parse. Checked: semver v3.5.0 prints
`256 260 version string is too long (max 256 bytes)`. The snippet `ReqRoundTrip`
(`leaves.go:109-115`) panics on that input under its stated assumption ("s parses"). The law is a
trust-boundary statement over an opaque `parse`, so it is an assumed universal that is false
somewhere.
**Fix**: `parse s = some sv → (render sv).length ≤ 256 → parse (render sv) = some sv` (a named
`maxVersionLen`); the stored cluster version's writers (`decideClusterVersion`'s `major.minor.0`,
`parse_plain`) meet it; `ClusterVersionFromBackend`'s premise and `ReqRoundTrip`'s `Assumes:` take it.

### F6. `preLtb` is opaque with no law; two snippets need its irreflexivity (`leaves.go:88,112`)

`ReqParseCompare` panics if `lv.LessThan(lv)` for `lv = 3.8.0-alpha.0`; `SemVer.ltb a a` reduces to
`preLtb "alpha.0" "alpha.0"`, which nothing determines. `ReqRoundTrip`'s `v.LessThan(w)` with
`w = v` likewise whenever `v.pre ≠ []`. In the code `comparePrePart` returns `0` on equal parts
(`version.go:680-684`), so `comparePrerelease(x, x) = 0`.
**Fix**: a law `preLtb_irrefl : ∀ s, preLtb s s = false` (true of `comparePrerelease`), or more of
its order if a caller needs it (asymmetry is also true).

### F7. Probing's `AddHTTP` triple is false at inputs it admits (`probing/Api.lean`, `proberOk`)

`proberOk` promises `AddHTTP(id, interval, urls)` returns for every `interval` and `urls`, with no
ownership of `urls`. In the code (`prober.go:41-90`): `time.NewTicker(probingInterval)` panics at
`interval ≤ 0`, synchronously (`:51`); the goroutine indexes `endpoints[pinned]` (empty `urls`:
index out of range, and `% len(endpoints)`: division by zero) and `panic(err)`s when
`http.NewRequest` cannot parse a URL (`:59-62`), which kills the process; and it reads the slice for
as long as the target lives, so the caller must not write it again. rafthttp meets all of this
(`proberInterval` is 4 s; `AddPeer` panics first on URLs `types.NewURLs` rejects,
`transport.go:305-310`, and `hus[i] = us[i] + "/raft/probing"` of a parsed URL parses).
**Fix**: `AddHTTP`'s row takes `⌜0 < sint.Z interval⌝ ∗ urls ↦*□ us ∗ ⌜us ≠ [] ∧ ∀ u ∈ us,
urlParses u⌝` (`urlParses` from 2f's vocabulary, or a named opaque `Prop` with the law rafthttp
needs). `ReqProberLifecycle` (`leaves.go:136`) then needs `Assumes:` of the same. Record it as a
nonissue (a library precondition etcd meets: `nonissues/probing-addhttp-preconditions.md`).

### F8. `alarmBackend.ForceCommit.spec` takes nothing of `be` (`alarmBackend__ForceCommit.lean`)

The pre is `ab ↦□ alarmBackend.mk lg be ∗ True`, for any `be`. `NewAlarmBackend.spec` admits
`be = nil` (a method call on a nil interface panics), and on a closed backend `ForceCommit` reaches
`lg.Fatal` (`backend.go:377-378` → `batchTx.Commit` → `begin` → `unsafeBegin`, `:1101-1107`, on a
closed database). The old store's backend is closed by `applySnapshot` while the old
`alarmBackend` still points to it. 4a's lock calls take `isBackend γ b p Pk ∗ beOpen γ q`
(`batchTxBuffered__LockOutsideApply.lean`): an assumed spec with `True` cannot rest on them.
**Fix**: take `alarmBkt be al` (kept; its realization holds the open backend's share), or
`callOk be "ForceCommit" P Q ∗ P` as `authBackend.ForceCommit.spec` does.

### F9. `MustUnsafePutLease` and `leaseMsg_of_struct` claim the message is unchanged by a `Marshal` that writes it (`MustUnsafePutLease.lean`; `Api.lean:488-492`)

`MustUnsafePutLease` is assumed with `lpb ↦{dq} v` in and the same `lpb ↦{dq} v` out; it calls
`proto.Marshal(lpb)`, which stores the size into `lpb`'s `sizeCache` field (`atomic.StoreInt32`:
2a's own header, `SpecPlan/Spec/google_golang_org/protobuf/proto/Api.lean`, `msgAt`). So the post is false of
the heap (the field changes), and at `dq ≠ 1` the write has no permission at all. The law
`leaseMsg_of_struct` (`p ↦{dq} v ⊢ ∃ c, msgAt p dq c ∗ … ∗ (msgAt p dq c -∗ p ↦{dq} v)`) has the
same defect: after a `Marshal` through the `msgAt`, the wand must give back the old `sizeCache`.
The one caller passes a fresh local (`lease.go:57-60`).
**Fix**: state `MustUnsafePutLease` over `Proto.msgAt Lease.ty lpb dq c ∗ ⌜leaseModel c = r⌝`
(kept), like the other message writers, and restrict `leaseMsg_of_struct` to `DFrac.own 1` with a
one-way conversion (`p ↦ v ⊢ ∃ c, msgAt p (own 1) c ∗ ⌜leaseModel c = (…)⌝`; `leaseMsg_to_struct`
already gives the way back).

### F10. A `Scope` cannot give mvcc `Meta`'s existence without all of `Meta` (schema `Api.lean:179-198`; `UnsafeCreateMetaBucket.lean`)

`UnsafeCreateMetaBucket` (and `txWr`'s create row) needs `S.whole .metaB`, i.e. the whole `Meta`
bucket, every key included. The plan (`req/…_storage_backend.md`, "from 4b", item 1) gives mvcc only
`scheduledCompactRev`, `finishedCompactRev` and `Meta`'s existence; the consistent index (2d) and
the conf state (2e) own other keys of it, in their own invariants. mvcc's `NewStore`
(`kvstore.go:121-123`) cannot meet the premise with its part, so 3e's use is not served. Creation
changes no key (`View.create`), and buckets are never deleted on these paths, so existence is a
monotone fact every part holder can share.
**Fix**: separate existence from keys: a `Scope` component for the right to create (`S.made b`), and
existence as a persistent fact (`bucketMade be b`, or a `View` whose `b` is `some` in every part once
created) that `txRd`/`txWr`'s `V b = some m` premises can come from. Then `UnsafeCreateMetaBucket`
takes `S.made .metaB`.

### F11. `NewLimitedBufferReader` and the `ReaderAndCloser` laws need an intro law of 2f's opaque `readerAt` that does not exist (`ioutil/NewLimitedBufferReader.lean`, `ioutil/Api.lean`)

`Http.readerAt` is opaque (`SpecPlan/Spec/net/http/Api.lean:231`); its only laws give `Read`/`Close` triples
(`readerAt_read`, `readerAt_close`), and the intro laws are for 2f's own readers (`NewBuffer_reader`,
`MultiReader_reader`). The sketch "hence the returned reader has `r`'s contract" for a translated
`*limitedBufferReader`, and the laws `ReaderAndCloser_reader`/`_closer` for `ReaderAndCloser`'s promoted
methods, have no source: nothing outside 2f can produce a `readerAt`.
**Fix**: ask 2f for one intro law (`readerAt_wrap`: a value whose `Read(p)` is, from `readerAt rd Pre
Φ r`, a `Read` of `rd` on a prefix of `p` with the same result, is a `readerAt` with the same
knowledge; and `readerCloser` the same), written in `req/net_http.md`, and cite it in both sketches.

## Second tier

1. **`api/v3/version.LessThan` has no spec** (3c's request, `req/…_storage_schema.md`, "from 3c",
   item 2): it is names only (`Code/go_etcd_io/etcd/api/v3/version.toml`), wraps
   `ver1.LessThan(&ver2)` over semver values (`api/version/version.go:84-86`), and `version.V3_6` is a
   global `semver.New(...)` value. 3c's `greaterOrEqual.spec` needs both. 4b owns semver: give the
   assumed `version.LessThan.spec` (over two `Version` values, `SemVer.ltb (verOf x) (verOf y)`) and
   an init law for `V3_6`, or route it to W0 (owner of `api/v3`) explicitly. The report does not
   mention the request.
2. **`OtelTrace.spanOk` omits `SpanContext` and `IsRecording`**, which the no-op tracer's `Start`
   calls on the context's span (`noop/noop.go:54-73`); the header says `ctxSpanOk` is "what makes
   that safe", but its stated realization is "nil or a value with `spanOk`". Add the two methods to
   `spanOk` (or to `ctxSpanOk`'s realization).
3. **The names-only alarm/membership specs rest on the lock calls' verification check** (`backend/
   verify.go`: with `ETCD_VERIFY` lock checks on, `LockOutsideApply` panics inside `applyEntries`,
   `LockInsideApply` with a hook outside it). Etcd's call sites are right; say in each docstring
   that the assumption is 4a's `envOk` (or what 4a chooses), carried by `alarmBkt`/`memberBkts`/
   `applyHook`'s realization.
4. **`bucketVars_init`/`keyNames_init` cover untranslated initializers**: of the buckets only `Key`,
   `Meta`, `Lease`, `Auth*` are translated (`Code/…/schema.toml:14-29`); `Alarm`, `Cluster`,
   `Members*`, `ScheduledCompactKeyName`, `FinishedCompactKeyName`, `MetaConfStateName` are names
   only, so these rows of the laws rest on `etc/gen-init.py`'s trust axioms for untranslated
   initializers. Say so in the laws' docstrings (or restrict the laws to the translated variables
   plus an explicitly assumed row).
5. **A part's view under a lock another component took**: `lessor.Revoke` calls
   `UnsafeDeleteLease(le.b.BatchTx(), …)` while mvcc's write transaction holds the batch lock
   (`lessor.go:340-360`); the lessor's `R` must be usable there. The schema's statement is fine (`R`
   is generic), but the 4a request (item 2, "Batch transaction, lock held") should say that the
   lock's holder and the part's owner differ here, so 4a's lock-held token must be lendable to other
   parts' owners. No snippet covers it (below).
6. **`UnsafeUpdateConsistentIndex.spec` takes `txRd` also when `verifyOff`**: harmless (the callers
   have it), but it is a premise the code needs only with `ETCD_VERIFY` on; the internal
   `unsafeUpdateConsistentIndex.spec` already gates it.
7. **`Rate/Api.lean`'s header** says "true of its `examples/specreq/pkgleaves/leaves.go`": a slip for
   `rate.go`.
8. **`ReqMarshalRoundTrip`'s `Assumes: nothing`**: `MustMarshalMessage` needs `c.fits`, which for a
   raft message holds only when its byte slices are distinct allocations (2a's header); assume `m` is
   a message R1's predicates hold of.

## Completeness

Users scanned: every `schema.*` call outside the package in the pinned server (`grep`: 20 functions;
the uncovered ones are `Validate`, `DetectSchemaVersion`, `UnsafeMigrate`, `ReadStorageVersion`
(migration, left out by the report), `MustUnsafeGetLease`, `UnsafeConfStateFromBackend` (tests and
an untranslated bootstrap path)); every `traceutil.*` call (server request path, `txn`, `apply`,
mvcc, read loop); every `traceutil.Field` value (all predeclared basic types: `fieldsFmt` holds at
every site); otel's spans (`v3_server.go`, `v3rpc/watch.go:333`, `mvcc/watcher.go:140`); pbutil
(apply, server, storage/util, WAL, rafthttp); probing, rate, semver, ioutil, httputil in rafthttp,
membership, apply, version.

Every old spec of these packages is kept (`specs-ref`'s schema, traceutil, pbutil, ioutil,
httputil, rate files all have a successor).

Slots of the callers, realizable over the bundles (after F1-F4, F10):

* **2d `txStoredCI tx c`**: `∃ R V m, txWr tx ciScope R ∗ txRd tx ciScope R ∗ R V ∗ ⌜V .metaB = some m
  ∧ ciWf m ∧ (ciOf m).1 = c⌝` over 4a's CI part: works with `UnsafeUpdateConsistentIndex.spec` (the
  `i = 0` case needs no `Meta`). `beStoredCI` as a persistent fact is unsound, as the report says; the
  read is `ReadConsistentIndex.spec` over `rdSect`.
* **3c `beLeases be B`**: the lease part's batch view with `leaseBktIs`; all four calls served
  (put, delete, create, read-all, the latter "each once" after F3). The `Revoke` case needs item 5.
* **3d `authBackendAt be a`**: the three auth parts with the records' encodings; every method has a
  spec (the batch side is new). `UnsafeGetAllRoles` on a read transaction is unusable, as it should
  be (nonissue). `recordsFit` must be passed down (F4).
* **2e `beAlarms`/`beMembers`**: `alarmBkt`/`memberBkts` serve `NewAlarmStore`, `Activate`,
  `Deactivate`, `Recover` and `RaftCluster`'s savers and readers.
* **3e**: `bucketAt` in place of constant `bucketVal` is right (the name slices are allocated at
  init); `UnsafeCreateMetaBucket` is blocked by F10.
* **2c/3b/3a/3e traces**: `traceOwn`/`traceOpt` serve every use; `EnsureTrace`/`Get` need
  `ctxTraceIs` of each context, given for `Background`, `TODO`, children, `WithValue`s, and by 2a for
  grpc's per-call context (requested).

Patterns without a snippet (each with a call site):

* listing users through a read transaction (`UserList`, `auth/store.go:602`, `GetAllUsers`): the
  pattern F3 is about;
* deleting users and roles (`UnsafeDeleteUser`/`UnsafeDeleteRole`, `UserDelete`, `RoleDelete`);
* the consistent index read from the shared read transaction **without** `RLock` under the batch
  lock (`cindex.go:107`, `UnsafeConsistentIndex`);
* a part written under a lock another component took (`lessor.go:359`, item 5);
* the cluster version and downgrade info saved and read back (`cluster.go:586,610`,
  `MustSaveClusterVersionToBackend`, `ClusterVersionFromBackend`, `DowngradeInfoFromBackend`);
* a span ended from another goroutine (`mvcc/watcher.go:140-144`: `span.End()` in a cancel
  closure) and `AddEvent` (`v3_server.go:1112-1125`);
* `Reserve().Delay()` (client-go's limiter; the report lists it as a user).

## Provability of the snippets (sketch)

* `schema.go`: `ReqCreateBuckets`, `ReqSaveThenRead` (`ciOf (ciPut m i t) = (i, t)` for `i, t ≠ 0` is a
  pure fact of `beU64`/`u64Of`; the read after `Unlock` rests on 4a's realization of `Q`),
  `ReqLeaseRecover`, `ReqAuthWriteRead` (with 3h's `Name`-field law for `userName`),
  `ReqAlarmPutGet`, `ReqMembersSaveRead`: provable from the specs as stated, but each rests on the
  bundles F1-F4 make unprovable for 4a; they stay provable after the fixes (the snippets decode within
  the section, pass `nil` ends, do not depend on order, and write small records).
* `trace.go`: all five provable (`ReqRequestTrace`: `Tracer.Start` then `ctxTraceIs_value` for the
  otel key, `EnsureTrace`'s reuse case gives `tr2 = tr ∧ ctx2 = ctx`, `StepWithFunction` lends the
  trace to the closure, `ctxSpanOk_value` for `SpanFromContext`; the others as their headers say).
* `leaves.go`: `ReqParseCompare` and `ReqRoundTrip` not provable (F6; `ReqRoundTrip` also false, F5);
  `ReqProberLifecycle` provable only because `proberOk` is too strong (F7); the rest provable
  (`ReqLimitedRead`/`ReqReaderAndCloser` after F11).

## What is good

* The schema over the transaction contracts (the caller's `R`, its `S`) instead of the backend's
  predicates is the right shape (PRINCIPLES, "An API is stated over the abstractions it builds on"),
  and it makes the callers' slots realizations rather than new schema predicates. The encodings
  (`ciOf`, `ciPut`, `authEnabledOf`, `authRevOf`, `leaseBktIs`, `rangeOf`) match the code exactly,
  absent keys included (`(0, 0)` without an index; the term `0` without a term; `authEnabled` true
  only for `[1]`; `Uint64`'s panic as `u64Ok`), and the CI update's `i = 0` early return no longer
  needs `Meta`.
* `bucketAt` in place of constant bucket values (the name slices are allocated at init) is right and
  catches a real defect in 3e's contract.
* Traces: the persistent `traceAt` is indeed false (`Step` appends to `t.steps` with no lock), and
  the split into exclusive `traceOwn` plus the persistent `traceEmpty` (the only field read across
  owners, written only at creation) is exactly what `EnsureTrace`'s reuse needs. `fieldsFmt` matches
  every `Field` value in the server. `LogIfLong` consuming the trace is justified by `logInfo`'s
  aliasing `append`s. The `traceutil.Init` scope restriction is marked and put to the user (the
  alternative, an owned `Tracer` points-to frozen after `embed`'s `Init`, is heavier; the
  restriction is acceptable as an open question).
* `Tracer.Start` is true of otel v1.47.0's no-op tracer, both branches (`noop/noop.go:54-73`); `rate`
  is true of v0.16.0 (`Delay ≥ 0` also for a not-ok reservation, `InfDuration`); `pbutil` over 2a's
  `Proto` is sound; `GracefulClose` taking the reader owned and flagging the snapshot sender's
  concurrent drain is a good catch.
* No boundary spec hands out a counted resource: the read-section specs take the caller's
  `threadTok` and give it back after `RUnlock`.

## Ranking (most in need of revision first)

1. `storage/schema/Api.lean`'s bundles and scopes (F1, F2, F3, F4, F10) and the specs over them
   (`GetAllUsers`, `unsafeGetAllUsers`, `MustUnsafeGetAllLeases`, `UnsafeCreateMetaBucket`,
   `UnsafePutUser/Role`).
2. `probing` (F7).
3. `semver` (F5, F6; second-tier 1).
4. The schema's names-only specs: `alarmBackend.ForceCommit` (F8), `MustUnsafePutLease` and
   `leaseMsg_of_struct` (F9).
5. `ioutil` (F11).
6. `otel/trace` (second-tier 2).
7. `traceutil` (good; nothing first-tier).
8. `pbutil`, `httputil`, `rate`, `otel/attribute` (good).

## Verdict

Not done: eleven first-tier findings. The design (transaction bundles, exclusive traces, the
boundaries' vocabularies) is sound in shape; the bundles promise more than etcd's backend gives (bytes
for good, sorted read-transaction scans, nil-or-empty ends, unbounded puts, existence only with the
whole bucket), and three trust-boundary statements are false at inputs they admit (`parse_render`,
`AddHTTP`, `alarmBackend.ForceCommit`). All the fixes are local; a second round is needed.
