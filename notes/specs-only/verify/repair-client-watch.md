# Repair after the verification round: group `client-watch` (2026-11-09)

Files: `SpecPlan/Spec/go_etcd_io/etcd/client/v3/{ApiWatch, WatchInternal, streamKeyFromCtx, watcher__Watch,
watcher__RequestProgress, watcher__Close, watcher__closeStream, watcher__newWatcherGRPCStream,
NewWatcher, NewWatchFromWatchClient, watchGRPCStream__run}.lean`, `examples/specreq/clientv3watch/
{consume,ending}.go`, and a new issue `issues/etcd-client-resolver-build-race.md` (with its test).

## Findings

### A2-provability

- **W1 (fragments: the first fragment's header and compaction revision). Fixed.** `WireSt.frag` is
  now `Option (WireWatchRespM × List EventM)`: the first fragment's message and the events so far.
  `wireStep` requires every later fragment and the completing response to agree with the first on
  the id, the header, the compaction revision and the cancel reason (and to be neither `Created`
  nor `Canceled`), so the completing step's `m.toResp evs` equals the first's, which is what `run`
  dispatches (`watch.go:596-603`). 2b proves the agreement from `sendFragments`, which copies these
  fields into every fragment (`v3rpc/watch.go:634-643`). `watchGRPCStream__run.lean`'s sketch says
  how `cur` is tied to `WireSt.frag`. (I chose agreement over stating the step on the first's
  `toResp`: it keeps the step on the message received, and the server's facts are per message.)
- **W2 (a joined stream's principal). Fixed.** New in `ApiWatch.lean`: `ctxStreamKey ctx k`
  (persistent; `k` is `streamKeyFromCtx(ctx)`), and the law `ctxStreamKey_prin.spec`: `ctxPrin dflt
  ctx p ∗ ctxPrin dflt ctx' p' ∗ ctxStreamKey ctx k ∗ ctxStreamKey ctx' k ⊢ ⌜p = p'⌝`, with its
  soundness argument (the metadata `ctxPrin`'s introductions admit print injectively; the old
  tree's `streamKeyOf_none`/`_single`). `streamKeyFromCtx.spec` returns `ctxStreamKey ctx k` and
  takes `ctxPrin dflt ctx p` (every caller has it; its realization carries the metadata,
  `Grpc.outMD`). `watcherHandle`'s intended realization keeps, per map key, the opening context's
  `ctxStreamKey` and `ctxPrin`; `watcher.Watch`'s and `RequestProgress`'s sketches use the law.
  Differently from the reviewer: no functionality law for `ctxStreamKey` (grpc's
  `FromOutgoingContext.spec` does not say whether an empty map was attached, so the realization is
  a disjunction; nothing needs functionality for safety).
- **W3 (no readiness on the watch chain). Fixed on my side; needs 3h's stub change (request
  below).** `watcherHandle w c γ who` records the client whose readiness the stub needs;
  `watcherHandle_watcherAt` takes `clientReady c`. `watcher.Watch.spec`,
  `watcher.RequestProgress.spec` and `watcher.newWatcherGRPCStream.spec` take `clientReady c` (they
  may open a stream); `watcher.Close.spec` and `closeStream.spec` do not (no stream opened).
  `NewWatchFromWatchClient.spec` takes the stub gated, `□ (clientReady rc -∗ remoteWatchAt wc γ
  who)`, for a ghost client `rc`, and returns `watcherHandle w rc γ who`: `NewWatcher` passes
  `rc = c`; the in-process client passes `rc = null` (`clientReady_null`), since its `c` gets
  `clientReady` from `clientBare_assemble` only after the watcher is built (a handle recording `c`
  there would be circular). `NewWatcher.spec` returns `watcherHandle w c γ who`. `wgsAt`'s
  realization keeps `remoteWatchAt` (a stream is made only on a ready client) and the watcher's
  handle (for the teardown's `closeStream`).
- **W4 (`Created` after an error). Fixed.** `watchStep`'s ended case has `m.created = false`.
  `ReqWatchCreatedFirst` closes now (its Specs line says so).
- **S1 (the tie and progress between resumes). Fixed (stated).** `WatchInternal.lean`'s tie now
  says a substream with unknown position carries what progress facts it learned while its
  registration's position was known, and names the two pure model lemmas the proof needs.
- **S2 (events' keys in range only under `exactFrom`). Fixed, cross-group (requests below).**
  `watchStep`'s event case has a new unconditional clause: each delivered event is an event of the
  history (`σ.kv.eventsAt r`) that the watch keeps (key in range, filters), whatever the compaction
  did. This is also A3-provability's "stronger fix" (keys in range and each event's key-value the
  record its revision wrote). `ReqWatchRewrite` no longer assumes the compaction condition; new
  snippet `ReqWatchSharedStream` (two require-leader contexts sharing a stream, slicing keys as the
  namespace wrapper does, no compaction assumption).
- **S4 (resolver race). Real: filed as `issues/etcd-client-resolver-build-race.md`** (test in
  `issues/etcd-client-resolver-build-race/`, fails under `-race` at the pinned fork, default
  configuration; upstream's `resolver.go` is identical). grpc builds the resolver on its
  serializer goroutine when the channel exits idle (the client's first RPC, or after an idle
  period); `Build` writes `serviceConfig` and reads `endpoints` while `SetEndpoints` (a caller's or
  auto-sync's) writes `endpoints` and copies the resolver, under `epMu` only. `blocks-proof: no`
  (no top-level workload changes endpoints). The spec side is client-core's (request below).
- W2/W3 in `Client.Watch`/`Client.RequestProgress`: unchanged files; they inherit the fixes
  through `isClient_fields`' `watcherAt`.
- L1, L2, S3, S5: lease/client, not mine (client-core).

### A2-completeness

1b passed with recorded open decisions; S5 (Kubernetes' watch context) and S6 (grpcproxy floor)
are recorded margins: no change. S1 (no server-side `ctxPrin` introduction) is W0's: not mine.

### A3 (client-users)

- **F5 (no progress notification without `WithProgressNotify`)**: about the cache's own
  notifications to its local watchers (`cacheWatchAt_recv`, client-users' file), not the client
  watch: no change here. At the client level such a promise is not expressible locally: a member
  answers any `RequestProgress` on a shared stream (any context with the same metadata) with a
  progress to every watch of the stream, `IsProgressNotify` alike.
- **A3-provability, "the stronger fix"** (also client-users' request via the coordinator): done
  (S2 above). The clause, outside the `exactFrom` gate: for each delivered event `e` there are a
  revision `r` and a history event `ev ∈ σ.kv.eventsAt r` with `e.kv.modRevision = W64 r`,
  `WEv.ofEvent r ev` equal to `e` in `del` and `kv` (a put's key-value is exactly the record
  revision `r` wrote; a delete's the key and revision), and `w.keeps` it (key in the range, not
  filtered). True at every compaction state: mvcc's events come either from the committing txn's
  own changes (`notify`) or from backend records read at real revisions `≥ minRev` (`syncWatchers`,
  a compaction past `minRev` gives a compaction error instead), filtered by the watcher's range
  (`kvsToEvents`, `w.contains`); compaction deletes records but never alters one. Recipes'
  `Dequeue` specs can drop the gate on the read path. (Its chain needs mvcc's `wStep` to say the
  same: the request to mvcc below.)

### A1 (client-kv)

- The completeness note on `valCtx_ctxOk` forwarding `Value` (A1 `Context.Value` finding): the law
  states `Context.ctxOk` of the `valCtx`, whose meaning is W0's bundle; when W0 adds `Value` to
  `ctxOk`'s bundle, `valCtx`'s `Value` is the embedded context's (Go's promotion), so the law's
  statement is unchanged. No change.

### Sentinel errors

None in the watch files: errors are classified by kind (`closeErrOk`, `callErr`); no
`errors.New` global is equated with a constant.

## Requests to grpc-v3rpc

1. **`SpecPlan/Spec/go_etcd_io/etcd/api/v3/etcdserverpb/NewWatchClient.lean`** (W3): the post
   `ClientV3.remoteWatchAt v γ who` is unprovable: the stub opens streams through the connection's
   stream interceptor, whose token refresh reads `c.Auth`, unset when `newClient` calls
   `NewWatcher` (`client.go:460-461`). Give the contract gated on the readiness of the client whose
   connection it is: e.g. take `ClientV3.clientConnOk c γ who` and the `conn` read from `c.conn`
   (or a W0 law naming `connOk conn`'s client), post `□ (ClientV3.clientReady c -∗
   ClientV3.remoteWatchAt v γ who)`. `NewWatcher.spec`'s sketch assumes that form. The sibling
   stubs `NewKVClient`, `NewLeaseClient`, `NewAuthClient`, ... have the same unconditional post and
   the same problem (`RetryKVClient` etc. call them before `c.Auth` is set); coordinate with
   client-core.
2. **2b, `v3rpc/ApiWatch.lean` and the watch server's sketches** (W1): `wireStep` now requires every
   fragment after the first, and the completing response, to carry the first fragment's id, header,
   compaction revision and cancel reason (`WireSt.frag` keeps the first's message). True of
   `sendFragments`; the sketch should cite it.
3. **2b** (S2): `watchStep`'s event case now says unconditionally that each event is an event of
   the history the watch keeps (key in range, filters). 2b gets it from mvcc (request to mvcc).

## Requests to mvcc

1. **`SpecPlan/Spec/go_etcd_io/etcd/server/v3/storage/mvcc/ApiWatch.lean`, `wStep`** (S2): add, outside the
   `exactFrom` guard, that each event of `r.evs` is an event of `h` at its revision whose key the
   watcher's range contains (`∀ e ∈ r.evs, ∃ rv ev, ev ∈ h.eventsAt rv ∧ e = evOf rv ev ∧ W`'s range
   contains its key`). True: `syncWatchers` reads backend records of real revisions and
   `kvsToEvents` filters by `w.contains`; `notify` passes the txn's own changes. 2b's filters
   (`filterNoPut`, `filterNoDelete`) give the client's filter part.

## Requests to client-core

1. **`newClient.lean`'s sketch** (W3): `NewWatcher` now returns `watcherHandle w c γ who`; after
   `c.Auth` is set and `clientReady c` minted, `watcherHandle_watcherAt` gives `watcherAt`.
2. **`v3client.New`/`clientBare_assemble` users** (W3): `NewWatchFromWatchClient(adapter, c)` is
   applied at `rc = null` with the adapter's `remoteWatchAt` (`□ (clientReady null -∗ …)` from the
   unconditional one); then `watcherHandle_watcherAt` with `clientReady_null`.
3. **`Api.lean`, `ctxPrin`** (W2): its introductions must keep `ctxStreamKey_prin` (ApiWatch) true:
   any new introduction of `ctxPrin` for a context with other outgoing metadata must print
   injectively (fixed lower-case keys, single values free of space, `:`, `[`, `]`). The
   realization of `ctxPrin` should carry the context's outgoing metadata (`Grpc.outMD`), which
   `streamKeyFromCtx`'s proof reads. `fmt`'s boundary needs `Sprintf("%+v", map[string][]string)`
   as a function of the map's model.
4. **`Client__SetEndpoints.lean` / `Client__Sync.lean` / the resolver boundary** (S4,
   `issues/etcd-client-resolver-build-race.md`): `SetEndpoints` races grpc's `Build` of the
   resolver when the channel exits idle (any RPC). With the whole `epsTok` and a concurrent RPC
   the spec as stated admits the race; its pre (or the grpc boundary's account of `Build`) must
   exclude a concurrent channel wake-up, e.g. by taking a token every RPC on the connection needs a
   fraction of, or state the resolver's fields as racy (out of the model) and record the issue.

## New decisions

- **Readiness is recorded per handle with a ghost client (`rc`)**, not the Go client argument: the
  in-process client's `NewWatchFromWatchClient(adapter, c)` would otherwise need `clientReady c`
  before `clientBare_assemble` mints it. Client-core's `NewLeaseFromLeaseClient` fix (L1) faces
  the same circularity and could use the same device.
- **Compaction affects only exactness, now stated in `watchStep`**: event responses are always
  made of history events the watch keeps, whatever the compaction did (A17 said so in words). This
  needs mvcc's `wStep` to say the same (request above); until then 2b's chain does not close for
  the new clause.
- **`ctxStreamKey_prin` is a law about W0's `ctxPrin`, stated in 1b's `ApiWatch.lean`** (as the
  coordinator asked): whoever realizes `ctxPrin` proves it; it constrains future `ctxPrin`
  introductions (no metadata that prints ambiguously).

## Build

`etc/specs-build.sh --dir SpecPlan/Spec/go_etcd_io/etcd/client/v3`: OK (347 modules), once client-core's
in-progress `Api.lean` built again. No module outside the directory names `watcherHandle`,
`ctxStreamKey` or `WireSt.frag`'s old type. `go vet ./specreq/clientv3watch/...`: clean.
`etc/issues-status.py --index`/`--check`: clean.
