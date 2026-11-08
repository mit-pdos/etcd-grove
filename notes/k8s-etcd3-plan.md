# Plan: the Kubernetes etcd3 storage backend (`k8s.io/apiserver/pkg/storage/etcd3`)

Status: started (2026-10-22, branch `k8s-etcd3`: `lean` with `k8s-etcd3-goose` merged). Decisions:
D30 in `notes/decisions.md` (D30a-l; D30h-j and D30l proposed). The translation survey is branch
`k8s-etcd3-goose` (`notes/k8s-etcd3-goose.md`): the store translates and builds with the pinned
translator except six functions left names-only; its gaps G1-G3 are under "What blocks where", and
the Perennial changes they call for in `notes/perennial-changes.md`. Done so far (`notes/STATUS.md`
has the details): phase 1's contract, phase 2's model, phase 3's client (`Get`, `OptimisticPut`,
`OptimisticDelete`; one `sorry`, `kvIs_ne_null`: request 3 below), and phase 4's `store.Get`,
`store.Create`, `store.Delete` and `store.GuaranteedUpdate` (D30l: the read-or-write update;
`reflect` through local axioms, the user's choice), linked, with restrictions (`notes/STATUS.md`).

(2026-10-23) Phase 6's closed theorem `k8setcd3_safe` done and merged into `lean`, on restricted
traffic. (2026-10-31) **Next: phase 7**, the etcd3 subtest of `TestCorrectness` itself (below);
stage 7a done (`store.GetList` translated, branch `worktree-k8s-etcd3-correctness`).

## Goal

Rule out, by proof, the class of bugs Kubernetes' storage correctness test finds in the etcd3
store (`test/integration/apiserver/storage/`, `TestCorrectness`; its README lists the bugs). The
store's own: #43152, #48394, #54780, #77619, #94002; shared with the watch cache: #35415, #89828
(deleted object), #113380, #135452, #138724, #142591. The watcher (`watcher.go`) and the watch
cache (`cacher`) come later.

Two results:

1. **Generic method specs.** A logically atomic triple for each `storage.Interface` method of
   `*store` (`Create`, `Delete`, `GuaranteedUpdate`, `Get`, `GetList`, `Stats`,
   `GetCurrentResourceVersion`, ...), stated with a Lean copy of `correctness.Model`
   (`staging/src/k8s.io/apiserver/pkg/storage/testing/correctness/model.go`), for **any** codec,
   versioner and transformer meeting a contract (a premise, not an axiom).
2. **A closed driver theorem** (`k8setcd3_porcupine_safe`, as `kv_porcupine_safe`): a Go program
   in `examples/` runs `TestCorrectness`'s traffic and checks against the store over in-process
   etcd members, with a simple concrete codec, and never panics. Its trusted spec is then the
   Kubernetes maintainers' `Model` and porcupine (verified here), not our Lean spec.

## How the store works (what the spec is about)

- An object (`runtime.Object`; in the test `*api.Pod`) lives at one etcd key
  (`/registry/pods/<ns>/<name>`); the value is the object's encoding (`runtime.Codec`) passed
  through a transformer (`value.Transformer`, encryption at rest; identity in the test).
- The resource version is not stored: `PrepareObjectForStorage` clears it before encoding, and
  every read sets it to the etcd `ModRevision` (`decoder.Decode` -> `versioner.UpdateObject`).
  Preconditions and optimistic updates are `ModRevision` compares in etcd transactions
  (`client/v3/kubernetes`: `OptimisticPut`, `OptimisticDelete`).
- `GuaranteedUpdate` and `Delete` may start from a caller's possibly stale
  `cachedExistingObject`, check preconditions, run `tryUpdate`/`validateDeletion`, refresh on an
  error (`refreshOnError`), re-read on a no-op from a non-current state, and retry on a
  `ModRevision` mismatch. `Model.update` ignores the cached object: the spec says the outcome is
  the Model's at one linearization point whatever the suggestion was, exactly the class of
  #35415, #43152, #48394, #54780, #77619, #82303, #89828, #113380, #138724.

## The codec contract (and why the driver's codec is non-canonical; D30g)

The specs quantify over a codec, versioner and transformer with a contract. It must be weak
enough to hold of the real ones:

- decoding fails or gives some object; decoding what the store encoded gives that object back
  (up to the resource version, which `UpdateObject` sets);
- **encoding is not canonical**: stored bytes `b` may differ from `encode(decode(b))`, and the
  transformer may report a stored value `stale`. #48394 (`GuaranteedUpdate` skipping the write
  when the stored data is not canonical) lives exactly there, and `GuaranteedUpdate`'s no-op
  check compares bytes (`bytes.Equal(data, origState.data)`).

**`correctness.Model` is wrong on that path (2026-10-22, D30g).** On a no-op update of
non-canonical or stale data the store rewrites the object at a new resource version, as its
own unit test requires, while the Model skips the write and rejects the response
(`nonissues/k8s-correctness-model-noop-rewrite.md`, reproduced). Decided (D30g):
- The Lean model's items carry a bit `canon` (the stored value is the codec's current encoding
  and not stale), and `update` writes unless the object is unchanged and `canon` holds. This is
  the store's rule, and the generic specs are stated with it. On states whose items are all
  canonical it is `correctness.Model`.
- **The driver's codec stays non-canonical** (D30b), for example a decoder that accepts several
  encodings of one object (a field order, optional padding or a version tag). The driver seeds
  some keys in a non-canonical encoding before the traffic starts, as an older API server or a
  different serializer would have left them, and its transformer sometimes reports `stale` (a
  function of the stored value). It checks against a **fixed `correctness.Model`**: a patched
  copy of the package in `examples/k8s/etcd3/`, whose items carry their stored form, so that
  `update` compares as the store does. That copy is trusted until upstream fixes the Model. The
  contract's proof for the driver's codec is a real proof (no axiom).

## The driver and failed writes

**Superseded (2026-11-06).** This describes the first design, which stopped on a failed write. The driver as built (7b) checks over configurations with pending failed writes (`Model`, as linkvtxn's), and `k8s_etcd3_safe` covers those runs. See Phase 6/7 and the cluster3 Scope below.

`correctness.Model.Step` panics on any write error, and a faithful client spec lets any RPC
fail. First version: **a failed write stops the run without checking.** Each client stops at
its first failed write and sets a flag; after all clients finish, `Main` returns without
running porcupine if the flag is set. Failed reads are dropped from the history (a read has no
effect, so dropping it keeps a linearizable history linearizable).

Not "check the history up to the failure": a write that errored may still have taken effect,
and a concurrent read may have seen it, so the checker could reject a correct store and the
theorem would be false.

What this costs: the driver theorem says nothing about runs with a failed write (bugs in
recovery after one); the method specs still cover them (a failed write fired at most once).
The driver's Go test should show that runs reach the check in practice.

Upgrade, later: linkvtxn's model already checks over configurations with pending failed writes
(`examples/etcd/txnlin/linkvtxn.go`, "The model", `TxnModel.lean`'s `mStep`): a failed write may
take effect at any later time or never. Wrapping `correctness.Model` the same way needs a
write's effect to be a function of its input; the test's `randomUpdate` fixes its random choices
when the update function is made, so it is.

## Phases

0. **Setup.** The translation survey (branch `k8s-etcd3-goose`): Goose configuration, the gaps
   and their workarounds. Pin `k8s.io/apiserver` (the mirror at kubernetes master `d9cafe4`) with
   etcd replaced by this repo's fork pin. Fixed configuration for the proofs and the driver:
   `EtcdRangeStream` off (lists use paginated `Range`s, not `GetStream`), no compactor
   (`CompactionInterval` 0, and `ListFromCacheSnapshot` off: either starts a compactor
   goroutine in `NewCompactor`, the second its watch loop, which reaches G1's
   `fromWatchResponse`), `ttl = 0` (no leases), `AllowUnsafeMalformedObjectDeletion` off.
1. **Object boundary.** The contract above for `runtime.Codec`, `storage.Versioner` and
   `value.Transformer`; the store's `reflect`/`conversion.EnforcePtr` uses (from the survey:
   trusted models or Perennial support). The store invariant: every value under the prefix
   decodes (written by a store with this codec, or seeded by the driver).
2. **Pure Lean model.** `correctness.Model`'s create, delete, update, get and list over items,
   resource version and compaction revision; an abstraction from etcd's `KVState` (the etcd
   specs' state) under the prefix; lemmas that each transaction the store sends moves the
   abstraction as the Model's operation. No new ghost state: the store's specs take atomic
   updates over the etcd specs' `etcdKV` through the abstraction.
3. **`client/v3/kubernetes`.** Specs of `Get`, `List`, `Count`, `OptimisticPut` and
   `OptimisticDelete`, proved from `kv.Get`/`kv.Txn`'s (a new package of the etcd project; tell
   the client proof's owner).
4. **Unary methods.** Helpers (`prepareKey`, `getStateFromObject`, `stateFromEtcdResponse`,
   `updateState`, `refreshOnError`, `txnError`, `validateMinimumResourceVersion`), then `Get`,
   `Create`, `Delete` (`conditionalDelete`, `deleteOnce`; preconditions and `validateDeletion`
   as callback specs), `GuaranteedUpdate` (`updateOnce`; `tryUpdate` with a repeatable spec: it
   may run on stale states, only the run at the linearization point counts). An RPC error needs
   only "some error, the write fired at most once": no dependence on error identity.
5. **`GetList`.** `pagedChunks` (an `iter.Seq2`), continue tokens, predicate filtering, limits,
   the resource-version modes (#94002). Needs error identity: `ErrFutureRev` ->
   `TooLargeResourceVersion`, `ErrCompacted` -> 410.
6. **Driver.** `examples/k8s/etcd3`: in-process etcd members (as linkv3p), the etcd3 store with
   the driver's codec, `RunUnaryTraffic`-style traffic (reused from the test, `math/rand` choices
   nondeterministic), porcupine with `correctness.Model`, `Replay.Validate`; failed writes as
   above. Then faults: partitions and client cuts from linkv3p's schedule.

## Phase 6: the driver, as carried out (2026-10-22)

`examples/k8s/etcd3/k8setcd3.go` (translated with project `k8s-apiserver`, package `.`): one
in-process member, a `kubernetes.New` client (one attempt per call), two keys seeded through the
client in an older encoding (non-canonical, D30g), the etcd3 store over the client with the
driver's `Obj`, codec, versioner, decoder and identity transformer, and `lintest.Run` of the
minimal unary traffic (Create, Delete, GuaranteedUpdate, consistent Get; rejecting callbacks,
no-op updates) against `Model`, a Go copy of `correctness.Model` (D30m) with the canonical bit and
linkvtxn's pending failed writes. Go tests: `Main` is linearizable; sequential traffic matches the
model and reaches every outcome (the non-canonical rewrite included); the model agrees with the
real `correctness.Model` on random traffic from canonical states and differs only on the
non-canonical rewrite.

The closed theorem (`k8setcd3_safe`, as `linkvtxn_safe`), in stages:

- **6a. The driver's model in Lean**: the Go model's functions (`lookup`, `setItem`, `delItem`,
  `mcreate`, `mdelete`, `mupdate`, `mget`, `mstep`, `step`, `closure`, `Model`'s `Step`) proved
  against Lean functions, as linkvtxn's (`TxnModel.lean`, its per-function proofs).
- **6b. The refinement**: the store's model (`Model.lean`'s `KSt`, through `absK`) and the
  driver's (`mstore`, objects with their resource version string, the canonical bit) answer the
  same: `create`/`delete`/`update`/`get` against `mcreate`/`mdelete`/`mupdate`/`mget`.
- **6c. The contract's instance**: the driver's `ObjSpec` (its objects are `(name, value)`;
  `objAt` the `*Obj` points-to) and `contractOk` for its codec, versioner, transformer and
  decoder. `runtime.Encode` and `runtime.SetZeroValue` are names-only (apimachinery's
  `runtime`): either their bodies translated (`Encode` writes into a `bytes.Buffer`;
  `SetZeroValue` uses `reflect`) or trust-boundary specs in terms of the codec's `Encode` and
  the object's zero value.
- **6d. The callbacks**: `validateOk` of `validateFor`, `tryUpdateOk` of `tryUpdateFor`
  (`updated`), matching the model's `validate` and `f`.
- **6e. `etcd3.New`**: its spec giving `isStore` (from `kubernetes.New`'s, over linkvtxn's
  client); `path.Join` (not translated by Perennial), the lease manager, the metrics tracker, and
  `feature.DefaultFeatureSupportChecker.CheckClient` (names-only; its goroutines poll each
  endpoint with `Status`, a read: a trust-boundary spec).
- **6f. The history**: the caller's updates (`k8sAuRW` with a token per call, `k8sAu1` for Create,
  the read update for Get) from an invariant over etcd's state and porcupine's linearization, as
  linkvtxn's `Inv`/`Apply`, keeping the store's states (`kvWf`: the seeds decode) and the history
  of key-values (`kvSeen`, D30j's local option: the invariant owns `γh`'s authority).
- **6g. `Apply`, `Check`, `Main`, adequacy.**

Done (2026-10-22): **6a** (`KModel.lean`: `kSpec st0`, linkv's `PendSpec` of `mstepL`, stated
on the Go records; `KSteps.lean`: the configurations, `Bounded` on items plus pending inputs;
every function of the Go model proved, `Model(st0)` against `k8setcd3S g0`), **6b**
(`ItemList.lean`, `Refine.lean`: `KRel`, `outOf`, `refine_create/delete/update/get`), **6c**
(`driver_contractOk`), **6d** (`validateD`, `tryUpdateD`, the exact sentinel error; the store's
`validateOk`/`tryUpdateOk` of them). The store's specs now carry the error shapes 6f needs
(`unkErr`: an outcome-unknown error is the client's, an `InternalError` or the codec's;
`KUserErr`: a callback's error keeps its identity). Still to do: 6e, 6f, 6g; 6f's `errOut`
needs a client error told apart from the sentinels ("From the etcd client proof", item 5), a
marked trust-boundary assumption until that lands.

Done (2026-10-23), toward 6f (D30n): the linearization points' store side. `Apply` prophesies the
output's `Err`, `ErrRV`, `RV`; `Client.Get` is prophetic (the etcd fork's `goose-lean-getproph`,
not yet on `goose-lean`), so a read update fires once, at the prophesied pair; `k8sAuRW` hands the
caller's token `W` at its linearization point (the write, or a read where the model's step is the
identity), the first read through `rwInv` (`FirstRead.lean`); `Delete`/`GuaranteedUpdate` and their
pieces proved on it. Also fixed: `step.lean` (the Go model's `step`), stale against `outEqual`'s
spec and `Output.Err` as a number, now builds.

Done (2026-10-23): **6f**. The driver's invariant (`Inv.lean`: `KOk`, the store's model refining
a configuration of porcupine's state, `kStep`/`refine_step`; etcd's state, the pending writes, the
revisions' map and the store's history `histAuth`), the updates it hands the store and the commits
it makes (`InvSteps.lean`), `errOut`, `call` (the four store methods through `storage.Interface`)
and `Apply` (`Apply.lean`, `lintest`'s `applySpec` against `k8setcd3S g0`), with the two marked
`sorry`s (`revRoom`, `clientErr_other`; D30n). Not yet linked (6g's driver `Link`). Still to do:
6e (`kubernetes.New`, `etcd3.New`: `isStore` with the driver's prefixes and `driverSpec`, the
history's allocation `histAuth` from the seeded state), 6g (`Gen`'s spec giving `GenIn`, `Check`,
`Main`, the initial `kInv` from the seeded store, adequacy, `gen-init` for the driver).

Done (2026-10-23): **6e**, `etcd3.New`'s spec and proof (`isStore` of the arguments' configuration,
some metrics tracker), with its callees: trust-boundary specs for the names-only
`metrics.NewEtcdMetricsTracker`, `path.Join`, `strings.TrimSuffix` and the packages' facts
`checkerInit`/`storageInit` (`Base.lean`); proved: the lease manager, the error aggregator
factories, the key reverse function. `feature.toml` imports what `client` names (G4), so it is
concrete. Premises still to discharge in 6g: the client's `ctx` field (item 6 below), `newFunc`
returning a non-nil object, `kubernetes.New`'s `kc ↦□`.

Done (2026-10-23): **6g**, the closed theorem. `k8setcd3_safe`/`k8setcd3_adequate`
(`Adequacy.lean`, `Results.lean`; collection `etc/tcb-collections/k8setcd3.txt`): every real
execution of the driver's initialization and `Main(clients, ops)` has no stuck thread, no panic,
and returns `Ok` or `Unknown`, under linkvtxn's hypotheses at the driver's configuration
(`127.0.0.1:23896`), the Kubernetes packages' semantics assumptions and the method-set fact
`objTyOk` (`*Obj` is a `runtime.Object`, not a `runtime.Unstructured`; `methodSet` is
uninterpreted). On the way: `Gen` (`GenIn`), `Check` (`lintest.Run` of `Apply` against
`Model(st0)`), the seeding (`seed` as `seedOne` of each key, the seeding's invariant `seedInv`
and the seeded state `σs2`/store `g0s`, `kInv_seed`), `Main` (the server's start as linkvtxn's,
`kubernetes.New`, `etcd3.New` with the driver's arguments, `Check`'s `Ok`), the driver's `Link`
(`etc/gen-link.py --k8setcd3`; `New` in the store's and the kubernetes client's), and package
initialization (`etc/gen-init.py`: the driver in `ROOTS`/`PROGRAMS`, entries for `etcd3`,
`storage`, `storage/feature`, `util/feature`, `etcd3/metrics` and the driver; steps inside a
translated `init` function, `after`). New trust-boundary axioms: the names-only `labels`/`fields`
`Everything`, `grpclog.SetLoggerV2`, `os.Getenv`, `strconv.ParseBool`, the conversion of a
`klogWrapper` to the axiomatized `grpclog.LoggerV2` (G3), and the initializers the facts read
(`DefaultFeatureGate`, `DefaultFeatureSupportChecker`, `ErrTransactionConflict`). `sharding.toml`
imports `runtime` (G4), so `storage.SelectionPredicate`'s `sharding.Selector` is concrete and no
result reaches an axiomatized type's `sorry`. The `sorry`s the result rests on: `revRoom` (the
revision bound, D30n), `client_ctx_field` (item 6), and the store's `kvIs_ne_null` (item 3);
`clientErr_other` (item 5 below) was a fourth until 2026-10-26 (D37b: proved, over the new
method-set premise `storageErrTyOk`).

## Phase 7: `TestCorrectness`'s etcd3 subtest (planned 2026-10-31)

The target: the `etcd3` case of `TestCorrectness`
(`k8s.io/kubernetes/test/integration/apiserver/storage/correctness_test.go`, at the DaemonSet pin
`878cfa6c4cc7`; README: "Inspired by etcd robustness testing"), the test Kubernetes uses as the
storage layer's robustness test: 8 concurrent clients run 10 000 random unary operations
(`RunUnaryTraffic`, `traffic.go`) while 16 watchers run (`RunWatchTraffic`), then porcupine checks
the unary history against `correctness.Model`, `Replay.Validate` checks every operation along
porcupine's linearization, and `WatchValidator.ValidateWatch` checks every watch against the
replay. The cacher cases are out of scope (the watch cache is a later target).

**What `k8setcd3_safe` already covers, and what the test does beyond it** (weights from
`requestDistribution`):

| Test traffic | `k8setcd3_safe` | Missing |
| --- | --- | --- |
| Create 15% | yes (`ttl = 0`) | - |
| Delete 20%: preconditions UID/RV 25% each, cached object 25%, `validateDeletion` 25% | `validateDeletion` only | preconditions; cached (stale) object |
| Update 30%: preconditions 20%/20%, no-op 15%, cached 15%, `ignoreNotFound` 15%, validate 25% | no-op, validate | preconditions; cached object; `ignoreNotFound` |
| Get 10%: `IgnoreNotFound` 50%; RV empty 30%, `0`, `1`, cached, current, past, future | consistent (RV empty) | `IgnoreNotFound`; every RV mode |
| List 25%: scope, recursive, field/label selectors, RV and RV-match modes, limit 0/1/2 | none (`GetList` names-only) | all |
| Watches (16 concurrent) | none | all (the watcher) |
| Check: porcupine, then `Replay.Validate` along the linearization, then the watch validator | porcupine (`lintest.Run`) | the replay; the watch validator |

The cached-object and precondition paths are where most of the README's etcd3 bugs live (#35415,
#43152, #54780, #77619, #89828), lists are #94002, watches #135452. The real Pod codec stays out
(D30b: the contract, with the driver's non-canonical codec), as does `TestCorrectness`'s single
real etcd process (the driver runs in-process members).

**Why stale reads need the replay.** `Model.validateGet`/`validateList` check only the response's
resource version for a non-consistent read (RV `0`, past, `NotOlderThan`, `Exact`): "contents are
validated later during replay". So porcupine's `Ok` alone says nothing about a stale read's
contents; the theorem must cover `Replay.Validate` on porcupine's linearization, which needs the
verified porcupine (`examples/lintest`, `Run`) to return the linearization it found
(`info.PartialLinearizations()`), with a spec saying it is one.

**Stages**, each closing with the driver extended to the new traffic and `k8setcd3_safe` still
closed (the Go copy of the Model and the Lean model, `KModel.lean`/`Refine.lean`, extended as the
traffic grows):

- **7a. `GetList` translated** (done 2026-10-31): the pinned Perennial supports range over a
  function (`caa9d07ee`, pin `edcadb1e5`), so `!store.GetList` is dropped from `etcd3.toml`;
  476 lines of `Code`, elaborates. G2 closed.
- **7b. The unary paths without new etcd capabilities** (done 2026-11-05, branch `k8s-etcd3-7b`; the
  sections "7b: ..." below): `Get` with a resource version (a minimum),
  `Preconditions.Check` non-nil (UID, RV),
  `cachedExistingObject` on `Delete`/`GuaranteedUpdate` (`getStateFromObject`, the
  `!origStateIsCurrent` re-read and retry: the stale-suggestion class), `ignoreNotFound` on
  `GuaranteedUpdate`, `IgnoreNotFound` on a consistent `Get`. The store's specs already state the
  outcome as the model's at one linearization point whatever the suggestion; the work is the
  proofs of the lifted branches, the model's preconditions, and the driver's traffic.
- **7c. Reads at a revision.** `kubernetes.Client.Get` with `opts.Revision ≠ 0` (its spec is at
  the latest revision only: "the only revision the server's specs serve"), over the server's
  `Range` at a revision, which M2 specified (`txn.executeRange`: `stateAt` of the read log, or
  `ErrFutureRev`, or `ErrCompacted` below the compaction revision); the client-layer specs
  (linkvtxn's `client_*`) carry it up, with the error identities ("From the etcd client proof",
  item 1). Needed by lists only (7e): `store.Get` always reads etcd's latest state
  (`store.go:299`) and uses its resource version as a minimum only
  (`validateMinimumResourceVersion`), so its RV modes are 7b's (the model's `get` has the
  minimum), not this stage's (corrected 2026-11-01).
- **7d. The replay.** The verified porcupine returns its linearization; a Go copy of `Replay`
  (or the real one, with 7g) in the driver's `Check`, proved against the history. (2026-11-07,
  `notes/k8s-7d-scope.md`: stages 1-2 built, porcupine's `linInfoOk` and `lintest.RunLin`; the
  driver's replay folded into 7e/7g, since for the current traffic it checks nothing porcupine
  does not, and the failed-write trap of its §2 and §12 shapes 7e and 7g.)
- **7e. `GetList`**, the paginated path (`EtcdRangeStream` off, so no `streamChunks`): a spec of
  `kubernetes.Client.List` (new; recursive ranges at a revision, limit, continue), `pagedChunks`'
  iterator, `appendChunk`/`processListItem` (`reflect`'s slice operations: `MakeSlice`, `Append`,
  `Set`, `Len`, `Cap`, `Copy`, as local trust-boundary specs like the store's other `reflect`
  axioms), `storage.ValidateListOptions`, `PrepareContinueToken` (continue tokens: `encoding/json`
  and `base64`, names-only now), `SelectionPredicate.Matches` for the test's selectors (labels and
  fields: names-only apimachinery), `versioner.UpdateList` (the contract grows a list half),
  `listReadError` (error identity, from 7c), and the model's `list` with pages at one revision.
- **7f. Watches.** The etcd3 watcher (`watcher.go`; G1's alias fix in Goose first, a small
  Perennial change, `notes/perennial-changes.md`), over the etcd client's `Watch` (the watch
  specs of `watchkv`/G2), the test's watcher behaviours (slow, hiccup, stalled consumers), and the
  watch validator. The largest stage; last. (2026-11-08, `notes/k8s-7f-scope.md`, to 81 for
  review: G1's fix has landed, so only the two `etcd3.toml` exclusions go; watches become lintest
  operations checked against 7e's per-configuration history; the store's watches need
  `WithPrevKV` and `WithRequireLeader` through etcd's watch stack, the second making the premise
  `runsNoRequireLeader` false; the watcher can deliver events after a `watch.Error`,
  `nonissues/k8s-etcd3-watcher-events-after-error.md`; 10-16k Lean lines in 8 sub-stages.
  Revision 2, 2026-11-08, after the review and the user's decisions: departures 1-4 accepted with
  bookmarks bounded and foreign-object events rejected; `runsNoRequireLeader` deleted with no fork
  change, through a weak handler context and a changed grpc stream-interceptor contract, Watch and
  LeaseKeepAlive re-proved; 13-21k Lean lines.)
- **7g. The maintainers' checker.** Translate `correctness` itself (`Model`, `Replay`,
  `WatchValidator`) in place of the Go copy (D30m, "Open" below), with D30g's fix as a patch
  until upstream takes it; `reflect.DeepEqual` and the list/meta accessors at the trust boundary.

Also, independent of the stages: the three `sorry`s of `k8setcd3_safe`'s own (`revRoom`,
`client_ctx_field`, `kvIs_ne_null`; the last two proved 2026-11-05, `revRoom`'s options in branch
`k8s-sorrys`'s `questions.md`, after 7b); the server's `sorry`s it rests on (`EtcdServer.run`, ...) are
the server repair's (Stage P), not this plan's.

Order: 7b first (the most bugs per unit of work, nothing new from etcd), then 7c and 7d with 7e
(stale lists are the traffic needing them), 7f, 7g. The specs' statements for 7b are under review
(2026-11-01, the `spec` skill: a cached object needs a witness of what the key held at its resource
version, `nonissues/k8s-etcd3-cached-object-trusted-at-current-rv.md`; preconditions answer the model's
own error).

### 7b: Scope (2026-11-05, branch `k8s-etcd3-7b`; approved by the user 2026-11-05)

**Approved (the user, 2026-11-05), with the recommendations:** Q0 (a), the rest of the 11-01 redesign
is a later stage of its own; Q1, P1-P5 and the traffic table as written; Q2 (a), the driver's history
records deletions (if its cost gets out of proportion: report back, do not switch to (b)); Q3 (a),
`Get`'s current/past/future resource versions relative to the client's cached object's; Q4 (a), the
model checks a `Get` with a resource version exactly. Next: Draft.

**Where the 2026-11-01 review ended.** Three candidates and two `spec-reviewer` rounds, in scratch
files that were not committed and are gone; what survives is `notes/STATUS.md`'s summary (one KV in
place of the member lists; the updates in the triples; the general methods: preconditions as data
answering the model's own error, a cached object held by the key at its revision, `Get`'s minimum;
errors through laws), the non-issue it found, and "waiting on the user's decisions". None of it was
decided, so this Scope starts from the specs on `lean` and re-proposes the third group (the one 7b
needs); the other three are Q0 below.

**The paths** (store.go at the pin; all reached by `TestCorrectness`'s unary traffic):

| Path | Code | What is new for the proof |
| --- | --- | --- |
| P1. `Get` with a minimum resource version | `validateMinimumResourceVersion` (`store.go:1286`): parse (the versioner's `ParseResourceVersion`, in the contract), `NewTooLargeResourceVersionError` if above the read's revision | the model's `get` already takes the minimum (`KSt.get req`); `respIs`'s `tooLarge` answer gets a shape (`tooLargeErrIs`: a `*apierrors.StatusError`, reason `Timeout`, the `ResourceVersionTooLarge` cause), proved from `NewTimeoutError`'s translated body (no axiom) |
| P2. `IgnoreNotFound` on `Get` | `store.go:311` | nothing: already in `store.Get.spec` and in the driver (half its `Get`s) |
| P3. `Preconditions.Check` non-nil (UID, RV) on `Delete` and `GuaranteedUpdate` | `interfaces.go:145`: `meta.Accessor`, `GetUID`/`GetResourceVersion`, `NewInvalidObjError` with a `fmt.Sprintf` message | preconditions as data (`KPre`: optional UID, optional RV string) in the model, a failure answering the model's own `InvalidObj` error (code 4, the prepared key; message unspecified); `meta.Accessor` and the two accessors on the object (below) |
| P4. `cachedExistingObject` on `Delete`/`GuaranteedUpdate` | `getStateFromObject` (`store.go:1239`), `refreshOnError`'s stale branch (`store.go:128`: re-read, the cached error kept when the revision did not move), `GuaranteedUpdate`'s `!origState.current` re-read before a no-op (`store.go:556`), the conflict retry from a stale state | the witness (below); `refreshOnError.spec` and the loops' invariants over a non-current state |
| P5. `ignoreNotFound` on `GuaranteedUpdate` | `getCurrentState`/`stateFromEtcdResponse` with `ignoreNotFound` (`runtime.SetZeroValue`, in the contract's `zeroOk`); a conflict's re-read of an absent key | the model's `update` already takes it (`KSt.current`); the specs' `false` generalized |

**What admitting the cases breaks** (where the statements rule them out today, and whether each stays
true): `store.Delete.spec`/`GuaranteedUpdate.spec` (and `conditionalDelete`, `deleteOnce`,
`updateOnce`) pass `#null` preconditions and a `nil` cached object, and `GuaranteedUpdate`'s
`ignoreNotFound` is `false`: generalized, callers re-proved (the driver's `call` only). `Get.spec`'s
premise `opts.ResourceVersion' = []`: replaced by "the minimum parses" (below). `refreshOnError.spec`
requires `s.current = true`: generalized. `Preconditions.Check.spec` and
`validateMinimumResourceVersion.spec` cover only `nil`/`""`: generalized. The model's
`KSt.delete`/`update` take preconditions as a caller's error function `pre : Obj → Nat → Option E`:
replaced by data (`KPre`) with `.err (.invalidObj key)` (`KErr` gains it); `update_eq_updateM`,
`delete_local`, `update_local`, `refine_*` restated. `respIs` answers `tooLarge` and `invalidObj` as
"some error": given shapes. The driver's `Gen` is a pure function of a random number (no cached
object to pick from), its `Model` has no preconditions, minimum or `ignoreNotFound` update, its
`errOut` no `InvalidObj`/`TooLarge` class, and its `Obj` no UID and no `metav1.Object` methods. The
store's history `kvSeen` records the key-values of the states seen, not deletions: what a deleted
object's witness needs (Q2). Not touched: the client's specs (`kubernetes.Client.*`, so the compactor's
`k8s_compactor_safe` is unaffected), `k8sAuRW`/`k8sAu1`, `Create`, `GetCurrentResourceVersion`,
`etcd3.New`, the five `sorry`s outside 7b.

**The top-level statements, sketched** (to be written in full in Draft):

```lean
-- the model (Model.lean)
structure KPre where uid : Option GoString; rv : Option GoString
def KPre.ok (p : KPre) (uidOf : Obj → GoString) (fmtRV : Nat → GoString) (o : Obj) (r : Nat) : Bool
inductive KErr E | notFound k rv | keyExists k | rvSetOnCreate | tooLarge req cur
                 | invalidObj (key : GoString) | user (e : E)
KSt.delete s k (p : KPre) validate   -- not found; invalidObj k if ¬ p.ok; validate's error; the delete
KSt.update s k ign z (p : KPre) f    -- as now, `pre` replaced by `p`

-- the cached object (Steps.lean): r is its resource version, never 0, and any state the caller's
-- history has seen with the key at mod revision r holds o there
def heldAt (c) (key) (o : Obj) (r : w64) (σ : KVState) : Prop :=
  modAt key σ = r → ∃ it, (c.abs σ).items key = some it ∧ it.obj = o
def cachedOk (c) (key) : Option (GoInterface × Obj × w64) → GoInterface → IProp GF
  | none, x => ⌜x = GoInterface.nil⌝
  | some (x', o, r), x => ⌜x = x' ∧ r ≠ 0⌝ ∗ c.S.objAt x o (c.S.fmtRV r) ∗
      □ ∀ σ, kvSeen c.γh σ -∗ ⌜heldAt c key o r σ⌝

-- store.Delete.spec: the preconditions `pp` (null or a `*Preconditions` holding `p`) and the
-- cached object are arguments; the step and the answer are the model's with `p`
{{ … ∗ preAt pp p ∗ cachedOk c (pathPrefix ++ k) ca x ∗ W ∗
     [∗list] m ∈ c.ms, k8sAuRW m.γr.kv c (delStep (pathPrefix ++ k) p validate) W Φ ∗ validateOk … }}
  s.Delete(ctx, key, out, pp, vf, x, opts)
{{ err, RET err; delOut c (pathPrefix ++ k) p validate Φ err out }}
-- store.GuaranteedUpdate.spec: likewise, with `ign : Bool` for ignoreNotFound and
-- `updStep (pathPrefix ++ k) ign c.S.zero p f`
-- store.Get.spec: `c.S.parseRV opts.ResourceVersion' = some n` in place of `= []`; the answer
-- `(c.abs σ).get key (uint.nat n) opts.IgnoreNotFound'`
```

The witness is abstract on purpose (a persistent implication over the states the history has seen,
the shape `k8sAuRW_kvAu1`'s `A` already has): the store needs only that a compare on `r` that succeeds
is at a state whose item is `o`, and a caller produces it however it can (a `kvSeen` entry for an
object it was answered, a deletion record for a deleted one).

**The driver's traffic** (`TestCorrectness`'s `requestDistribution` without `List`, renormalized:
Create 15, Delete 20, Get 10, Update 30 of 75):

| Op | Choices (as the test's weights) |
| --- | --- |
| Create (20%) | a new UID drawn at random (the test's `uuid.NewUUID()`; a range of 2^16, so a recreated object's UID differs from the old one's almost always) |
| Delete (27%) | UID precondition 25%, RV precondition 25% (from the client's cached object; none cached: none), cached object 25%, `validateDeletion` 25% |
| Update (40%) | UID 20%, RV 20%, no-op 15%, cached 15%, `ignoreNotFound` 15% (not with a no-op, as the test), `tryUpdate` rejecting 25%; on the zero object `tryUpdate` makes the key's object (the test's `validPod`, UID empty) |
| Get (13%) | `IgnoreNotFound` 50%; RV empty 30, `0` 15, `1` 10, cached 15, current 14, past 14, future 2, where current/past/future are relative to the client's cached object's RV (the test asks the store's `GetCurrentResourceVersion`; Q3) |

The cached object is, as in the test, the client's last answer with a non-empty name (Create, Update,
Delete and Get answers; Q2 for Delete's): the driver keeps one per client in a table under a
`sync.Mutex`, `Gen(id)` reads it (and copies it into the input, which also carries the client's id
and the preconditions' values), `Apply` writes it after a call; the table's lock invariant holds each
entry's witness. Keys `a`, `b`, `c`, values `x`, `y`, `z`, two keys seeded non-canonical, as now.
The Go model gains UIDs, preconditions, the minimum and the update's `ignoreNotFound`; its Go tests
are extended (the new outcomes reached sequentially; agreement with the real `correctness.Model` on
random traffic from canonical states, with preconditions and `ignoreNotFound`).

**What stays a premise or outside.** The minimum parses (the driver sends only its versioner's
strings; a malformed one would answer the versioner's error, not specified). The rest of phase 0's
configuration (D30d: `ExpectTransformOrDecodeError` false, `ttl = 0`, no `tryUpdate` TTL). Lists,
watches, the replay (7c-7f). The failed-write rule (pending writes) and the five `sorry`s, unchanged.

**The trust base, expected.** New trusted statements, each drafted and attacked (`axiom` skill)
before the Freeze:
- `fmt.Sprintf` with `types.UID` arguments (`Preconditions.Check`'s UID message): Perennial's spec
  formats only basic types and named integer types (`ArgWf`); a local spec "returns some string",
  with the general fix (named string types without formatting methods, as named integers) in
  `notes/perennial-changes.md`.
- `meta.Accessor` (names-only, apimachinery): either translate its body (a type switch;
  `meta.toml` gains `Accessor`; its initializer `errNotObject` goes through `gen-init`), so no axiom,
  and the DaemonSet's pending `Accessor.spec` hypothesis becomes provable (recommended), or a local
  spec for the driver's `*Obj`.
- None for the driver's `*Obj` implementing `metav1.Object` (31 methods, hand-written, two of them
  meaningful): the method-set facts come from goose's method sets, as `objTyOk_holds`.
- The client errors are not `*apierrors.StatusError`s (what `errOut`'s new `TooLarge` test needs, as
  `storageErrTyOk` for `StorageError`): from `statusErrOk`/`clientErr` if they say enough, otherwise
  a method-set premise or a Draft question.

**Sub-stages** (each builds; one full build per round): 7b-1 the model and contract (`KPre`,
`invalidObj`, `uidOf` and the accessors in `ObjSpec`), Draft of every changed statement with glue
(`Delete`, `conditionalDelete`, `GuaranteedUpdate`, `refreshOnError`, `getStateFromObject`,
`Preconditions.Check`, `validateMinimumResourceVersion`, the driver's `call`/`Apply`/`Gen`/invariant
written out), review rounds, then the Freeze (the user); 7b-2 the store's proofs (P1, P5, P3, P4 in
that order); 7b-3 the driver's Go (`Obj`, `Input`, `Gen` with the table, `Model`, `errOut`) and Go
tests; 7b-4 the driver's model proofs (`KModel`, `Refine`, the per-function proofs); 7b-5 the
invariant (witnesses, the table), `Apply`, `Check`, `Main`, `k8setcd3_safe` closed, the collection's
baseline.

**Questions for the user.**
- **Q0. The rest of the 2026-11-01 redesign** (one KV in place of the member lists, the updates in the
  triples, errors through laws). (a) Not in 7b: 7b generalizes the current statements as sketched, the
  redesign is its own later stage (it touches every store spec and the client's, for no new
  behaviour). (b) Do it first, in 7b. Recommended: (a).
- **Q1. The paths and traffic above.** Recommended: all of P1-P5, the traffic as in the table.
- **Q2. Deleted objects as cached objects.** The test caches a `Delete`'s answer (the object at the
  deletion's revision; #89828's class: a deleted object as the suggestion). Its witness is that no
  state has the key at the deletion's revision, which the history `kvSeen` cannot say today. (a)
  Cache them, as the test: the driver's history records deletions (`γh`'s values become
  `Option GoString`, `none` for a key deleted at that revision; `History.lean`, the driver's
  invariant), the store's specs unchanged (the witness is abstract). (b) Cache only Create, Update
  and Get answers (a deviation from the test). Recommended: (a); (b) if (a)'s cost is out of
  proportion (to be reported, not done silently).
- **Q3. Get's current/past/future resource versions.** (a) Relative to the client's cached object's
  RV (no store call in `Gen`; `Gen` stays a function of randomness and the client's table). (b) As the
  test, `Gen` asks the store's `GetCurrentResourceVersion` (proved) first: `Gen` needs the store and
  read updates, outside the history. Recommended: (a).
- **Q4. How the driver's model checks a `Get` with a resource version.** `correctness.Model.validateGet`
  checks only the answer's resource version for a non-empty one ("contents are validated later during
  replay"), because the cacher may serve stale data; the etcd3 store always reads the latest state.
  (a) The driver's model checks every `Get` exactly (the model's `get` at the linearization point):
  a stronger theorem, true of the store. (b) Copy `validateGet`'s weaker check. Recommended: (a).

### 7b: Draft, the trusted statements (2026-11-05; approved by the user 2026-11-05)

**Approved (the user, 2026-11-05), with the recommendations:** T1, `types.UID` added to
`fmt.methodlessNamedTypes` (the general fix recorded in `notes/perennial-changes.md`; the `axiom`
skill's attack still due before the Freeze). T2 (b), the driver answers a too-large error as `EOther`
for now; (c), strengthening the client's `clientErr` to exclude a `*apierrors.StatusError`, is a later
client change that restores the exact check (below, "From the etcd client proof").

Done since the approval: the driver's Go (`examples/k8s/etcd3/k8setcd3.go`: objects with a UID,
preconditions, cached objects, `IgnoreNotFound`, minimum resource versions, the per-client table,
the Go model and its tests, 1500-operation stats test with every new outcome reached) and
`meta.Accessor` translated (`meta.toml`: `Accessor`; no axiom, as recommended in the Scope).
Two questions came up before the Lean statements, both about trust.

**T1. `fmt.Sprintf` with `types.UID` arguments.** `Preconditions.Check` (`interfaces.go:145`) answers
a failed UID precondition with `NewInvalidObjError(key, fmt.Sprintf("Precondition failed: UID in
precondition: %v, UID in object meta: %v", *p.UID, objMeta.GetUID()))`. Perennial's `fmt.wp_Sprintf`
admits basic types and named integer types only (`ArgWf`); `types.UID` is `type UID string`.
- *Proposed* (the smallest change): add `types.UID` to the list of the existing trust-boundary axiom
  `fmt.SprintfNamed.wp_proof` (`Spec/fmt/SprintfNamed.lean`, drafted on the branch, uncommitted until
  approved):
  old `fmt.methodlessNamedTypes = [LeaseID]`, new `= [LeaseID, types.UID]`; the statement of
  `fmt.SprintfNamed.spec` is unchanged. No new axiom: the existing one admits more arguments.
- *Why sound* (the `axiom` skill's question: a Go program that panics or returns other than the spec
  says): `k8s.io/apimachinery/pkg/types/uid.go` is the whole declaration of `UID`, no methods (checked
  at the pinned apimachinery), so Go's `fmt` calls no `Error`/`String`/`Format`/`GoString` and prints
  the string; `fmt` never panics on an argument it formats by kind. What the spec promises of the
  output: `SprintfOut format xs s`, where `%v` (and `%s`) of a non-`go.string`, non-integer argument is
  not a `SimpleDirective`, so `SprintfOut.other` makes everything from the first `%v` on arbitrary;
  the bytes before it are copied, as Go does. No promise about the UIDs' text, so nothing false to
  derive. (The k8setcd3 statements need only "returns some string": the message is unspecified.)
- *Who rests on it*: collections `concurrency` (already) and `k8setcd3` (new, through
  `Preconditions.Check`). Proofs using membership (`Mutex.tryAcquire`, `Election.Campaign`) prove it
  by `simp [fmt.methodlessNamedTypes]`, unaffected by a second element.
- *General fix* (Perennial, independent, entry in `notes/perennial-changes.md`): `ArgWf` admits a
  named type with `fmt.NoFmtMethods` whatever its basic underlying type (today integers only), the
  output of a non-integer one arbitrary; then the list goes, with `LeaseID`'s.
- *Alternatives*: (b) a separate axiom `Preconditions.Check.wp_proof` (larger: the whole function at
  the trust boundary); (c) leave UID preconditions out of 7b (P3 checks RV only; the test's UID
  traffic is the case #89828's class needs). Recommended: the list extension.

**T2. The `TooLarge` answer's classification in the driver.** The driver's `errOut` tells a
`TooLarge` answer by `apierrors.IsTooLargeResourceVersion` (a `*StatusError`, reason `Timeout`, a
`ResourceVersionTooLarge` cause). Proving that `errOut` gives `ETooLarge` only for the store's own
`NewTooLargeResourceVersionError` needs that the etcd client's errors (which the store passes through,
answering `EOther`, which the model admits anywhere) are not such `*StatusError`s. Neither `clientErr`
nor `statusErrOk`/`errCellOk` say it.
- (a) A premise (or method-set axiom) "a client error is not a `*apierrors.StatusError`": new trust.
- (b) The driver answers `EOther` for a `TooLarge` error (no `isTooLarge` test in `errOut`; the Go
  model's `get` admits `EOther` where it answered `ETooLarge`). No trust growth. What is lost: the
  check that the store answers too-large exactly when the minimum is above the read's revision.
  What stays: the store's spec still states the shape (`tooLargeErrIs`, proved from
  `NewTimeoutError`'s body); a `Get` that should be too large but returns an object (a stale read
  served as fresh) is still caught, as a `Get` answering an object is checked exactly (Q4).
- (c) Strengthen the client's `clientErr` to exclude `*StatusError` (the client's track; the
  compactor's `k8s_compactor_safe` rests on the same specs).
- Recommended: (b) now, (c) as a later client change that restores the check.

### 7b: Draft, the cached no-op (2026-11-05; the user chose (a), 2026-11-05)

**Decided (the user, 2026-11-05): (a), a scope premise.** The driver's traffic never pairs a cached
object with a resource-version precondition on an update (`genFrom`); UID preconditions with a
cached object stay, RV preconditions stay on uncached updates and on every `Delete`. Cause: the
finding below (`issues/k8s-etcd3-cached-noop-skips-preconditions.md`), on which the store's answer is
not the model's. The theorem does not cover that combination; the issue holds the bug report.

Drafting `GuaranteedUpdate`'s spec with a cached object found that the store's answer is not the
model's on a path the approved traffic reaches (`issues/k8s-etcd3-cached-noop-skips-preconditions.md`;
`examples/k8s/etcd3/cachednoop_test.go` reproduces it against an etcd member). When `tryUpdate`
leaves the cached object unchanged, the store re-reads the key (`store.go:556`) and, if the bytes
are equal, returns the current object (or, if stale, writes) without re-running the preconditions
or `tryUpdate` on the re-read state, whose revision may differ from the cached object's. With a
resource version precondition naming the cached version, the store answers the object at the newer
version where the model (and `correctness.Model`) answers `InvalidObj`. The driver reaches it: a
cached object, an RV precondition and an update that leaves the object as it is (`NoOp`, or a value
equal to the current one), after the key was rewritten with equal bytes (a non-canonical seed's
rewrite, or a delete and an `ignoreNotFound` re-create of the same object). Without an RV
precondition the answers agree (the driver's `tryUpdate` ignores the resource version, and a UID
precondition is the same on equal bytes); `Delete` has no such shortcut.

- **(a)** The traffic: an update with a cached object carries no RV precondition (UID preconditions
  stay; RV preconditions stay on updates without a cached object and on every `Delete`). The theorem
  does not cover the case; the finding is recorded, for an upstream report once a test in the
  store's own harness exists (the `upstream-report` skill). Cost: one line in `genFrom`, the stats
  test unchanged.
- **(b)** Fix the store on a copy of `k8s.io/apiserver` (a `replace` in `examples/k8s/etcd3/go.mod`
  to a patched module, translated by goose): continue the loop after the re-read unless its
  revision is the cached one. The traffic as approved. Cost: a patched copy of the module in the
  repository (or a fork to push), and a fix not upstream.
- **(c)** Weaken the model to the store's behavior (the update takes the cached object's version
  and admits the newer object): the theorem states the bug as correct. Not recommended.
- Recommended: (a).

### 7b: Draft, the design (2026-11-05; each statement old → new, and what it is proved from)

Written before threading the sites (`notes/spec-first-plan.md`, "Design before plumbing"). Names as in
`Proof/k8s_io/apiserver/pkg/storage/etcd3/` unless said.

**The model** (`Model.lean`). `KErr` gains `invalidObj (key)`. The preconditions become a predicate:
`KSt.delete s k (pre : Obj → Nat → Bool) validate` (old: `pre : Obj → Nat → Option E`): no item →
`notFound`; `pre it.obj it.rv = false` → `.err (.invalidObj k)`; then `validate` as now. `KSt.update s
k ign z pre f` (and `updateM`) likewise, `pre` checked on `current` (the item, or `(z, 0)` with
`ign`). `update_eq_updateM`, `AllCanon_*`, `absK_delete`/`absK_update`, `update_noop`: restated
(`pre … = true` for `= none`), same proofs.

**The contract** (`Contract.lean`). `ObjCodec` gains `uid : Obj → GoString` (the object's UID) and two
laws: `fmt_zero : fmtRV 0 = []` (the versioner renders `0` as `""`, as `APIObjectVersioner` does: the
zero object's string is the one `fmtRV` gives at `0`) and `encode_ne_nil : ∀ o, encode o ≠ []` (a
stored object's encoding is not empty: the zero state's data is `[]`, and the store's no-op test
compares with it). `ObjSpec.tyOk` gains `typeSetContains (*objTy) metav1.Object.ty = true`
(`meta.Accessor`'s first case). `contractOk` gains `metaOk S := □ ∀ x o rv, metaAt x (S.objAt x o rv)
(S.uid o) rv`, with, in `Proof/k8s_io/apiserver/pkg/storage/Defs.lean` (the storage package's
vocabulary, so that `Preconditions.Check`'s spec does not name the etcd3 store's):

```lean
-- an object `x` (owned as `R`) as a metav1.Object: its dynamic type is one, and GetUID /
-- GetResourceVersion answer `uid` / `rvs`, leaving `R`
def metaAt (x : GoInterface) (R : IProp GF) (uid rvs : GoString) : IProp GF :=
  □ (R -∗ ⌜∃ ii, x = .ok ii ∧ typeSetContains ii.ty metav1.Object.ty⌝) ∗
  □ (∀ ii Φ, ⌜x = .ok ii⌝ -∗ R -∗ ▷ (R -∗ Φ #uid) -∗ WP (methods ii.ty "GetUID" ii.v) #() {{Φ}}) ∗
  □ (∀ ii Φ, ⌜x = .ok ii⌝ -∗ R -∗ ▷ (R -∗ Φ #rvs) -∗ WP (methods ii.ty "GetResourceVersion" ii.v) #() {{Φ}})
-- a *Preconditions (null: none) holding p
structure KPre where uid : Option GoString; rv : Option GoString
def preAt (pp : Loc) (p : KPre) : IProp GF :=
  ⌜pp = null ∧ p = ⟨none, none⟩⌝ ∨ ∃ lu lr, pp ↦□ Preconditions.mk lu lr ∗ optPtr lu p.uid ∗ optPtr lr p.rv
def KPre.ok (p : KPre) (uid rvs : GoString) : Bool := p.uid.all (· = uid) && p.rv.all (· = rvs)
-- NewInvalidObjError(key, _): a *StorageError, code 4, the key, an inner error
def invalidErrIs (err : GoInterface) (key : GoString) : IProp GF :=
  ∃ l e, ⌜err = mkOk (*StorageError) #l⌝ ∗ l ↦□ StorageError.mk 4 key 0 e  -- (review S5: no `e ≠ nil`)
```

and in the store's `Steps.lean`: `c.S.preOk p o r := p.ok (c.S.uid o) (c.S.fmtRV (W64 r))`.

**The cached object** (`Steps.lean`; `Store.lean`'s `kvSeen` over the revision-keyed history, Q2 and
D2 below):

```lean
def versionAt (c) (key) (r : w64) (o : Obj) : IProp GF :=   -- persistent
  □ ∀ σ, kvSeen c.γh σ -∗ ⌜modAt key σ = r → ∃ b, (c.abs σ).items key = some ⟨o, uint.nat r, b⟩⌝
def cachedOk (c) (key) (x : GoInterface) : Option (Obj × w64) → IProp GF
  | none => ⌜x = nil⌝
  | some (o, r) => ⌜r ≠ 0⌝ ∗ c.S.objAt x o (c.S.fmtRV r) ∗ versionAt c key r o
```

**Callee specs, new or changed:**
- `meta.Accessor.spec` (D3: the existing spec, the DaemonSet track's hypothesis for four pointer
  types, generalized in place and proved from the translated body): `∀ ii, typeSetContains ii.ty
  metav1.Object.ty = true → {{ True }} Accessor(.ok ii) {{ RET (.ok ii, nil) }}`;
  `RealPodControl.createPods` gives the fact for `*apps.DaemonSet`.
- `storage.NewInvalidObjError.spec` (new; body): `{{ True }} (key, msg) {{ p, RET #p; p ↦ StorageError.mk 4
  key 0 e ∗ ⌜e ≠ nil⌝ }}`.
- `storage.Preconditions.Check.spec` (old: `p = nil` only): `{{ preAt pp p ∗ metaAt x R uid rvs ∗ R }}
  pp.Check(key, x) {{ err; R ∗ (if p.ok uid rvs then ⌜err = nil⌝ else invalidErrIs err key) }}`
  (review S7: `metaAt` always, `Check` calls `Accessor` before testing `pp`)
  (from `Accessor`, `NewInvalidObjError`, `fmt.SprintfNamed` (T1) and `fmt.wp_Sprintf`).
- `storage.NewTooLargeResourceVersionError.spec` (old: `err ≠ nil`): `err = mkOk (*apierrors.StatusError)
  #l` for some `l` (body, `NewTimeoutError`'s spec).
- `store.validateMinimumResourceVersion.spec` (old: `""` only): `{{ ⌜S.parseRV m = some n⌝ ∗ versionerOk
  }} (m, rev) {{ err; if n > rev then tooLarge shape else err = nil }}`.
- `store.getStateFromObject.spec` (new): from `cachedOk … (some (o, r))`, a `*objState` with
  `ownState c st ⟨o, r, encode o, current := false, stale := false⟩` (from `versionerOk`'s three
  methods and `encodeOk`; encode errors as now).
- `store.getCurrentState.spec`/`stateFromEtcdResponse.spec`/`stAt`/`getStateOk`: `ign : Bool` (old:
  `false`); `stAt c key ign σ st err` answers, for an absent key with `ign`, `ownState c st (zeroSt
  c)`, `zeroSt = ⟨zero, 0, [], current, ¬stale⟩` (from `zeroOk`).
- `stFrom c key s` (new, persistent): where the state came from: a read (`∃ σ0 kv0, rdFacts c σ0 ∗
  ⌜findKey key σ0 = some kv0 ∧ stOfKv c kv0 s⌝`), an absent key read with `ign` (`∃ σ0, rdFacts c
  σ0 ∗ ⌜findKey key σ0 = none ∧ s = zeroSt c⌝`), or the cached object (`⌜¬s.current ∧ ¬s.stale ∧
  s.data = encode s.o ∧ s.rev ≠ 0⌝ ∗ versionAt c key s.rev s.o`). Each gives, at a state seen in the
  history with the key at `s.rev`, the item `⟨s.o, s.rev, b⟩` with `b → (!s.stale && encode s.o =
  s.data)` (`stFrom_item`), or no item when `s.rev = 0`: what `delete_at`/`update_at` need.
- `refreshOnError.spec` (old: `s.current` only): on a current state, `(st, err)` unchanged; otherwise
  it calls the closure (`getStateOk`, a maker for its read) and answers the client's error, or `stAt`
  at the read's state `σ` with `err' = if modAt key σ = s.rev then err else nil` (the old state's
  object dropped).
- `store.deleteOnce.spec`/`updateOnce.spec`: `stFrom c key s` in place of `σ0, kv0, rdFacts σ0`
  (S3: the no-op `Update` path's re-read gives the witness of the state it returns, from that read's
  `kvSeen`, `update_noop_reread`; S1: an `OptimisticPut` at mod revision `0`, the zero state with
  `ign`, creates the key, `put_cases0`/`updStepOk0`),
  `c.S.preOk p s.o s.rev = true`, the step `delStep key pre validate` / `updStep key ign z pre f`;
  the answers `(c.abs σ).delete key pre validate` / `.update key ign z pre f`; on a conflict
  `stAt c key ign σ`.
- `delStepOk`/`updStepOk`/`delete_at`/`update_at`/`delete_invalid`/`update_err`/`update_skip`/
  `update_none`, `handOk_*`, `*_loc`, `*_local` (glue lemmas): `pre` and `ign` added, the item from
  `stFrom_item` in place of `sameAt`.

**The top-level store specs** (`k`: the prepared key):

```lean
-- store.Delete.spec: preconditions `pp` (holding `p`) and the cached object `cx` are arguments
{{ … ∗ preAt pp p ∗ cachedOk c (pathPrefix ++ k) cx ca ∗ c.S.objAt out o0 rv0 ∗ W ∗
   [∗list] m ∈ c.ms, k8sAuRW m.γr.kv c (delStep (pathPrefix ++ k) (c.S.preOk p) validate) W Φ ∗
   validateOk c validate vf }}
  s.Delete(ctx, key, out, pp, vf, cx, opts)
{{ err; delOut c (pathPrefix ++ k) (c.S.preOk p) validate Φ err out }}
-- store.GuaranteedUpdate.spec: likewise with `ign` (ignoreNotFound); the pure premises are
-- ⌜⌝ conjuncts of the precondition (review S4), two more size premises and the cached object's
-- scope premise (D1, review F1: the cached no-op path runs neither on the re-read state):
--   ign = true → ∀ o', f c.S.zero 0 = .ok o' → c.S.storedSizeOk o'
--   ∀ o r, ca = some (o, r) → ∀ n o', f o n = .ok o' → c.S.encode o' ≠ c.S.encode o → c.S.storedSizeOk o'
--   ∀ o r, ca = some (o, r) → p.rv = none ∧ ∀ n, f o n = f o (uint.nat r)            (D1)
-- the step `updStep (pathPrefix ++ k) ign c.S.zero (c.S.preOk p) f`, the answer `updOut … ign …`
-- store.Get.spec: `c.S.parseRV opts.ResourceVersion' = some n` (old: `= []`); the answer
--   `(c.abs σ).get key (uint.nat n) opts.IgnoreNotFound'`
-- conditionalDelete.spec: as Delete (the prepared key).
```

`respIs` gives `.err (.invalidObj k)` the shape `invalidErrIs err k` and `.err (.tooLarge _ _)` the
shape `∃ l, err = mkOk (*StatusError) #l` (T2 (b): the driver tells it from a `*StorageError` and its
sentinels by type, and answers `EOther`); `delOut`/`updOut` take `pre` (and `ign`).

**The history** (`Store.lean`, `History.lean`; D2, review F2: revision-keyed, so that a witness says
a revision did not change a key): `γh : rev ↦□ Changes`, `Changes := List (GoString × Option
GoString)` with distinct keys (`some` value written, `none` deleted); `kvSeen γh σ := □ ∀ v ∈ σ.kvs,
∃ ch, v.modRev ↦□ ch ∗ ⌜(v.key, some v.value) ∈ ch ∧ keys distinct⌝`. `histAuth_next` adds `σ'.rev ↦
chgOf σ σ'` (the step's new key-values, then its deleted keys) and returns it (`revSeen γh σ σ'`);
`chgOf_new`/`chgOf_del`/`chgOf_keys` say what it holds. `kvSeen_agree` and the store's uses unchanged
in form (done, checked).

**The driver.** `DObj` gains the UID (`{ (name, uid, val) // name.length < 256 ∧ uid.length < 256 }`;
the Go `Obj` its `UID` field, `encodeWith` its length and bytes), `codecD.uid`; `objTyD`'s method set
gives `metav1.Object` (`tyOk`); `metaOk` from `GetUID`/`GetResourceVersion`'s bodies. `GenIn` gains: a
cached object's name is the input's key, its value at most `2 ^ 20` bytes is not needed (the size
premise on a cached object holds for `updD`: a changed object takes the input's value). `kInOk`
(`Apply`'s input) carries, with `UseCached`, the cached object's witness `versionAt c (mkeyL key) r o`
and `r ≠ 0` (persistent). The table: `cacheInv c tbl := ∃ m, tbl's map ↦ m ∗ [∗ map] id ↦ ob ∈ m,
versionAt c (mkeyL ob.Name) ob.RV (dobjOf ob) ∗ ⌜ob.RV ≠ 0⌝`, in the `sync.Mutex`'s lock invariant
(`Gen` reads an entry under the lock, `Apply` writes one). Witnesses: a `Get` answer from its read's
`kvSeen` (`Q` includes it); a `Create`/`Update`/`Delete` answer from the write's `revSeen` (the
revision's changes: the key's new value or `none`, and no other key, so `versionAt` holds for every
key, vacuously for the others: `genFrom` attaches a cached object to an operation on any key, D2). The Lean
model (`KModel.lean`/`Refine.lean`): `kStep` with `KPre`, `invalidObj` → `EInvalid`, the minimum,
`ignoreNotFound` updates; the refinement restated.

### 7b: Draft, the driver as written (2026-11-05; frozen by the user 2026-11-05)

The design's driver paragraph above, as the statements came out (commits `5468af8faf`, `08c4901da6`):

- **The table** (`Proof/.../k8s/etcd3/Cache.lean`): `cachedObjOk c ob := ⌜name, UID < 256 ∧ ob.RV ≠ 0⌝ ∗
  □ ∀ k, versionAt c k ob.RV (dobjOf ob)` (every key, D2: `genFrom` attaches the cached object to an
  operation on any key, as the test); `cacheInv c tbl := ∃ mp m, tbl.objs ↦ mp ∗ mp ↦$ m ∗ [∗ map]
  _ ↦ ob ∈ m, cachedObjOk c ob`; `isCache c tbl := sync.isMutex tbl.mu (cacheInv c tbl)`;
  `cachedIn c x := if x.UseCached then cachedObjOk c x.Cached else True`. So the design's "`GenIn`
  gains: a cached object's name is the input's key" is dropped (D2 keeps the test's traffic).
- **The generator**: `genFrom.spec` (old: `∀ n, {{ True }} genFrom(n) {{ x; ⌜GenIn x⌝ }}`): `∀ n id c hasC,
  {{ isPkgInit }} genFrom(n, id, c, hasC) {{ x; ⌜GenIn x ∧ (x.UseCached → hasC ∧ x.Cached = c)⌝ }}`;
  `GenIn` gains `UID < 256`, `parseRVD MinRV` defined, `CachedNoRV x` (D1 in the traffic: `UseCached →
  Kind = update → ¬HasPreRV`). `Gen.spec` (old: `⊢ lintest.genSpec Gen kInOk`): a triple `{{ isPkgInit ∗
  isCache c tbl }} Gen(tbl, id) {{ x; ⌜GenIn x⌝ ∗ cachedIn c x }}`; `Check`'s closure gives
  `lintest.genSpec` (proved). `kInOk c i := ∃ x, ⌜i = boxIn x ∧ GenIn x⌝ ∗ cachedIn c x` (old: pure,
  no `c`). New: `uidOf`/`withPre`/`minRV` (`RET #(uidOfL u)`, `withPreL`, `minRVL`: Lean functions of
  the Go code), `newCache` (`isCache c tbl` for any `c`), `cache.get` (`if ok then cachedObjOk c o`),
  `cache.put` (takes `cachedObjOk c o`), `preconditions` (`preAt pp (kpreOf x)`), `cachedObj` (`if
  UseCached then ∃ p, cx = &p ∗ p ↦ x.Cached else cx = nil`).
- **`call.spec`**: gains `CachedNoRV x` and `cachedIn c x`; `callPre`'s steps take `preD x` and, for an
  update, `x.IgnoreNotFound`; `InOk` gains `UID < 256` and `parseRVD MinRV` defined. **`Apply.spec`**
  gains the table (`Apply(s, tbl, i)`, `isCache c tbl`) and `kInOk c`. **`Check.spec`, `Main.spec`,
  `k8s_etcd3_adequate`: unchanged** (the `metav1.Object` conjunct of `objTyOk` is proved from the
  instances the adequacy theorem already has).
- **The model's answers**: `errIs` gains `EInvalid` (`invalidErrIs err k`, `⟨5, k, 0, …⟩`);
  `NoOddErr` no longer excludes `tooLarge` (placed as `EOther`); `kStep_err`/`kStep_ans` take
  `Kind ∈ {create, delete, update} ∨ minOf x ≤ rev` (the model answers `EOther` to a too-large
  minimum, as `mget`); `get_read_au` therefore needs the minimum reached at the read's revision
  (D5). `errOutL` is now `otherL`'s value.
- **Proved in the Draft**: `Gen`, `Check`, `call`'s `Create` and `Get` branches, `errOut` (with
  `EInvalid`), `seedOne`, `Seed`'s relation (the UID `""`), the `Calls`/`InvSteps` glue. **Sorry at
  the failing step, text kept** (`835795d4d1` on `lean` had them): `genFrom`; `call`'s `Delete` and
  `GuaranteedUpdate` branches (preconditions, cached object, `cachedOk` from `cachedIn`); `Apply`'s
  put of an answer (four branches: `cachedObjOk` from the answer's state, D4) and its too-large
  `EOther` `Get`; `kStep_ans`'s `Get` case; `get_read_au`'s minimum (D5); `respIs_call`'s
  `tooLarge` branch (the sentinels by `drvInit`); the new functions' bodies (`uidOf`, `withPre`,
  `minRV`, `newCache`, `cache.get`/`put`, `preconditions`, `cachedObj`, `rvBytes`, `preOk`,
  `sameObj`), `decodeObj`, the model functions (`mget`, `mdelete`, `mupdate`), `Refine`'s
  `refine_*`, the store's loops (`deleteOnce`, `updateOnce`, `conditionalDelete`,
  `GuaranteedUpdate`) and `stFrom_item`.

### 7b: Draft, review round 2 (2026-11-05; a fresh spec-reviewer on the driver's statements)

No statement found false of the Go code; the helper specs (`withPre`, `minRV`, `uidOf`, `preconditions`,
`cachedObj`, `cache.get`/`put`, `newCache`, `genFrom`, `Gen`), the Lean model against `mget`/`mdelete`/
`mupdate`/`preOk` and the store's answers (too-large minimum as `EOther`, `InvalidObj` at the prepared
key), and `call.spec`'s premises (dischargeable by `Apply`; D1 the only one the cached no-op needs)
checked sound. Findings and what was done:

- **F1 (high), done:** `cachedObjOk` at every key could not be proved: outside the store's prefix
  `versionAt` says no seen state has the key at that revision, and the store's contract says nothing
  of keys outside its prefix. Restated at the keys under `c.pfx` (all the store takes: `pathPrefix ++
  k`). The clause it needs, `oneKeyRevs c σ.rev` (each revision `1..σ.rev` recorded, at most one key
  under the prefix), is written out in `Cache.lean`; the Prove phase adds it to `kInvBody`, records
  revision `1 ↦ []` at the seed, and keeps it with `revSeen` (`inv_next` returns it again), by a pure
  lemma (a `KvNext` step whose `abs` changes one key changes one key under the prefix).
- **F2 (medium), for the Prove phase:** the continuations `Apply` hands the store (`create_au`,
  `rw_au`'s `contAt`, `getCall`'s committed state) carry no history fact out; each must also carry the
  answer's `cachedObjOk` (a write's from its `revSeen`, a no-op's and a `Get`'s from `kvSeen σ` and
  `oneKeyRevs`). Internal statements (`InvSteps`), not exported.
- **F3 (low), for the Prove phase:** `respIs_call`'s `tooLarge` branch follows from types once `eD`,
  `eU` are `sentV`s: state it at `sentV lD`, `sentV lU` (`Apply`'s).
- **F4/F5/F6 (low), notes:** `errIs`'s `EOther` arm excludes every `*StorageError` (the store returns
  none with another code); `InOk`'s parse conjunct is the store's `Get.spec` premise; `cacheInv`'s body
  is exported (an example, no API list).

### 7b: Freeze (2026-11-05, the user)

The Draft frozen as it stands at the tag `k8s-etcd3-7b-frozen` (local): every statement above, D1-D6
of the branch's `questions.md` approved as decided (D1 in the agent's form, not the narrower
alternative), N1 left as is (`notes/audit.md`). From here every change to a frozen statement is
logged below with its classification; one that touches a premise of an exported statement stops
for the user. Prove order: `oneKeyRevs` into the driver's invariant first; the history facts
through `create_au`, `rw_au`, `getCall`; D5's read update; then the store's loops, `call`/`Apply`,
`refine_*`, the model functions and the rest.

**Post-freeze changes** (statement, class, why):

- Prove (a), `oneKeyRevs` in the invariant (2026-11-05): `kInvBody` holds `histOwn c σ`
  (`histAuth c.γh σ ∗ oneKeyRevs c σ.rev`; `oneKeyRevs` moved from `Cache.lean` to `Inv.lean`);
  `inv_next` takes the step's one key (`∃ K, ...`, from `kStep_items`) and returns `revSeen`;
  `histAuth_seed` records etcd's first revision (`W64 1 ↦ []`) and returns `seedRevs`, which
  `kInv_seed` takes. Class: internal (the invariant and its lemmas; no exported statement, no
  premise of one). It held as planned: a step that changes the store's items at one key changes at
  most one key under the prefix (`chgOf_pfx_one`: a new key-value is at the new revision, which no
  item of the old state has; a deleted key had an item).
- Prove (b), the answer's cached object (2026-11-05): `dobjOf`, `cachedOf`, `cachedObjOk` moved
  from `Cache.lean` to `Inv.lean` (unchanged; `getCall` needs them), with `ansOk c y` (an object
  answer with a name is `cachedObjOk`); the continuations of `create_au`, `rw_au` and `getCall`
  (so `getCall_take`) carry `ansOk` of the model's answer. Class: internal (no exported statement;
  `call.spec`'s continuation is a parameter). The facts: `AnsFrom`/`kStep_ansFrom` (an answer with a
  name is an item of the state before or after, or a deleted key's), `versionAt_of_chg`,
  `cachedObj_of_item`, `cachedObj_of_del`, `ansOk_step`, `ansOk_read`; `Apply`'s four puts proved.
- Prove (c), D5 (2026-11-05): `readQ c γc n R σ` takes the read's minimum resource version `n`; the
  commit bit is promised only at `σ.rev = R` with `n ≤ σ.rev`, and `get_read_au` commits only
  then. Class: internal. `Apply` learns `n ≤ σ.rev` from the prophecy (not `EOther`, `kStep_min`);
  a `Get` whose prophecy says `EOther` answers `errOutL` (`kStep_err4`); `kStep_ans`'s `Get` case
  proved. `Apply` and `InvSteps` are `sorry`-free but `revRoom` (D30n, lean's).
- Prove (d), the store's loops and the rest (2026-11-05): no statement changed. `genFrom`, `call`'s
  `Delete`/`GuaranteedUpdate` branches, `respIs_call`'s too-large case, the new driver functions'
  bodies, `decodeObj`, `rvBytes`, the model functions, `refine_*`, `stFrom_item`, `deleteOnce`,
  `conditionalDelete`, `updateOnce` and `GuaranteedUpdate` proved. `GuaranteedUpdate`'s loop
  invariant is `conditionalDelete`'s with `rdOf` (a read's key-value, or the zero state with
  `ignoreNotFound`) and the size premises' consequence `szOk`; the cached no-op's re-read
  (`store.go:556`) is the first read, and when it returns the cached object's encoding its object
  is the cached one (`rd_data`), on which D1 makes the preconditions and `tryUpdate` answer as on the
  cached state: the model's no-op at the re-read's state (`rd_noop`), or, stale, the write from it.
  Helper lemmas: `rdOf`, `rd_current`, `update_cur_pre`/`update_cur_err`, `rd_hand_upd`,
  `stFrom_cached`, `stFrom_rdOf`, `preOk_rv_none` (`Steps.lean`); `stAt_cases`, `gu_answer`,
  `rd_noop`, `rd_data`, `rd_szOk` (private, in the proof file).

- `[C, check (the build after merging lean), touches the new specs' parameters (internal and driver), approved by the user, 2026-11-05]` Merge of
  `lean` (2026-11-05): lean's `2811fb73f8` (Q1 (c), the compactor registry) gave the driver's
  package init and every k8s etcd3 spec the instance parameter `[reg : EtcdGrove.k8s.CompactorRegistry]`;
  the 18 specs 7b added or restated in those directories (`rvBytes`, `rvString`, `Obj.GetUID`,
  `Obj.GetResourceVersion`, `uidOf`, `withPre`, `minRV`, `preOk`, `sameObj`, `preconditions`,
  `cachedObj`, `newCache`, `cache.get`, `cache.put`, `invalidObj`, `genFrom`, `Gen`,
  `store.getStateFromObject`) and their proofs get the same `variable` line. No other text changed.

- `[C, check (bounds), internal spec; same meaning, decided by etcd-grove-82, 2026-11-05]`
  `refreshOnError.spec`'s bound on the re-read's values written `etcdKeyMax` (was the literal
  `2 ^ 27`, which the bounds gate's `shared-limit` refuses in a spec), as `updateOnce.spec` does.

**7b done (2026-11-05).** Two post-freeze changes to frozen statements, the merge's follow-through
and the bound's name above (both C); otherwise the post-freeze changes above
are internal (the driver's invariant, `InvSteps`' continuations, D5's read update). Trust base of
`etc/tcb-collections/k8setcd3.txt`: before the stage (lean), 659 axioms and 3 `sorry`s (`client_ctx_field`, `revRoom`, `kvIs_ne_null`, none
7b's); after, 660 axioms (the approved extension T1, `fmt.SprintfNamed.wp_proof`, already in
`etc/tcb-baseline.txt`, now reached through `Preconditions.Check`), the same 3 `sorry`s (also
`k8s.txt`: + T1). `etc/tcb-baseline.txt` unchanged (785 axioms, 6 `sorry`s); `k8s_compactor_safe`
reaches no `sorry`.

### 7c: Scope (2026-11-05, branch `k8s-etcd3-7c`; approved by the user 2026-11-05)

**Approved (the user, 2026-11-05, via etcd-grove-82), every recommendation:** Q7c-1 (E1); Q7c-2, the
four restatements, each attacked by the `axiom` skill in the round that writes it; Q7c-3 (T2 (c) in
7c); Q7d (a); Q7e (a). Order (the coordinator's condition on the hub request): 7c-0, then 7c-1's
`GrpcSpec` change and mechanical migration as a separate early landing.

**What 7c proves.** `kubernetes.Client.Get` at any revision (`opts.Revision ≥ 0`). On success the
answer is the key at the state the response read. On error, the soundness of the two read errors
(the user's choice: *soundness only*; completeness later): an `ErrFutureRev` returned to the client
means the revision was above the state the read was served at; an `ErrCompacted` means it was below
that state's compaction revision. Both are stated by the error's description (`errDesc`, D29), so that
both of the store's tests (`errors.Is(err, etcdrpc.ErrFutureRev)` in `listReadError`,
`err == etcdrpc.ErrCompacted` in `interpretListError`) reduce to them. 7c has no consumer in the
driver yet: the first one is 7e's `getList` (its non-recursive branch calls `Client.Get` with
`options.Revision`, `store.go:1088`). So 7c ends with the client-layer statements proved, the
driver's traffic unchanged and `k8setcd3_safe`/`k8s_compactor_safe` still closed (their calls pass
revision 0).

**What exists.** The success side at a revision is already carried up to the client:
- `txn.rangeResult` (M2) answers `stateAt log (rangeRev rev o.rev)`;
- `rangeReplyOk` (the client's view of a reply) keeps it;
- `client_Get_kv` states it, `(σ.at (σ.readRev rev)).kvs`.

Only `kubernetes.Client.Get.spec`'s premise `opts.Revision' = 0` restricts it. The error side has
identity at one layer only. `txn.rangeResult` returns mvcc's `ErrFutureRev` exactly when
`rev < o.rev`, and `ErrCompacted` when `rangeRev < crev`. Every layer above drops this:
- `EtcdServer.Range`'s post: `applyErrIs` only;
- `togRPCError`: "non-nil";
- the Range handler's contract: nothing on error (`grpcHandlerOk`'s post is `err = nil -∗ …`);
- the gRPC attempt (`grpcInvokerOk`): "a client error … nothing about whether the handler ran";
- `kvErr` at the client.

**The design question: error identity across gRPC, per call.** The soundness is about the call's own
read (its revision against the state the read was served at, a state after the call began), so it
cannot be a member-wide fact like D29's `noRefusalAt`. A state the member had before the request
arrived says nothing. It has to travel with the call, from the handler's run to the attempt's error
post. That is a change to the gRPC specs' shape and to the gRPC trust boundary.

- **(E1) The gRPC specs get an error outcome (recommended).** Three changes:
  - A method's spec also states what its errors mean. Among the forms, the one with the least churn
    gives `GrpcSpec`'s continuation an error case, `Φ : Rep.M ⊕ GoString → IProp` (a description in
    the error case). Each spec says which descriptions it covers, `D`, empty for every method but
    `Range`.
  - The handler contract (`grpcHandlerOk(Md)`) gains on its error side
    `errDesc err ∈ D → Φ (.inr (errDesc err))`.
  - The attempt contract (`grpcInvokerOk`, inside the trusted `grpc.ClientConn.Invoke.spec`) gains
    the same, for descriptions grpc itself never produces. As D29's: a status the server sends is
    forwarded unchanged, and grpc's own errors carry grpc's messages; the two descriptions are
    etcd's own (`rpctypes/error.go:32-33`).

  Range's spec (`etcdRangeSpec`) then covers `D = {futureRevDesc, compactedDesc}`. Its caller's `Φ`
  at an error gets the read's facts: `readLogOk γr c log` (and the read update `□ Q (kvStateOf log)`
  for a linearizable read), with `o.rev > len log - 1`, or `rangeRev < crev`. These are the facts
  `rangeReplyOk` gives on success. Cost: every `GrpcSpec` definition is rewritten `Φ m` to
  `Φ (.inl m)` (about 160 sites in 84 files, mechanical), and every handler proof's last step gains
  a trivial error case (about 40 files; a lemma for `D = ∅`). This is shared vocabulary of the
  server, the client and the examples, so it is filed as a hub request too.
- (E2) A member-wide trust-boundary axiom, as D29's `noRefusalAt` ("a member sends `ErrFutureRev`
  only for a revision above its state"). Not sound as a per-call statement: rejected.
- (E3) No error identity: the driver's model (7e) treats `TooLargeResourceVersion`/410 on a list as
  a failed read. A weaker theorem and a deviation from `correctness.Model`, which rejects them for a
  valid revision. The fallback if E1's cost is refused.

**The statements touched (old → new)**, under E1. Each is written in full in Draft:

| Statement | Old | New |
| --- | --- | --- |
| `GrpcSpec`/`GrpcSpecMd` (`InvGrpc.lean`), `grpcHandlerOk(Md)`, `grpcMethodOk(Md)`, `isGrpcRpc(Md)` | continuation `Rep.M → IProp`; handler post `err = nil -∗ ∃ m', send ∗ Φ m'` | continuation over `Rep.M ⊕ GoString`; post adds `⌜err ≠ nil ∧ errDesc err ∈ D⌝ -∗ Φ (.inr (errDesc err))` |
| **trusted** `grpcInvokerOk` (in `grpc.ClientConn.Invoke.spec`) and `grpc.Server.Serve.spec`'s handler side | error: `clientErr`, `statusErrOk`, `errCellOk`, `noRefusal` | adds the handler's error outcome for `errDesc err ∈ D` |
| **trusted** `rpctypes` initializers (`ErrFutureRev_init`, `ErrCompacted_init`, the server-side `ErrGRPCFutureRev`/`ErrGRPCCompacted`) | an `EtcdError` / non-nil | adds `errDesc = "etcdserver: mvcc: required revision is a future revision"` / `"… has been compacted"` (as D29's refusals) |
| **trusted** v3rpc's `grpcErrMap` (`toGRPCErrorMap`'s package fact) | values non-nil | adds: mvcc's `ErrFutureRev`/`ErrCompacted` map to those two; no other key does; the default case's `err.Error()` is neither (the server's error messages, `applyErrIs`) |
| `v3rpc.togRPCError.spec` (proved) | non-nil | the mapped error's description for the two |
| `EtcdServer.Range.spec` (M2's, frozen) | error: `applyErrIs` | adds the two errors' conditions with the read's log facts (DRAFT batch: a frozen statement) |
| `kvServer.Range`, the served `etcd_rangeHandlerM` (stage 5), `etcdRangeSpec` | no error side | the error outcome |
| client: `kv.Get`/`Do`/`toErr` chain, `client_range_any`, `client_Get_kv`, `client_Get_st` | `kvErr err` | adds `rangeErrSound o Q err` (description → `∃ σ, □ Q σ ∗ ⌜σ.rev < o.rev⌝`, or `⌜o.rev < σ.compacted⌝`) |
| `kubernetes.Client.Get.spec` | premise `opts.Revision' = 0`; answer `findKey key σ.kvs`; error `kvErr` | no premise; answer `findKey key (σ.at (σ.readRev opts.Revision')).kvs`, the prophesied `m` its mod revision there; error adds `rangeErrSound` |
| callers of `Client.Get` (the store: `Get`, `getCurrentState`, `refreshOnError`, …; the compactor's `getCompactRev`) | – | re-proved at revision 0 (`σ.at σ.rev = σ`); the error pattern gains a field |

**Hubs.** `InvGrpc.lean` (`GrpcSpec`) is shared by the server, the client and every example: a hub
request to etcd-grove-82, whatever E1's form. None of the listed hubs (NewServer, bootOk, etcdstart,
the records) changes.

**Trust base.** No new axiom by count. Restated (a hard stop, each attacked by the `axiom` skill
before the Freeze):
- `grpc.ClientConn.Invoke.spec` (`grpcInvokerOk`);
- `grpc.Server.Serve.spec`'s handler contract;
- rpctypes' four initializers;
- v3rpc's `toGRPCErrorMap` fact.

The claim behind them is D29's (descriptions are forwarded, and grpc never makes etcd's), applied
to two more etcd strings.

**Related item, proposed into 7c.** "The client's errors are not `*apierrors.StatusError`s" (T2 (c)
of 7b, approved as a later change): `clientErr` strengthened. 7c rewrites the same error posts, and
7e needs it (`listReadError`'s `TooLargeResourceVersion` is a `*StatusError` the driver must tell
apart). Recommended in 7c if the gRPC boundary already fixes the error's dynamic type (to be checked
in Draft); otherwise its own step.

**Sub-steps (sizes are estimates, changed lines):**
- 7c-0, Go first: a Go test in the driver's module (in-process etcd). `Get` at a past revision
  returns the value then. A future revision gives `errors.Is(err, rpctypes.ErrFutureRev)`. A
  compacted one gives `err == rpctypes.ErrCompacted`. Both descriptions are what the trust statements
  say. ~100 lines of Go.
- 7c-1, Draft: the gRPC error outcome (definitions and the trusted statements) and the mechanical
  migration (~600, mostly one-line); the rpctypes/v3rpc facts (~80).
- 7c-2, Draft: the server's error side (`EtcdServer.Range`, `togRPCError`, `kvServer.Range`, the
  handler), statements and glue (~250).
- 7c-3, Draft: the client chain and `kubernetes.Client.Get`, statements, and the glue of its callers
  (~300).
- Then Review, Test (the tester on `Client.Get` at revisions), Probe (easy: `togRPCError`; hard:
  `EtcdServer.Range`'s error path firing the read update), Freeze (with the axiom attacks), Prove
  (~500).

In all ≈ 1,800 changed lines, ≈ 800 of them new proof.

**Found while scoping** (Draft records them in `nonissues/`, documentation only).
`kubernetes.Interface.List`'s doc says `Count` is "the total number of keys with the specified
prefix". The code counts from `opts.Continue` when it is set (`client.go:76`, `rangeStart`).

**Questions for the user (the Scope's batch):**
- **Q7c-1. Error identity across gRPC.** (E1) per-call error outcomes in the gRPC specs; (E3) no
  identity, the driver treats the two list errors as failed reads. Recommended: (E1).
- **Q7c-2. The trust statements restated as listed.** Recommended: yes.
- **Q7c-3. The `*StatusError` exclusion (7b's T2 (c)) in 7c.** Recommended: yes, if the boundary
  gives the dynamic type.
- **Q7d. The replay in the driver's `Check`.** (a) A Go copy of `correctness.Replay` (as D30m's copy
  of the Model). It would be trusted as a statement, with Go tests that compare it against the real
  `Replay` on random histories; 7g replaces it with the translation. (b) Translate the real
  `correctness` package now (7g first: `reflect.DeepEqual`, the object and list accessors at the
  trust boundary). Recommended: (a). (b) puts 7g's whole trust question in front of 7d, and the copy
  is checked against the real one by test.
- **Q7e. The shape of `kubernetes.Client.List`'s spec.** (a) As `Client.Get`'s:
  - the members' read update `Q R`, which knows the response's revision through a prophecy. This is
    a prophecy patch, `etc/proph-patches`, not a fork change; `Get`'s prophecy is in the fork from
    before the patches;
  - the answer at the state the read was served at: the keys of `[start, prefixEnd)` at the revision
    read, sorted, the first `limit` (`0`: all), where `start` is `opts.Continue` if set, else
    `prefix`;
  - `Count` the number of keys in that range;
  - `Revision` the state's revision;
  - errors as `Get`'s, with 7c's soundness.

  (b) No prophecy: the update fires at any state. The driver could not commit a list at the state
  its answer reflects, which is D30n's reason for `Get`'s. Recommended: (a). The spec follows the
  code's `Count`, not the doc's.

### 7c-1: Draft, the gRPC error outcome (2026-11-06; design decided by the agent, to the user via 82 with the landing)

**Form.** The error outcome goes into the metadata-indexed form only, the general one since the
auth plan's E3zb. The plain form is embedded in it, as for metadata. (The alternative, the
continuation over `Rep.M ⊕ GoString` the Scope sketched, would have changed every spec.)

- `GrpcSpecMd Req Rep := GrpcMd → Req.M → (Rep.M → IProp) → (GoString → IProp) → IProp`. The new
  last argument `Ψe` is the caller's error outcome, at the error's description (`errDesc`, D29's).
- `GrpcSpec Req Rep` is unchanged: a spec with no error outcome.
- `GrpcSpec.md S := fun _ m Φ Ψe => S m Φ ∗ □ (∀ d, Ψe d)`. A plain spec's caller gives every
  error's outcome; a caller that wants none passes `Ψe := fun _ => True`.
- **`handlerDescs`** (`InvGrpc.lean`): the descriptions of the errors a handler's spec may speak
  of, which no other step of a call (grpc's decoding, the server's interceptors, the transport)
  makes. The Md contracts (`grpcHandlerOkMd`, `grpcHandlerOwnOkMd`, `grpcMethodOkMd`) quantify
  over `Ψe`. Their error post gains `⌜err ≠ nil ∧ errDesc err ∈ handlerDescs⌝ -∗ Ψe (errDesc err)`.
  It is conditional because an error before the handler runs (`grpcDecOk`, `srvInterceptorsOk`,
  the quota check) has no `Ψe` to give; 7c-1b shows those descriptions are not in `handlerDescs`.
- The plain contracts keep their definitions. The laws `*_md` (`grpcHandlerOk h S Spec ⊣⊢
  grpcHandlerOkMd h S (GrpcSpec.md Spec)`, `grpcHandlerOwnOk_md`, `grpcMethodOk_md`,
  `isGrpcRpc(s)_md`) stay equivalences, now proved rather than `rfl`: left to right, the error gets
  `Ψe` from `□ ∀ d, Ψe d`; right to left, `Ψe := fun _ => True`.
- **The trusted attempt** (`grpcInvokerOk`, in `grpc.ClientConn.Invoke.spec`): `∀ Ψe`, the
  precondition `Spec md m Φ Ψe` at every attempt's metadata, and on an error
  `⌜errDesc err ∈ handlerDescs⌝ -∗ Ψe (errDesc err)`: such an error is the handler's own.

**7c-1a, the early landing (82's condition): mechanical.** `handlerDescs := []`, so every new
conjunct is vacuous, and every proof discharges it by `simp [handlerDescs]`. The trusted
statements (`grpc.ClientConn.Invoke.spec` through `grpcInvokerOk`; `grpc.Server.Serve` and
`RegisterService` through `GrpcMethod.spec : GrpcSpecMd`) change only by the quantifier `Ψe`,
which they pass through unused. The client asks for no outcome yet: `attemptPre` instantiates
`Ψe := fun _ => True`. The Md specs (`etcd*SpecM`, `etcd*SpecOn`, the auth service's) ignore their
`Ψe`.

**7c-1b** (the trusted statements, so that they are attacked once, at their final text):
- The rpctypes initializer axioms say what the two read errors' descriptions are (`futureRevDesc`,
  `compactedDesc`, cache/v3 `Base.lean`), for `ErrFutureRev`/`ErrCompacted` and
  `ErrGRPCFutureRev`/`ErrGRPCCompacted`, and the eleven other errors' literal descriptions (HS-1).
- The `toGRPCErrorMap` fact (`grpcErrMapOk`): non-nil values; mvcc's `ErrFutureRev` and
  `ErrCompacted` map to the two descriptions, and no other key does.
- The decoder's (`grpcDecOk`) and the interceptors' (`srvInterceptorOk`) errors are not in
  `handlerDescs`.
- HS-4 (DRAFT): the Md specs other than Range's take `□ ∀ d, Ψe d`.
- Each restated trusted statement is attacked with the axiom skill (Q7c-2), at `handlerDescs`'s
  7c-2 value.
**Gate (etcd-grove-82, 2026-11-06): 7c-2 does not fill `handlerDescs` before HS-5 is fixed** (`questions.md`, "7c-1b attacks"): with the descriptions in it, `grpcInvokerOk`'s claim that only a handler makes them, false in Go, would no longer be vacuous.
**For 7c-2/7c-3 (etcd-grove-82, 2026-11-06):** prometheus `StreamServerInterceptor`: the same
error-shape check as HS-6 (its `PostCall`'s `status.FromError` of the handler's error).
**7c: left (out of scope; etcd-grove-82, 2026-11-06):** grpc over etcd's HTTP mux (`ServeHTTP`):
unmodeled. `grpcDecOk` covers `Server.Serve`'s HTTP/2 transport only (the one `grpc.start` covers);
under `ServeHTTP` (etcd's TLS+HTTP on one port, `embed/serve.go:260, 314-324`), `mapRecvMsgError`
returns a raw `transport.ConnectionError`, not a leaf (`notes/axiom-review/hs6.md`). `Serve` is the
path of the insecure listener the examples use (through cmux); etcd's TLS path (`embed/serve.go`,
`grpcHandlerFunc`) goes through `ServeHTTP`, and that is how Kubernetes normally connects (82's
precision, 2026-11-06). Nothing is widened for it; also a gap of `/shared/tmp/k8s-server-trace.md` (row 15).
**Next stage after 7c (queued by the user, 2026-11-06; deferred by the user 2026-11-06, see "The
ServeHTTP stage: deferred" below): gRPC over etcd's HTTP mux.** Model
`grpc.Server.ServeHTTP` (the TLS path Kubernetes uses: `embed/serve.go`'s `grpcHandlerFunc`), starting
from the finding above: `mapRecvMsgError` (`handler_server.go:449,493-506`) returns a raw
`transport.ConnectionError`, not a leaf, so `grpcDecOk`'s error branch does not hold of that
transport as stated; the stage states the decoder's errors under `ServeHTTP` (or widens them, by
the attack), and carries the closed results to the TLS listener.
**Moved to 7c-2:** filling `handlerDescs`, and `etcdRangeSpecM`'s `Ψe` facts. Range's handler
proves `Ψe` at the two descriptions only from `EtcdServer.Range`'s error post (HS-3 (a)), which
is 7c-2's. Filled earlier, the Range handler's proof has nothing to prove it from.
**The attacks (2026-11-06).** The rpctypes and `toGRPCErrorMap` facts survive
(`notes/axiom-review/7c1b-init.md`, branch `axiom/7c1b-init` 7174bc28bd), and so does `grpcDecOk`.
Two claims fail in Go (`notes/axiom-review/7c1b-grpc.md`, branch `axiom/7c1b-grpc` 95e694f82a; Stuck
in Lean). First, `grpcInvokerOk`'s "only a handler makes these descriptions": a caller's context
whose `Err()` is `rpctypes.ErrCompacted`, or a per-RPC credentials error, carries `compactedDesc` with
no handler run. Second, already before 7c, a handler's error whose `Error()` panics makes
grpc-prometheus's interceptor and grpc's server panic, which `srvInterceptorOk` and `grpcMethodOk` do
not exclude. Both go to etcd-grove-82 as hard stops (`questions.md`, "7c-1b attacks").
7c-2 also needs `status.Error.spec` to state its description (`errDesc err = msg`).

**Why this form.**
- Most specs are plain (`GrpcSpec`) and do not change. Their handlers prove the plain contracts
  unchanged.
- Only the Md specs gain the argument (`fun md o Φ` becomes `fun md o Φ _`).
- The precedent is `GrpcSpec.md` itself: one family, the plain form embedded in it.

### k8s etcd3 over cluster3: Scope, revision 2 (2026-11-06, etcd-grove-56; revised for etcd-grove-82's independent check; approved by the user as recommended, Qc-1..Qc-5, 2026-11-06, via etcd-grove-82)

**Approved order:**
1. step 1 (no faults) lands alone;
2. then ServeHTTP, with its own Scope, since it changes a trusted statement;
3. then step 2.

The Freeze package of step 1 lists `seed.spec`/`seedOne.spec` old → new, with the closed-theorem comparison (`k8s_etcd3_safe`'s text unchanged).

**Changes from revision 1.** These answer etcd-grove-82's independent check (a workflow with 3
checkers and a critic, against lean 546dfc5378):
- The seeding is one-member, and the invariant is per member. Step 1 now has a cluster seed and a
  `kvSame` congruence. Its proof path is `k8s.New.spec`, not `isKv_of_newClient`.
- `kubernetes.New` at three endpoints has no proved precedent.
- `MaxUnaryRetries: 1` is dropped for the default retries.
- Step 2 gains keepalive, and possibly per-call timeouts.
- (M2) is restated. It is no longer called test-only.
- (M1)'s estimate is corrected, with the internal specs it changes.
- The trust count is 34, with the roots line.
- The 7e paragraph is corrected.
- Names are fixed.
- The Scope of revision 1 is otherwise unchanged. The model claim was confirmed: the driver's
  `Model` already keeps failed writes pending, and `k8s_etcd3_safe` covers them.

**Goal.** `k8s_etcd3_safe` runs the driver against one member. This stage runs the same driver,
traffic and model against a three-member cluster: first without faults, then under partition
schedules. It reuses the cluster start and failover that partition (`etcd_partition_safe`) and the
k8s compactor's `MainPartition` (K6, `k8s_compactor_partition_safe`) already proved.

#### What exists (surveyed on lean)

- **The cluster.** `examples/lib/cluster3`, in Go and Lean:
  - `StartCluster`, `NewClient`, `Partitioner` and the peer and client steps, with their proofs
    and `etc/gen-link.py --cluster3`;
  - the facts `clusterUp`/`memberAt`, `cfgOk`, `kvSame`, the `forwards` facts through the bridges,
    and `schedLit`;
  - the bridge's actions are axioms, already in the trust base, and are not proved.
- **The driver** (`examples/k8s/etcd3`):
  - `Main` starts one member and calls `kubernetes.New` with `Endpoints: {clientAddr}` and
    `MaxUnaryRetries: 1`.
  - It then seeds (`seed`/`seedOne`), runs `etcd3.New`, and calls `Check(s, st0, clients, ops, 0)`
    (`lintest.Run` against `Model`, which keeps failed writes pending).
  - `Main.lean` goes through `kubernetes.New.spec`, `seed.spec` and `k8s.New.spec`, whose
    `StoreCfg.ms` is the member list. It does not use `client.isKv_of_newClient`.
  - The invariants (`seedInv`, `kInv`) are per member (`γk`).
- **What is one-member today.**
  - `seed.spec` and `seedOne.spec` take `isNewClient cl [x.addr]`, `clientWriteOnce cl [x.addr]`
    and `kvRegsAt x` (`Spec/…/k8s/etcd3/seed.lean:38`, `seedOne.lean:42`).
  - K6 connected with `cluster3.NewClient`, not `kubernetes.New`. So `kubernetes.New` at three
    endpoints has no proved precedent. `clientCfgOk` at a three-element `eps` is cheap, because the
    bridges are `plainEndpoints`.
- **Retries.** `MaxUnaryRetries` is clientv3's whole attempt count, so `1` disables failover to the
  next endpoint. The proof's write-once rests on the members' `noRefusalAt` through `forwards`,
  which holds for any retry bound, not on `MaxUnaryRetries`. `etcdstart.NewClients`
  (`common.go:211-223`) uses the default retries, plus `DialTimeout` and `DialKeepAlive*`.
- **The model's cost.** The driver's `closure`/`addConfig` are txnlin's old linear-scan versions.
  c9's measurements (`notes/txnlin-perf-plan.md`) show the following:
  - The cost is the number of pending failed writes held at once. With k up to 7, the old model
    used 9-34 GiB and failed 2 of 5 TestFailover runs under 32G.
  - With (b) and routed writes, all 5 runs passed at under 0.5 GiB. The routing was a 4th client
    with a per-operation pick.

#### Step 1: no faults

**Go.** `MainCluster(clients, ops int)` in package `etcd3`, beside `Main`.
- `cluster3.StartCluster(cfg, lg)` with compaction off.
- `kubernetes.New` with `Endpoints` the three bridges, `DialTimeout`, `DialKeepAlive*`, and the
  default retries, as `etcdstart.NewClients` does. Not `MaxUnaryRetries: 1`.
- `seed`, then `etcd3.New`, then `Check(…, 0)`; panic on `Illegal`.
- The config literal is `clusterConfig()`, with its own token, names and nine addresses.
- Tests: `TestMainCluster` and `TestMemberIDs`. About 120 lines of Go and 80 of test.

**Statements.**
- `MainCluster.spec` (new): the shape of K6's `MainPartition.spec` without the schedule; post
  `True`.
- The closed theorem `k8s_etcd3_cluster_safe` (new, exported). It is `k8s_etcd3_safe`'s statement
  at `MainCluster #clients #ops`, with `etcd_partition_safe`'s hypotheses at `clusterCfg`:
  - the ids, `BootFacts`, the nine addresses, and the three WAL directories, distinct and absent;
  - `cluster3.premises`.
- **The seeding, generalized.** Recommended: generalize `seed.spec` and `seedOne.spec` from
  `[x.addr]`/`kvRegsAt x` to a member list `ms` with `kvRegsAt` for each member.
  - `Main` then instantiates them at `[x]`.
  - The alternative is a separate `seedCluster`, which duplicates about 200 lines.
  - These are internal specs of the example; no exported statement changes.
- **The invariant across members.** `kInv`/`seedInv` are stated at one member's `γk`. Step 1 adds
  a congruence over `kvSame`, in the style of `etcdKV_congr`: the invariant at one member's names
  holds at any member's whose KV is the same.
- **Nothing frozen changes.** `k8s_etcd3_safe` and the store, client and server specs stay as they
  are. `Model`, `Refine` and the invariants' definitions are reused.

**Trust base.** No new axiom or `sorry`.
- The `k8setcd3` collection gains about 34 cluster axioms already in the trust base: the bridge
  actions, the peers' HTTP, `probing` and the snapshot axioms. That is 31 without the
  `Partitioner`, which step 1 does not call.
- Its `roots` line is extended to cover the hand-written `MainLinked`, as `k8scompactor`'s is.
- The baseline is updated on purpose.

**Proof plan.**
1. `StartCluster` and `clusterUp` give three `memberAt … false` and `kvSame`.
2. `kubernetes.New.spec` at the three bridges gives `isNewClient cl eps`; `clientCfgOk` at a
   three-element `eps` comes from the bridges' `plainEndpoints`. `clientWriteOnce` and `kvRegsAt`
   for each member come through `forwards`, as in K6.
3. `seedInv` is allocated at one member, the generalized `seed.spec` runs at the three members, and
   the `kvSame` congruence carries the result.
4. `k8s.New.spec` takes `StoreCfg.ms` as the three members. `kInv_seed` comes through the
   congruence, then the rest follows as in `Main.lean`.
5. `clusterConfig`, the `MainLinked` written by hand, the Adequacy, and the Results with
   `#print axioms`.

**Estimates.**
- Go: about 200 lines.
- Lean: about 1100-1300 lines:
  - the seed generalization: about 150, with `Main.lean` re-instantiated;
  - the `kvSame` congruence: about 100-200;
  - `MainCluster`: about 500;
  - Adequacy, config and links: about 250.
- About 1.5 sessions. Builds cover the example's modules only; nothing hub-wide.

#### Step 2: faults

**Go.** `MainPartition(clients, ops int, sched []cluster3.Step)`: step 1 plus
`go cluster3.Partitioner(srvs, brs, sched)` before `Check`.
- **Calls must end under a blackhole.** Today `Apply` uses `context.Background()` and the config
  has no keepalive, so a call to a blackholed member hangs and `Check` never returns. The changes,
  in order:
  - (a) Keepalive (`DialKeepAliveTime`/`Timeout`, which `clientCfgOk` allows as `kaOpts`). This
    closes the dead transport, so the call fails with `Unavailable`. A read is then retried on the
    next endpoint; a write fails, and the model keeps it pending.
  - (b) Only if the tests still hang: a per-call deadline in `Apply`
    (`context.WithTimeout`). The store specs must then accept a deadline context. The 7c context
    facts (`ctxDeadlineLeaf`) cover its error; the Draft checks the rest. It changes `Apply`'s
    internal spec.
  - porcupine's `timeout = 0` in `Check` is kept in the theorem. A WP is partial correctness, so
    the theorem is about runs that return. The tests bound the run by the memory cap and
    wall-clock limits of the test harness.
- **Failed writes stay in the check.** The driver's `Model` already treats a write that returned an
  error as pending: it takes effect later or never. No model change in meaning.
- **The checker's memory.** Recommended: (M1) plus (M2'), with (M4) as the fallback and (M3)
  rejected.
  - **(M1)** Port txnlin-perf's (b) to the driver's model: a sorted, duplicate-free state and a
    binary-search `addConfig` over a total order on `mcfg`.
    - Size: txnlin's (b) is about 1330 Lean lines over 12-13 files. The k8s `Input` has 15 fields
      and a nested `Obj`, so expect 1000-1400 lines of Lean and about 300 of Go.
    - The abstract state stays a set, so `Model.spec` and every exported statement are unchanged.
    - It does change internal specs that revision 1 called reused: `addConfig.spec`, `closure`'s
      pure forms, and `Model.Equal`'s `isEqHash` proof.
  - **(M2')** Restated: the routing must be in the verified program. A test that meets the 5/5 bar
    with routing that the theorem's program lacks would not test the theorem. Two forms:
    - (i) Recommended first: clientv3's own balancer, with step (a)'s keepalive and the default
      retries, fails over away from a member whose transport closed. The routing is then inside
      the verified program already, and `MainPartition`/`Check` do not change. The memory runs
      measure whether this meets the bar.
    - (ii) If (i) does not meet the bar: explicit routing in the driver, c9's per-operation pick
      among per-member clients. This changes `Check` (one store and `apply` per client),
      `MainPartition` and their specs. It would be a Draft with its own statements, sent to the
      user before any Lean.
  - (M3) A cap on concurrent pending failed writes is rejected: it changes the traffic the theorem
    is about.
  - (M4) A compact representation is the fallback.
  - The bar: `TestMainPartition`'s schedules pass 5 of 5 runs under a 32G cap, with peak memory
    reported. These runs are of the theorem's program.
- Tests: `TestMainPartition`, covering peer cuts, the leader isolated, a client blackhole and
  drops. Each is run 5 times under `systemd-run -p MemoryMax=32G`.

**Statements.**
- `MainPartition.spec`: step 1's, plus `sched ↦*□ steps`.
- The closed theorem `k8s_etcd3_partition_safe`, for every schedule.
- (M1)'s changed internal specs, listed above.
- With (M2'-ii) only: `Check`'s and `MainPartition`'s new shape.
- Nothing frozen changes. With (b) only: `Apply`'s internal spec takes a deadline context.

**Trust base.** The collection's count of about 34 is now complete, because the `Partitioner` is
called. Its facts (`srvPeerCtl`, `ownBridge`) are proved already.

**Estimates.**
- Go: about 150 lines, plus (M1)'s 300.
- Lean: about 150-250 for the fork, Adequacy and Results, plus (M1)'s 1000-1400.
- (M2'-ii), if needed: about 400 more.
- About 2-3 sessions, most of it (M1) and the memory runs.

**Alternative:** fold step 1 into step 2. Recommended: keep step 1 as its own landing.

#### How 7d, 7e and 7f build on the cluster setup

Each of these stages is proved against one member first, then carried to `MainCluster` or
`MainPartition`. The store and client specs do not mention the member; the member list enters
only through `StoreCfg.ms` and the seeding.
- **7d (replay).** Independent of the cluster: the replay runs inside `Check` on porcupine's
  linearization.
- **7e (lists).** The k8s store's reads are linearizable (ReadIndex), so a lagging member does not
  serve a stale list. `ErrFutureRev` is reachable only through a requested revision ahead of the
  store, which one member already exercises. So 7e is proved on one member and carries over
  unchanged. The cluster adds only that a read may be retried on another endpoint, which the
  client specs already cover. The compacted case needs compaction on and a compactor in the
  driver: that is 7e's choice.
- **7f (watches).** A watch re-established on another member after a blackhole. It uses
  partition's `MainWatch` and compactorp's watch facts through the bridges. This is where the
  cluster setup pays most.

#### The order with the ServeHTTP stage

The user queued "gRPC over etcd's HTTP mux" (`ServeHTTP`) as the next stage after 7c. The two
stages are independent:
- `cluster3` serves gRPC with `gs.Serve` on its insecure client listener (`cluster3.go:123`), the
  path `grpcDecOk` covers.
- The ServeHTTP stage changes a trusted statement, about a TLS listener that no example uses yet.

Recommended order: cluster3 step 1, then ServeHTTP, then cluster3 step 2. Once both have landed, a
TLS cluster driver is a listener change.
(Superseded 2026-11-06: ServeHTTP is deferred, and cluster3 step 2 is next; see "The ServeHTTP
stage: deferred".)

#### Questions for the user

- **Qc-1.** Two steps: step 1 lands alone, then step 2. Recommended: yes.
- **Qc-2.** The checker's memory: (M1), plus (M2') with routing inside the verified program. Try
  (i), clientv3's own failover with keepalive, first; (ii), explicit routing with a `Check`/spec
  change, only if (i) misses the bar, as a separate Draft. (M4) is the fallback and (M3) is
  rejected. Recommended: yes.
- **Qc-3.** `MainCluster`/`MainPartition` in package `etcd3`, and `seed`/`seedOne` generalized to a
  member list rather than a separate cluster seed. Recommended: yes.
- **Qc-4.** Compaction off in both steps; the compacted list case is left to 7e. Recommended: yes.
- **Qc-5.** Order: cluster3 step 1, then ServeHTTP, then cluster3 step 2. Recommended: yes.

### The ServeHTTP stage: deferred (2026-11-06, the user via etcd-grove-82)

The Scope (etcd-grove-56, `/shared/tmp/k8s-servehttp-scope.md`, not committed) was reviewed by
82's read-only workflow (`/shared/tmp/k8s-servehttp-review.md`, wf_cd9419da-56c). **The user's
decision: defer the stage (option (c), nothing modeled now); cluster3 step 2 next. When it comes
back, it is (b), etcd's TLS listener, with the fixes below.**

**Why defer.**
- Option (a), unencrypted `ServeHTTP` (h2c), is a configuration etcd never runs, while the queued
  goal is the TLS listener (the queue entry above).
- grpc is names-only, and `embed` is untranslated. Under (a), `serverHandlerTransport`, `net/http`'s
  HTTP/2 server and the routing would all sit inside the new axioms. The result would add little
  beyond `Serve`'s, at the cost of 2-3 axioms.
- (a) does work in Go (`/shared/tmp/h2c-check`: grpc-go's client reaches `gs.ServeHTTP` over h2c,
  and HS-6's `ConnectionError` reproduces, 200/200). That changes neither point.

**What the review found (surviving).**
- **TLS is not only a layer below HTTP/2.** grpc's `serverHandlerTransport` builds the peer's
  `AuthInfo` from `r.TLS` (`handler_server.go:83-86`). Under `--client-cert-auth`, etcd's
  `AuthInfoFromCtx` takes the user from the certificate's CommonName (`v3_server.go:1206-1215`), and
  `accessController` branches on `req.TLS` (`serve.go:454-475`). So (b) adds client-certificate
  identity and those branches, not just crypto.
- **The error comes only from a unary call's second recv.** Only that recv returns the raw
  `ConnectionError` (`stream.go:1960-1970`). The first recv, every stream `RecvMsg` (Watch) and
  `SendMsg` go through `toRPCErr`, which gives a status leaf. So `streamErr` needs no change (the
  Scope's F3 is resolved).
- **The serve axiom must pin its receiver.** A `(*http.Server).Serve` axiom must hold `srv`'s
  points-to read-only: `Handler` the grpc server, every other field zero (`BaseContext`,
  `ConnContext` and the timeouts; `ReadTimeout = 0`), `Protocols` as the program sets it. A nil
  `BaseContext`/`ConnContext` result panics (`net/http/server.go:3563-3566, 3595-3598`). A hook's
  context would reach `grpcRunCtx` through `r.Context()` (grpc `server.go:1141-1152`).
- **The new axioms mint nothing.** No `threadTok`, run slots or `HttpNet` resources (as lease-ex's
  D1).
- **No inherited justification.** The start cannot rest on "`RegisterService` after `Serve` is
  fatal": `ServeHTTP` never sets `s.serve`. Only the consumed `grpcSrvNew` guarantees it.
- **Liveness facts change.** grpc's `MaxConcurrentStreams` and keepalive policy are inert under
  `ServeHTTP`; that affects liveness only. `InvGrpcServer.lean`'s "calls wait" header line would be
  false there.
- **One address, one `net/http` model.** The grpc-over-HTTP listener must exclude the address from
  `HttpNet` (`Proof/net/http/Boundary.lean:551-575`), so one address is never both.
- **Facts to correct.**
  - etcd's default client URL is `http://localhost:2379` (`embed/config.go:86`), so the secure path
    is not "the default".
  - `splitHTTP` is global: any HTTP-only URL makes every URL `onlyGRPC`.
  - `grpcHandlerFunc` is at `serve.go:314-327`.
  - In go1.27.3, `net/http`'s HTTP/2 server is `net/http/internal/http2`.
- **The name.** A result over h2c with `gs` as the bare handler should not be named as if it were
  etcd's secure grpc+http port.

**The design for when it comes back: the error shape at the method level** (decided by the user,
2026-11-06).
- Widen only `grpcDecOk`'s error branch and `grpcMethodOk`/`grpcMethodOkMd`'s post
  (`InvGrpc.lean:447`, `:485`, `:507`) to `srvErrOk err ∨ grpcConnErr err`. Place `grpcConnErr`
  where it has the fewest importers.
- `srvErrOk` stays unchanged. `dec`'s error never reaches an interceptor: the generated handler
  returns it before calling the interceptor (`rpc_grpc.pb.go:219-232`), and a unary RPC calls
  `sd.Handler` directly (grpc `server.go:1446-1450`).
- Widening `srvErrOk` instead would weaken the prometheus interceptor axiom, about 29 v3rpc specs
  and exported results (`etcd_kv_servedM_with`, v3rpc `Results.lean`'s `srvErrOk` posts), and
  rebuild about 6000 modules.
- The one consumer of `dec`'s error is `UnaryHandlerLemmas.lean:191-193`. So the only trust change
  is `grpc.serve`'s premise.
- **`grpcConnErr`'s inner error** is a leaf meeting `statusErrOk`, or `net/http`'s internal
  `StreamError`, a struct whose `Error()` returns and whose reflect-based `As` returns false for
  interface or non-struct targets (`net/http/internal/http2/errors.go:94-110`).
  - The `StreamError` case: `closeStream` closes the body with it on a peer RST_STREAM or a
    server-generated reset (`server.go:1566-1567, 1600-1601`). `mapRecvMsgError` tests against
    x/net's `StreamError`, so it wraps the internal one in a `ConnectionError`.
  - It reaches `dec` only through a race in `recvBufferReader`'s select. The race was seen in
    source only; 6000 runs never hit it.
  - The other inner error, `ReadTimeout > 0`'s `fmt.Errorf("%w", os.ErrDeadlineExceeded)`, is
    excluded by the serve axiom's `ReadTimeout = 0` premise.
  - Go probes for the attack: message 1, then RST_STREAM, looped; and a flow-control violation
    mid-body.
  - `notes/axiom-review/hs6.md`'s "true shape" is corrected accordingly.

**Qc-5 (the order) re-read.** Its rationale, that the ServeHTTP stage is a trusted statement about a
TLS listener and that a TLS cluster driver is then a listener change, no longer drives the order.
cluster3 step 2 goes next on its own merits (the user, 2026-11-06). A TLS cluster driver, if
wanted, comes with (b).

### k8s etcd3 over cluster3, step 1: as built (2026-11-06, etcd-grove-56, branch `k8s-cluster-s1`; Freeze package to the user via etcd-grove-82)

**Go.** `MainCluster`/`clusterConfig` in `k8setcd3.go`:
- token `k8setcd3c`, ports 24041-24063;
- `kubernetes.New` of the three bridges, with `etcdstart`'s dial and keepalive timeouts and the
  default retries.

`TestMainCluster` is Ok, and `TestMemberIDs` passes.

**Statements.**
- `MainCluster.spec` and `clusterConfig.spec` are new.
- The closed theorem `k8s_etcd3_cluster_safe` (`Results.lean`, from `k8s_etcd3_cluster_adequate`,
  over `etcd_adequate_members`) is new.
- `seed.spec`/`seedOne.spec` now take a member list `ms` (`ms ≠ []`, `[∗list]` of `kvRegsAt` and of
  `seedInv`). `Main` instantiates them at `[x]`.
- `k8s_etcd3_safe` and every store, client and server spec are unchanged.

**Proof.**
- The cluster side follows K6's `MainPartition`.
- `seedInv`/`kInv` read `γk` only through `etcdKV` (`γk.st`), so one invariant at the first member's
  names serves all three: `seedInvs_of_same`, `kInvs_of_same`.
- `MainLinked.lean` is written by hand. The `k8setcd3` collection's roots cover it, and 32 existing
  cluster axioms join the collection.
- No new axiom or `sorry`.

**Bounds.** `MainCluster.spec` takes the adequacy constants as instance binders
(`[ThreadBoundLe GF (2^28)] [ReceiptBoundLe GF (2^48)] [ReceiptBoundLe GF (N+1)]`), the B1 form of
`notes/bounds-plan.md`, as `examples/etcd/restart`'s `Main.spec`; `k8s_etcd3_cluster_adequate` builds
them with `haveI`. The bounds baseline does not move. (The Freeze package first raised it by 3, as
K6 did in `076cc37625`; the user, via etcd-grove-82, approved the Freeze on the condition that it
did not.) `Main.spec` keeps its premises.

**Noted, not fixed (2026-11-06, etcd-grove-82's review of the Freeze).**
- `MainCluster`'s Go doc comment says a write is retried only after a refusal. That misses
  clientv3's `isSafeRetryMutableRPC`, which also retries a mutable RPC on "no address/connection
  available". There the request never left the client, so a write still reaches the servers at
  most once and the proof's `clientWriteOnce` is unaffected; only the comment is incomplete.
- The seed's `Put` runs on `context.Background()`, with no deadline. While the cluster has no
  leader, it relies on the server's own request timeout to return.

The size came in under the estimate: `MainCluster.lean` is ~330 lines, and Adequacy, Results and
links ~200.

### k8s etcd3 over cluster3, step 2: as built (2026-11-07, etcd-grove-56, branch `k8s-cluster-s2`; Draft rev 2 approved with fixes by the user via etcd-grove-82)

**Go.** `MainPartition(clients, ops, sched)` in `k8setcd3.go` is `MainCluster` plus one step: before
`Check`, it runs `go cluster3.Partitioner(srvs, brs, sched)`.

Tests:
- Every cluster test runs in a process of its own (`inChild`: `TestMainLinearizable`,
  `TestMainCluster`, `TestMainPartition`, `TestPartitionFailures`). The parent removes the data
  directory after the child exits. Removing it under a running member made the WAL's release fail
  (`server.go:2157` panics), which the theorem excludes by its premise `storage.diskOk ∋ releaseOk`.
- `TestMainPartition` runs five schedules: `isolate` (300ms cuts), `election` (3s cuts of each
  member in turn), `blackhole` (member 0 for 10s), `drop` and `mixed` (one K6-like round).
- `TestPartitionFailures` counts the failed writes and the leader changes.

Runs, under a 32G cap:
- `TestMainPartition`, the theorem's program, returned Ok in 25 of 25 runs (5 schedules × 5 runs),
  with a peak RSS of 61-71 MiB.
- The leader and failed-write counts come from 25 separate runs of the diagnostic
  `TestPartitionFailures`:
  - the election schedule had 2-3 distinct leaders in every run;
  - 0-4 writes failed per run.
- `inChild` requires the child's `--- PASS` line, so a child that ran no test fails.

**Not verified.** An earlier doc comment on `MainPartition` said that a read is then retried on
another endpoint. Nothing verified that claim, and the comment no longer says it.

**Statements.** These are new; nothing on lean changes.
- `MainPartition.spec` is `MainCluster.spec` with `sched ↦*□ steps` added.
- `k8setcd3PProgram clients ops steps := initialize' #() ;; MainPartition #clients #ops (schedLit
  steps)`.
- `k8s_etcd3_partition_safe` (from `k8s_etcd3_partition_adequate`) holds for every `steps` with
  `steps.length < 2^63`, under `k8s_etcd3_cluster_safe`'s hypotheses. Its adequacy allocates the
  literal, as K6's does.

**Proof.** K6's partition pattern: the Partitioner is forked after `etcd3.New`.
- `PeerPausable` comes from `peerPausable_inst`.
- `ownBridge … false` comes from `cluster3.clusterAt`.

**Trust.** No new axiom or `sorry` in the baseline. The `k8setcd3` collection gains the three bridge
axioms `bridge.bridge.{Blackhole,Unblackhole,DropConnections}.wp_proof`. Like every `_safe` theorem
here:
- the result is vacuous until `pbEnc_ok`'s per-type fix lands (`notes/pbenc-ok-inconsistent.md`);
- it rests on false axioms until sweep repairs 1 land: `zap.Logger.{Debug,Error,Fatal,Info,Warn}`,
  `errors.IsCtxErr`, `context.ValueStartTime`, `http.Handle_ok`, and the k8s
  `DefaultFeatureGate`/`DefaultFeatureSupportChecker` initializers.

## What blocks where

**Error identity (`Range`'s errors).** Only the list and watch paths branch on which etcd error
came back: `store.listReadError` (`store.go:923`, `errors.Is(err, ErrFutureRev)` ->
`TooLargeResourceVersion`), `interpretListError` (`errors.go:66`, `err == ErrCompacted` -> 410,
by interface equality, so the client must return rpctypes' own value) and `interpretWatchError`
(the watcher). `Get`, `Create`, `Delete`, `GuaranteedUpdate`, `Stats` and
`GetCurrentResourceVersion` return etcd's errors unchanged, and `Get`'s
`TooLargeResourceVersion` comes from a local comparison (`validateMinimumResourceVersion`).
So phases 1-4 never wait on it; phase 5 does, in two strengths:
- *soundness* (`ErrFutureRev` returned only when the revision is above the current one,
  `ErrCompacted` only when below the compaction revision): without it a valid list may come back
  `TooLargeResourceVersion` or 410, which the Model rejects. Needed by the driver once its
  traffic has lists (25% of `TestCorrectness`'s).
- *completeness* (such a revision gives that error): needed only for the generic spec to say a
  future-revision list returns `TooLargeResourceVersion` (and a compacted one 410); the driver
  can treat any other error as a failed read.

A driver without list traffic (phase 6 first, then lists) does not need it at all.

**Translation (the survey).**
- G2, range over a function (**closed 2026-10-31**, stage 7a: Perennial `caa9d07ee`; `GetList`
  translated): `store.GetList` loops over an `iter.Seq2` (`store.go:825`) on
  every path, the ordinary `pagedChunks` included. Goose does not translate it, so phase 5 is
  blocked on it before error identity: Goose support (the general fix, a Perennial change), a
  Goose fork of k8s.io/apiserver rewriting the loop (as the etcd fork), or a trusted model.
- G1, field selection through a type alias (`clientv3.Event = mvccpb.Event`): blocks
  `parseEvent` and the compactor's watch loop, so the watcher, not phases 1-6 (with the compactor
  configured off, phase 0); a one-line Goose fix (`types.Unalias` in `getStructInfo`), tried on a
  scratch translator; needed before the watcher.
- G3, a type of a package the file does not import: worked around in configuration, except
  `storage.InvalidError.Error` (names-only), which nothing on the store's paths calls
  (`ParseResourceVersion` builds an `InvalidError` for a malformed resource version, but only
  its type is used); not blocking.
- `reflect` is on every unary path (`conversion.EnforcePtr`, `reflect.New(v.Type())` in `Delete`,
  `GuaranteedUpdate`; `MakeSlice`/`Append` in lists) and Perennial's `reflect` has no specs:
  phase 1 needs them, either as an independent Perennial change or as local trust-boundary specs.
- (2026-10-22) **`reflect.Value` in a variable rests on a `sorry`**: Perennial's generated typed
  points-to of the axiomatized `reflect.Value` is `sorry`, and `Delete` and `GuaranteedUpdate`
  pass `v := conversion.EnforcePtr(out)` through parameters (`conditionalDelete`, `deleteOnce`,
  `updateOnce`, `getCurrentState`, `stateFromEtcdResponse`). This blocks both, waiting on a
  choice (`notes/perennial-changes.md`): a Perennial change (an opaque `reflect.Value` with real
  instances and specs of `New`, `Value.Type`/`Addr`/`Interface`), a Goose fork of
  `k8s.io/apiserver` passing the store's `newFunc` instead (as the etcd fork), or trusted models of
  the functions that take a `reflect.Value`.
- No specs yet for `strconv`'s parse/format functions, `encoding/json`, `encoding/base64` and
  `path` (continue tokens, `prepareKey`), or for the names-only apimachinery functions the unary
  path calls (`meta.Accessor`, `runtime.Encode`, the error constructors; klog, metrics, tracing
  and feature gates as no-ops).

## From the etcd client proof (coordinate with its owner)

- **The client's errors are not `*apierrors.StatusError`s** (k8s etcd3 stage 7b, T2 (c), approved as
  a later change, 2026-11-05): `clientErr` (or `statusErrOk`/`errCellOk`) strengthened to exclude a
  `*StatusError`, so that the k8setcd3 driver's `errOut` can again tell the store's
  `NewTooLargeResourceVersionError` (`ETooLarge`) from a client failure and the model check a `Get`'s
  too-large answer exactly. Shared with `k8s_compactor_safe`.

1. `Range`'s error side: `ErrFutureRev` exactly when the revision is above the current one,
   `ErrCompacted` exactly when below the compaction revision (the compaction revision in the
   model), as rpctypes' own error values (`interpretListError` compares with `==`). Needed by
   phase 5, and by the driver once it lists: soundness first ("What blocks where").
2. `Txn`/`DeleteRange` errors: what the caller learns about whether its update fired (at most
   once already holds: `kvOpAu1`). Needed by phase 4's error cases.
3. (2026-10-22) `txn.kvIs l v` (a response's key-value, `server/v3/etcdserver/txn/Requests.lean`)
   should carry `⌜l ≠ null⌝`. The store branches on `getResp.KV == nil`, so
   `kubernetes.Client.Get`'s spec needs a found key's pointer non-nil. Its one `sorry` is
   exactly that. The fix: `txn.kvAt_persist'` takes it from the struct's typed points-to
   (`typedPointsto_not_null`), and the dozen destructuring sites gain a pattern. **Done
   2026-11-05** (branch `k8s-sorrys`): the fact is `kvIs`'s last conjunct; `kvIs_ne_null` proved.
4. For the watcher, later: `prevKV` (the watch contract fixes it false), compaction cancels,
   watches under any prefix (the contract's `V.pfx` is fixed).
5. (2026-10-22; partly landed 2026-10-23 as D37, `kvErr`/`errCellOk`: a client error is no
   caller's `errors.New` value of another message, `kvErr_ne`; **done 2026-10-26**, D37b:
   `clientErr_other` proved. The kubernetes client's and the store's error cases carry
   `errCellOk`, which now also says an `*errorString` error is a pointer (`errCellOk_ptr`); the
   sentinels' cells are in the driver's package fact (`errVarOk x msg`); not a `*StorageError` by
   `clientErr`'s leaf fact and the method-set premise `storageErrTyOk`, `*StorageError` has
   `Unwrap`.) **A client error is not the driver's sentinel.** The driver's
   `errOut` (as the correctness test) classifies by identity: `*storage.StorageError` of code
   NotFound/Exists, then `err == errDeleteRejected || err == errUpdateRejected`, else `EOther`
   (outcome unknown, the prophecy's `false`). The store returns the client's errors unchanged
   (`Client.Get`/`OptimisticPut`/`OptimisticDelete`: `err ≠ nil ∗ ⌜clientErr err⌝ ∗
   statusErrOk err`). `clientErr`'s leaf fact already rules out a `*StorageError` (it has
   `Unwrap`), but the sentinels are `errors.New` leaves too: nothing says `err` is not
   `interface.mkOk (*errors.errorString) #x` for the driver's cell `x`. Wanted: a persistent fact
   in the error postcondition (and `ctxErrClient`'s, for the caller's context errors; trivial for
   `context.Background()`) that tells it apart, e.g. D19k's message cells: an `*errorString`
   error at `x` has `errStrCell x m` for `m` among the client's `errors.New` messages
   (`"context canceled"`, ...), so `errStrCell_ne` separates it from the driver's
   `"k8setcd3: deletion rejected"`.
6. (2026-10-23) **The client's `ctx` field.** `etcd3.New` calls `c.Ctx()` (for the feature
   checker), which reads `clientv3.Client.ctx`; `isNewClient` (the client's `New` spec) does not
   give that field. `etcd3.New`'s spec takes `∃ cx, structFieldRef Client "ctx" cl ↦□ cx` as a
   premise for now; wanted: `New`'s postcondition (or `isNewClient`) includes it, read-only.
   **Done 2026-11-05** (branch `k8s-sorrys`): `isNewClient`'s last conjunct, `isNewClient_ctx`;
   `client_ctx_field` proved.

## Open

- **The real `correctness` package as the driver's checker** (D30m: for now a hand-written Go copy
  of `correctness.Model`, as close to it as possible). Later: translate a copy of
  `k8s.io/apiserver/pkg/storage/testing/correctness` (the Model, with D30g's fix), with trusted
  models for what it needs: `reflect.DeepEqual` (states and write responses, errors included),
  `runtime.Object` and `meta.Accessor`/`ListAccessor`, `map[string]runtime.Object`, the
  closures in its requests; then the driver theorem's trusted spec is the maintainers' Model.

- How `reflect` is specified (Perennial change or local specs); how G2 is resolved.
- Whether `correctness.Model` translates (it uses `reflect.DeepEqual` on objects); if not, the
  driver needs a translatable copy of its checks, which then becomes trusted.
- Which in-process etcd setup the driver starts from (linkv3p's three members, or one member
  first).
