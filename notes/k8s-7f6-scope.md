# k8s etcd3 stage 7f-6, the driver with watches: Scope (2026-11-16, branch `k8s-7f6`; to etcd-grove-02)

7f-6 is the driver stage of 7f (`notes/k8s-7f-scope.md` §5.4, §9): the driver's watch traffic and
check in Go, their proofs, and the closed TestCorrectness theorems with watches. It starts now, in
parallel with 7f-5, against `store.Watch.spec` as a hypothesis (the user, 2026-11-16, (a)), and its
cluster and partition theorems are for `k` members, `1 ≤ k ≤ 1000`, on the generic
`etcdstart.Members`/`StartMembers` start (the user, 2026-11-16, (b)). The driver's watch context is
`WithCancel(Background())` with a Done token the driver owns (decided by etcd-grove-81, 2026-11-14).

This Scope is a hard stop. The Go change is written and tested on this branch (§1, §8); no Lean is
edited and no translation regenerated.

## 1. The Go driver change (done on `k8s-7f6`, `examples/k8s/etcd3`)

| File | Change |
| --- | --- |
| `watch.go` (new, ~600 lines) | the prototype's (`notes/k8s-7f-proto.patch`), with three changes: the watch context (below), `consume` split out of `watchEvents`, and `reliableOk` aligned with `KWatch.lean`'s `reliableOkL` (no event or bookmark: true; the prototype also answered true on an empty range `hi = 0`, which `reliableOkL` does not; the two differed only at `Match = Exact ∧ req = 0`, which `genWatch` never makes) |
| `k8setcd3.go` | `KWatch = 5`; `step`'s `KWatch` branch (first: `watchOk(in, out, c)` keeps or drops `c`); the cache's watcher fields (`watch`, `unary`, `total`, `done`) and `newWCache`; `Gen` (a watcher draws `genWatch`, or a `Skip` watch once the unary operations are done); `Apply`'s `KWatch` branch (`runWatch`; the last non-error event's object becomes the cached object) and `done.Add(1)` after each unary call; `Check(…, clients, ops, watchers, wops, timeout)` through `lintest.RunLin2`; `newStore` (seed, `noStreaming`, `watchList`, `etcd3.New`, shared by the three entry points); `Main(clients, ops, watchers, wops)`; `startCluster(k)`; `MainCluster(k, clients, ops, watchers, wops)` and `MainPartition(k, clients, ops, watchers, wops, sched)` over it; `clusterConfig` deleted |
| `watch_test.go` (new) | the tests of §8 |
| `k8setcd3_test.go`, `errtypes_test.go`, `partition_count_test.go` | the new signatures; `partitionSchedules(k)` (the five schedules for `k` members); `TestMemberIDs` for every `k ≤ 1000`; `TestFindToken`, `TestAddrs` |
| `go.mod` | `third_party/bridge` direct (it was indirect) |

**What a watch is.** `genWatch` is the test's `randomWatchRequest` (the 7f Scope §1, §4.2's
departures of the traffic). `runWatch` runs one watch as one lintest operation of a watcher client:

```go
ctx, cancel := context.WithCancel(context.Background())
w, err := s.Watch(ctx, in.WKey, watchOptions(in))
if err != nil { cancel(); return nil, true }   // WFailed: constrains nothing
evs := consume(w, in)                           // read for watchDuration / maxEvents / until closed
w.Stop()
cancel()
```

**The `WithCancel` change.** The test's `WithTimeout(2s + HiccupDuration)` is replaced by the
driver's own `WithCancel(Background())`, cancelled once the driver has stopped reading. The
consumer's timer (`watchDuration`, 500 ms) bounds the watch, as the deadline did (it never fired
before the timer). So every recorded event was received while the watch was live: the driver holds
`kLive γ` (it has not called `Stop`) and the token that refutes its context's `PDone'`
(`wp_WithCancel_Background_of`'s; the cancel function needs `□ PDone'`, which the driver produces
only after the loop). That is where `k8sWatch` promises the gap-free prefix (`kStreamOk`; Draft
`notes/k8s-7f5a-draft.md` §2), not only the subsequence. `TestWatchCancel` checks the Go side: after
`watchEvents` returns, the context is cancelled and the watch's result channel closes (its goroutines
end), for every behaviour, under writes.

**What the check checks** (`watchOk`, `KWatch.lean`'s `watchOkL`, unchanged from the 7f Scope §4.2):
a failed or skipped watch constrains nothing; an output that does not decode, or a bad event,
rejects; Error events are dropped wherever they are; every revision is at most the configuration's;
bookmarks never go back and are at least the last event's, at most one initial-events-end bookmark;
a watch-list's events before its first bookmark are the initial events at that bookmark's revision
(at least the requested one), or, if it ended before the bookmark, a prefix of the initial events at
some revision from the requested one to the configuration's; the events then equal exactly the
changes in scope of the revisions they mark, clipped by the request (`watchRevisionRange`). The check
runs at the watch's linearization point, its end, against each configuration's history (7e's `hist`).

**How `k` members enter `Main*`.** `startCluster(k, lg)` is `txnlinfaultsN`'s start with one
kubernetes client in place of `k` etcd clients: `etcdstart.Members("k8setcd3N", k, 20000, 21000)`,
`etcdstart.StartMembers(ms, "k8setcd3N-6285", 1, 1, lg)`, then per member a `holdToken` goroutine,
`etcdstart.Serve` on its client address and `cluster3.StartBridge` at `127.0.0.1:(22000+i)`; then
`kubernetes.New` over the `k` bridges with `etcdstart`'s timeouts and keepalive (the 3-member
`MainCluster`'s client configuration). The token is the first `k8setcd3N-<i>` whose member ids' low
16 bits are distinct and non-zero for every `k ≤ 1000` (`TestFindToken`; `TestMemberIDs` checks it).
The ports are below Linux's ephemeral range and no other example's. `cluster3.Partitioner` runs the
schedule (steps name members by index; out-of-range ones do nothing). `k = 0` returns `Unknown`.
`Main` stays single-member (one attempt per call), with watchers.

## 2. The closed theorems: planned statements

**Which change.** All three k8s etcd3 theorems change program and statement; no new theorem is
added beside them (Q1):

| Today | After 7f-6 |
| --- | --- |
| `k8s_etcd3_safe` (`Main(clients, ops)`) | same name, `Main(clients, ops, watchers, wops)` |
| `k8s_etcd3_cluster_safe` (3 members, `cluster3.StartCluster`) | same name, `MainCluster(k, clients, ops, watchers, wops)`, `1 ≤ k ≤ 1000` |
| `k8s_etcd3_partition_safe` (3 members) | same name, `MainPartition(k, clients, ops, watchers, wops, sched)`, `1 ≤ k ≤ 1000` |

(and their `k8setcd3_Main*` spec results, `Adequacy`'s `_adequate`, `MainLinked`).

**Sketch** (the partition one; the cluster one drops `steps`, `Main`'s keeps its one-member
premises and gains the watcher premises and `Hcec`):

```lean
theorem k8s_etcd3_partition_safe [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : …k8s.etcd3.Assumptions] [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    [k8s_io.apiserver.pkg.storage.etcd3.Assumptions] [k8s_io.apimachinery.pkg.runtime.Assumptions]
    [k8s_io.apimachinery.pkg.runtime.schema.Assumptions] [k8s_io.apiserver.pkg.storage.Assumptions]
    [k8s_io.apiserver.pkg.storage.value.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] [log.NewModel]
    (Hctx : ∀ hG, ContextReadErrs (GF := k8setcd3GF) (hG := k8setcd3HeapAt hG lctx))
    (Hcec : ∀ hG, ContextErrsClient (GF := k8setcd3GF) (hG := k8setcd3HeapAt hG lctx))  -- NEW
    (k : Nat) (hk1 : 1 ≤ k) (hk : k ≤ 1000)                                              -- NEW
    (ids ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (Hlen : ids.length = k) (Hbf : k8s_etcd3N.BootFacts ids ps ctxs boot)                 -- was cluster3.BootFacts id₁ id₂ id₃
    (Haf : authRecordsFit) (Hbuq : apply.backendUnderQuota) (Hrf : grpcRepliesFit) (Hdbo : storage.diskOk)
    (clients ops watchers wops : w64)                                                     -- watchers, wops NEW
    (Hc0 : 0 ≤ sint.Z clients) (Hw0 : 0 ≤ sint.Z watchers)
    (Hc31 : sint.Z clients + sint.Z watchers < 2 ^ 31)                                    -- was clients < 2^31
    (Hops : 0 ≤ sint.Z ops) (Hwops : 0 ≤ sint.Z wops)
    (Hmul : sint.Z clients * sint.Z ops + sint.Z watchers * sint.Z wops < 2 ^ 60)        -- RunLin2's
    (steps : List cluster3.Step) (Hsteps : steps.length < 2 ^ 63)
    (HNs : prometheus.namesUnclaimed (k8setcd3PProgram k clients ops watchers wops steps) k8setcd3Names)
    (HAs : addrsUnclaimed (…) (k8s_etcd3N.addrs k))        -- the 3k peer, client and bridge addresses
    (HDs : dataDirsAbsent (…) (k8s_etcd3N.dirs k))          -- the k members' data directories
    (HEnv : verifyEnvOff (…)) (n : Nat)
    (Hprem : ∀ hG, ⊢ k8s_etcd3N.premises (GF := k8setcd3GF) (hG := …) k n ids ps ctxs boot)  -- putgetN's, at these members
    (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ) (Hthreads : σ.threads = 1)
    (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps' : RealNsteps n ([k8setcd3PProgram k clients ops watchers wops steps], (σ, g)) κs (t2, σ2))
    (Hn : n + 2 ≤ 2 ^ 28) :
    (∀ v t2', t2 = Val v :: t2' → v = #(go!"Ok") ∨ v = #(go!"Unknown")) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧ (∀ v, Val v ∈ t2 → v.isPanic = false)
```

**In plain English.** For every member count `1 ≤ k ≤ 1000`, every partition schedule, and any
numbers of unary clients and watchers (their operation counts within lintest's bounds), every real
execution of the program (start `k` etcd members with bridges, one kubernetes client over the bridges,
the etcd3 store, `clients` concurrent clients doing the store's unary operations and lists, and
`watchers` concurrent watchers each running up to `wops` watches, while the partitioner cuts and
mends links) never panics, never gets stuck, and ends with `Ok` or `Unknown`. Since the program
panics when porcupine answers `Illegal`, porcupine never finds the history illegal.

**What is new in the guarantee: the watch events.** Porcupine's history now holds every watch, and
it accepts only if one linearization, with one choice of when the failed writes took effect, explains
the unary answers **and** every watch's events: each watch saw, with Error events removed, a gap-free,
duplicate-free, correctly filtered (scope, field and label selectors) window of that configuration's
revision history (Added/Modified/Deleted by the predicate on the new and the old object), starting
at the requested revision when one was given, with bookmarks never going back and never beyond the
store's revision; and a watch-list's initial events were exactly the matching objects at the
initial-events-end bookmark's revision (at least the requested one), or a prefix of them at some
revision if it ended before the bookmark. The departures from upstream's validator are the 7f Scope
§4.2's 1-4 (accepted by the user 2026-11-08), stated in `watchOk`'s docstring; what no check sees
(a dropped last event, a dropped first event of an unpinned window) is as upstream's.

**Every new premise:**
- `k`, `1 ≤ k ≤ 1000`, `ids.length = k`, the `k`-member `BootFacts`/`premises`/addresses/data
  directories: the user's decision (b), the forms putgetN/txnlinfaultsN already use (no new kind);
- `watchers`, `wops` and the bounds `clients + watchers < 2^31`, `clients·ops + watchers·wops < 2^60`:
  `RunLin2.spec`'s (7f-1);
- `Hcec : ContextErrsClient` (the context errors `Canceled`/`DeadlineExceeded` are client errors):
  `store.Watch.spec`'s `ctxErrClient` of the driver's `WithCancel(Background())` context needs it. It
  is already a premise of `k8s_compactor_safe` and of every etcd example with a context (Q4);
- nothing new in the trust base from 7f-6 itself. The checker text (`watchOk` and helpers, `genWatch`'s
  traffic) is statement-level text in the sense of D30m (it says what porcupine checks), as `Model` is.
  The trust items 7f-5 adds (T5-a…T5-f, E1, T-CE, and whatever steps 6-7 add) reach these theorems
  through `store.Watch`'s link and are 7f-5's to report.

**What stays.** `k8s_compactor_*`, the etcd theorems and every other closed theorem: untouched.

## 3. How `store.Watch.spec` enters, and how it is discharged

- **Now.** The statement is `Draft.store.Watch.spec` in
  `Proof/k8s_io/apiserver/pkg/storage/etcd3/Draft7f5a.lean` (7f-5's, still moving: steps 6-7).
  Recommended (Q3): 7f-5 moves the statement into `Spec/k8s_io/apiserver/pkg/storage/etcd3/store__Watch.lean`
  as `def store.Watch.spec : Prop` with no proof file (no `sorry`, no axiom), and from then on changes
  it only through the ledger (`notes/specs-only/ledger.md`), with 7f-6 told.
- **In 7f-6.** Every 7f-6 proof that reaches a watch takes it as a callee hypothesis, the repository's
  normal form: `theorem watchEvents.wp_proof (wp_sWatch : store.Watch.spec) (…) : watchEvents.spec`, and
  so on up through `runWatch`, `Apply`, `Check`, `Main*`. These proofs are complete (no `sorry`) but
  **unlinked**: `etc/gen-link.py` cannot produce `wp_Main*` until `store.Watch` has a `wp_proof`. So
  the closed theorems and the k8s `Link`/`MainLinked`/`Results` are not regenerated before then (§5's
  stage F).
- **Discharge.** 7f-5a step 7 lands `store__Watch.wp_proof` (over `concurrentDecodeOff`, Q6's
  temporary premise) and its link; 7f-5b removes `concurrentDecodeOff`. Then 7f-6's stage F adds the
  `store_Watch` entry to the k8s link list (`etc/link-lean-first-*.txt` or the k8s etcd3 `Link`'s
  generator), regenerates `Link`/`MainLinked`, and the closed theorems follow with no hypothesis left.
  Before 7f-5b, a closed theorem could only be linked with the driver setting
  `ConcurrentWatchObjectDecode=false` (Q5).

## 4. Dependencies and their state (lean `e9f67cdb20`)

| Dependency | State | Evidence |
| --- | --- | --- |
| 7f-1 `lintest.RunLin2` (spec, proof, `RunLin` through it) | **landed** | `Spec/.../lib/lintest/RunLin2.lean`, `lintest/Link.lean`'s `wp_RunLin2` |
| 7f-2 pure watch check, `watchOkL_of_stream` | **landed** | `Proof/.../examples/k8s/etcd3/KWatch.lean`, `KWatchStream.lean` (premises `StreamOkL`, `WatchInOk`, `HistWf`) |
| **7e-4's kInv history fact** (`hist[R] = absK (stateAt R)`) | **landed** | `RefineList.lean:231` `KRelH` (its third conjunct: `KRelS (σ.at r) r (histAtL h.hist r)` for `1 ≤ r ≤ σ.rev`); `Inv.lean:448` (the configuration's `KRelH` and `hist.length = σ.rev`); `shistOwn`'s `oneKeyRevs` (one key per revision) |
| T5-c `featureOn WatchList`, the driver's `Set("WatchList=true")` | **landed** | `ListDefs.lean:159` `watchListOn`; `watchList()` in every `Main*` |
| 7f-5a steps 1-5 | **landed** | the 7f-5 handoff |
| 7f-5a T-CE (`clientWatchCE` closed) | **on `k8s-7f5`, at its land stop** | `/shared/etcd-grove-k8s7f/notes/k8s-7f5-handoff.md` |
| 7f-5a step 6 (`Pos.Countable KRaw`, `sendEvent`), step 7 (link `startWatching`, `syncPaginated`, the watch; T5-f axioms) | **not started** | same; step 7 is what stage F needs |
| 7f-5b (concurrent decode; removes `concurrentDecodeOff`) | **not started** | before 7f-6's Freeze (Q7f-3, Q5 below) |
| Adequacy's thread bound | **no new need expected** | the Draft's §2: the watch's goroutines get their tokens at their `go` statements and `store.Watch.spec` takes no `threadTok`; it keeps `threadBound GF ≤ 2^30 - 1`, which `Apply.spec` already carries (GetList). Stage B landed. 7f-6 checks it at stage E. |
| `ContextErrsClient` producer | **exists** (a class premise, as the compactor's) | `Proof/go_etcd_io/etcd/client/v3/ErrorsNewOk.lean:75` |
| putgetN/txnlinfaultsN's generic `k`-member start in Lean | **landed** | `Proof/.../etcd/putgetN/Defs.lean` (`BootFacts`, `premises`), `txnlinfaultsN/startCluster.lean` (590 lines) |

## 5. Stages, with Lean-line estimates

Each stage lands on its own once the coordinator says go; A and B need nothing from 7f-5.

| Stage | Contents | Lean lines | Needs |
| --- | --- | --- | --- |
| **A. `k` members** (no watches) | Go: `startCluster(k)`, `newStore`, `MainCluster(k, …)`, `MainPartition(k, …)` (watchers not yet); the translation; Lean: `startCluster.wp_proof` (txnlinfaultsN's, with `kubernetes.New` over the `k` bridges in place of `k` `NewClients`), `MainCluster`/`MainPartition` over it, the `k8s_etcd3N` Defs (`BootFacts`, `premises`, addresses, directories: putgetN's at these names), adequacy, Results; `k8s_etcd3_cluster_safe`/`_partition_safe` restated for `k` (a closed-statement change: a stop) | 1200-2000 | nothing (Q2) |
| **B. The check in Go = the pure check** | the translation of `watch.go`'s pure part; one spec and proof per function, each equal to its `KWatch.lean` function: `encodeWEvents`, `decodeWEvents`, `changeAt`, `toEvent`, `initialEvents`, `eventsEqual`, `bookmarksOk`, `reliableOk`, `initialPrefixOk`, `watchOk`, `lastObj`, `toWEvent`, `watchOptions`, `genWatchFrom`/`genWatch` (with `WatchInOk` of every draw); `step`'s `KWatch` branch and `stepL`'s (the model's step; `Gen` never draws a watch yet, so `kInOk` excludes it and the closed theorems do not move) | 1500-2300 | nothing |
| **C. The bridge (Draft D1)** | pure: `kStreamOk` (the store's, over `KVState` and `DObj`) to `StreamOkL` (the driver's, over `HSt` and `Obj`) under `KRelH` and `oneKeyRevs`: `kEvOfL` ↔ `evAtL`, `kInitialL` ↔ `initialEventsL`, `kScopeOf` ↔ `keyInScopeL`, the selectors, `KTail`'s bookmarks (stronger) ↔ `TailOk.bm`, `kStartOk` ↔ the start points, `toWEvent` of `wevAt`; `HistWf` of the model's histories | 700-1200 | `store.Watch.spec`'s vocabulary frozen (Q3) |
| **D. The watch run** | `consume` (the `select` loop on the timer, `time.After` and `ResultChan`), `watchEvents` (`WithCancel(Background())`, the driver's Done token, `Stop`, `cancel`), `runWatch` (the hiccup sleep): over `store.Watch.spec` (hypothesis); post: `WFailed`, or the encoded events with `□ kStreamOk` at a firing of the read update `Q` | 600-1000 | Q3 |
| **E. The wiring** | the cache's watcher fields (`done` under the cache's invariant: `done ≤ total`; `etc/bounds-check.py` per the bounds plan), `Gen`, `Apply`'s `KWatch` branch (logically atomic, linearized at the watch's end: from `□ Q lb σ` and the instance's invariant at that point, `KRelH` of the matching configuration, then `watchOkL_of_stream`), the read-update producer `Q` from the history ghost (Draft D3), `kInOk` for watches, `Check` through `RunLin2`, `Main*` with `watchers, wops`; unlinked (over `store.Watch.spec`) | 1200-2000 | B, C, D |
| **F. Link and closed theorems** | `Link`/`MainLinked` with `store_Watch`; the three theorems restated (watchers, `Hcec`); Results with `#print axioms`; interfaces, tcb collection, STATUS | 200-400 | 7f-5a step 7 landed; **Freeze after 7f-5b** |
| total | | **5400-8900** | |

The 7f Scope's estimate for 7f-6 was 2000-3000. The difference: the `k`-member theorems (A, the
user's 2026-11-16 decision), the bridge C (Draft D1, decided 2026-11-14, after that estimate), and B
priced as one spec per Go function (the prototype's translation was 3876 generated lines).

**Landing order.** The Go change lands in pieces with its translation, since `etc/goose.py --check`
gates every landing and a changed `Gen`/`Apply`/`Check`/`Main*` breaks the linked proofs until E and
F are done: A's Go with A; `watch.go`'s pure functions and `step`'s branch with B; `consume`,
`watchEvents`, `runWatch` with D (new functions, called by nothing linked yet); the rest
(`Gen`/`Apply`/`Check`/`Main*` with watchers, the cache) with E+F together, or E on the branch until F
can land. This branch keeps the whole Go change as the target and the test bed.

## 6. Risks

- **The Done token through `WithCancel(Background())`.** `wp_WithCancel_Background_of` gives
  `isContext` with `PDone := PDone'` and a cancel that needs `□ PDone'`; `store.Watch.spec` also wants
  `outgoingCtxOkC`, `ctxErrClient` (`Hcec`) and `k8sCtxOk` of it. The producers exist for
  `Background()`-derived contexts (`metadata.outgoingCtxOkC_from`, `k8sctx.k8sCtxOk_bgFrom`,
  `ctxValueFrom`); D checks them first. If one is missing it is a local lemma, not trusted text.
- **`consume`'s loop**: three `select`s on timers (`time.NewTimer`, `time.After`, `timer.Stop`).
  Perennial's `time` specs must allow them with no bound on how often they fire; the prototype's Goose
  dry run translated them, elaboration was never tried.
- **The linearization point of a watch** is its end, but the facts are about states the read update
  fired at during the watch. E needs every such state to be a prefix of the state at the end
  (`kvSameHist` and the history ghost's monotonicity) so that `KRelH` at the end covers them.
- **The bridge C** is the largest unknown: the store's `KTail` bookmark condition is stronger than
  `TailOk`'s (fine), but `kEvOfL`'s previous object is `kPrevAt` (the record at the revision before)
  and `evAtL`'s is `changeAtL`'s merge of two stores; their agreement needs `oneKeyRevs`. The
  model's items carry the canonical bit and `changeAt` compares whole items; a no-op rewrite of a
  non-canonical item (D30g) also moves the object's resource version, so it is a change of the object
  too, which the store delivers as Modified: C must show the two agree there.
- **Porcupine's cost** with watches: each watch step runs `watchOk` per configuration. The runs of §8
  are fast at these sizes; the theorem is not about time.
- **7f-5's spec moving** after 7f-6 relies on it (Q3); and 7f-5b's `WaitGroup` risk, which delays F.
- **The Goose configuration**: `k8setcd3.go` now imports `strconv`, `etcdserver` and
  `third_party/bridge` (for `startCluster`), and `watch.go` `k8s.io/apimachinery/pkg/watch` and
  `metav1.Status`; the `k8s-apiserver` project's `Code/**/*.toml` gains what is missing (the 7f
  prototype's dry run translated `watch.go`; `startCluster`'s imports are txnlinfaultsN's).
- **Translation drift**: the Go on this branch must be re-checked against lean's when each piece
  lands (7f-5 may change the driver's codec or features).

## 7. Open questions, each with a recommendation

- **Q1. Replace the 3-member cluster and partition theorems by `k`-member ones, or add `N` versions
  beside them?** Recommended: **replace** (same names). `k = 3` is an instance (with `BootFacts`
  in putgetN's list form); keeping both would keep two starts and two proofs of every `Main*`. The
  Go on this branch replaces them.
- **Q2. Land the `k`-member change first, without watches (stage A), changing the closed statements
  twice?** Recommended: **yes**. It needs nothing from 7f-5, is ready now, and is reviewable alone;
  the watchers then add premises to statements already in their final shape. The alternative (both
  at F) saves one review but holds 1200-2000 lines on a branch for weeks.
- **Q3. Freeze `store.Watch.spec`'s statement in `Spec/` now** (moved out of `Draft7f5a.lean` by
  7f-5, no proof file, changes through the ledger)? Recommended: **yes**, before stage C starts.
- **Q4. `ContextErrsClient` (`Hcec`) as a new premise of the three k8s theorems?** Recommended:
  **accept**: `store.Watch.spec`'s `ctxErrClient` of a cancellable context needs exactly it, and it is
  the same class premise the k8s compactor and the etcd watch theorems carry.
- **Q5. `ConcurrentWatchObjectDecode`**: the driver does not set it (on by default at the pinned
  binary version), so F's Freeze needs 7f-5b (Q7f-3 stands). Alternative: the driver sets it off and
  the theorems cover the serial branch only, which takes 7f-5b off 7f-6's path. Recommended: **keep
  Q7f-3** (no `Set`; Freeze after 7f-5b); the tests run both values (§8).
- **Q6. The `k`-member start's names** (forms, decided unless the coordinator objects): member
  names `k8setcd3N-i`, ports `20000+i`/`21000+i`/`22000+i`, token `k8setcd3N-6285`.

## 8. The Go tests (all under `systemd-run --scope -q -p MemoryMax=32G`, `GOWORK=off`, go1.27.3)

See the handoff for the exact commands. Results are filled in below.

| Test | What | Result |
| --- | --- | --- |
| `TestWatchOkEdges` | `watchOk` on hand-made histories: 17 cases (full window, dropped middle/first event, bookmarks at and past the configuration, bad event, Error between events, pinned windows, watch-lists: initial events at the bookmark, stale initial events, ended before the bookmark, unannotated bookmark, gap), failed/skipped/undecodable outputs, the encoding's round trip | pass |
| `TestGenWatchCases` | 20000 draws of `genWatchFrom`: every request satisfies `KWatchStream.lean`'s `WatchInOk` (the 7f-2 premise), and every case of the generator is reached (3 `SendInitialEvents` modes, 6 RV kinds, 4 behaviours, 3 scopes, 6 field selectors, app selector, recursive, bookmarks, missing namespace/object) | pass |
| `TestWatchCancel` | the `WithCancel` change: 24 watches (6 per behaviour) under concurrent writes; after `watchEvents` returns, the context is cancelled and the result channel closes within 5 s; no watch takes longer than `watchDuration + HiccupDuration + 0.5 s` | pass (10.9 s) |
| `TestMainWatch` (mode counts, one member, 8 × 300 unary, 16 × 8 watches) | requires every behaviour, every `SendInitialEvents` mode, every scope, watches with events, pinned windows with events, watch-lists with events and their bookmark, Added/Modified/Deleted/Bookmark events; no bad event (skipped watches are logged, not required: under load the watchers can finish before the unary traffic; one whole-package run had none) | pass: 41 watches, 25 with events, 14 watch-lists with their bookmark, 623/412/615 Added/Modified/Deleted, 9.6 s, 130 MB |
| `TestWatchCorrupt` | one watch corrupted per run: `value`, `rv`, `type`, `dup`, `drop` (a middle event) → `Illegal`; `none` → `Ok` | 6 of 6 |
| `TestMemberIDs`, `TestAddrs` | the token's ids for every `k ≤ 1000`; the addresses | pass |
| **Repeated runs, default decode (concurrent)**: `watchruns.sh 10 "1 3 5"` | `MainCluster`'s setup and `MainPartition`'s with six schedules (`isolate`, `election`, `blackhole`, `drop`, `mixed`, `noleader`; `noleader` not at `k = 1`), 4 × 120 unary, 8 × 12 watches, 10 rounds × `k ∈ {1, 3, 5}` | **200 of 200 `Ok`**, peak RSS ≤ 293 MB, 2-20 s each |
| **Repeated runs, serial decode** (`K8SETCD3_DECODE=serial`): `watchruns.sh 3 "1 3"` | the same, `ConcurrentWatchObjectDecode` off (logged in each run) | **39 of 39 `Ok`** |
| Whole package (`go test .`) | every test, including the 3-member diagnostics (`TestClientErrorTypes`, `TestPartitionFailures`) over `startCluster(3)` | pass (394 s; a first run failed only on the then-required "skipped watches" count in `TestMainWatch`, a timing effect under load, now logged instead) |

**What the 200 default-decode runs reached** (sums over 10 rounds):
- watches: 140-960 per (`k`, schedule); failed `Watch` calls only under `election` (8) and `noleader`
  (58); Error events in 190 watches (`election` 52, `noleader` 138); no bad event anywhere;
- watch-lists with events: 1941, all reaching their initial-events-end bookmark; pinned windows
  (RV > 0) with events: 2206;
- unary calls failed with a client error (pending writes for the model): 0-34 per (`k`, schedule);
- **not reached:** a watch-list cut before its bookmark (`watchOk`'s `initialPrefixOk` path; covered
  only by `TestWatchOkEdges`), a progress bookmark (the driver never asks for `ProgressNotify`, so none
  is expected: §2's departures), events after an Error event (the non-issue's test reproduces it at
  1-12 of 50 with a fake client: `nonissues/k8s-etcd3-watcher-events-after-error/`).

No Go failure looked like an etcd or Kubernetes bug.
