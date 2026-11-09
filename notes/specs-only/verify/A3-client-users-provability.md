# A3 client users: provability review (2026-11-09)

Reviewer: independent provability verifier. Commit under review: `1aa6fc1337` (`specs-only` HEAD).
Area: batches 1d (`Spec/go_etcd_io/etcd/client/v3/concurrency/`), 1e (`.../leasing/`), 1f
(`.../experimental/recipes/`, `Spec/fmt/`), 1g (`Spec/go_etcd_io/etcd/cache/v3/`,
`Spec/k8s_io/utils/third_party/forked/golang/btree/`), and `Spec/sort/` (3c's trust boundary, in
this area per the brief). Snippets: `examples/specreq/{concurrency,leasing,recipes,cache,btree}/`.
Callees: W0 `client/v3/Api.lean` (KV and Txn contracts, `callErr`, `ctxPrin`), 1b `ApiWatch.lean`
(`watchChAt_recv`, `watchStep`), `api/v3/{State,Model,Wire}.lean`, Perennial (`errors.New`, `wp_fork`).

I wrote these findings before reading any batch, integration or open-question note. Afterwards I
read only `open-questions.md` and `batch-1d.md`/`batch-1f.md`, to see whether a finding is already
a recorded decision. I did not read the A3 completeness report.

## Verdicts

| batch | verdict | first-tier findings |
|---|---|---|
| 1d concurrency | **FAIL** | F1 (`Mutex.Unlock`'s catch-all error disjunct), F2 (`Campaign` -> `Resign` with an empty key), F4 (sentinel error constants) |
| 1e leasing | **PASS** (sampled; see "depth") | none |
| 1f recipes + fmt | **FAIL** | F3 (queue snippets lack the compaction condition the specs gate on; related to recorded A17), F4 (sentinel error constants) |
| 1g cache + btree (+ sort) | **PASS** (the demux's internals checked only in part) | none |

## First-tier findings

### F1 (1d). `Mutex.Unlock`'s third disjunct lets a released mutex return any error

* **Code.** `client/v3/concurrency/mutex.go:134-137`: if `myKey == "" || myRev <= 0 || myKey ==
  "\x00"`, the function returns `ErrLockReleased` and does nothing else.
* **Spec.** `Mutex__Unlock.lean`. The post's disjuncts are: (1) `nil`; (2) `ErrLockReleased` when
  the mutex is released; (3) `⌜err ≠ nil⌝ ∗ mutexSt m st`, with **no condition on `st`**. So on a
  released mutex the post still allows any non-nil error.
* **Effect.** Snippet `ReqTryLock` (after `ErrLocked`, `m.Unlock(ctx) != ErrLockReleased` panics)
  and snippet `ReqLockUnlock` (a second `Unlock` must be `ErrLockReleased`) do not close. The
  `ErrLocked` post leaves `{key := "\x00", rev := -1}` and the first `Unlock` leaves
  `st.released`, but disjunct 3 still admits another error.
* **Fix.** Give disjunct 3 the premise
  `⌜¬ (st.key = [] ∨ sint.Z st.rev ≤ 0 ∨ st.key = [W8 0])⌝`. That is true of the code: line 135
  returns before any other error. `lockerMutex.Unlock` is unaffected.

### F2 (1d). `Campaign`'s failure path calls `Resign` with an empty key, whose permission premise has no source

* **Code.** `election.go:85-88`: if `Proclaim` fails, `Campaign` calls `e.Resign(ctx)`.
  `Proclaim`'s failed-fence path first sets `e.leaderKey = ""` (`election.go:122-124`). So
  `Resign` runs with `leaderKey = ""` and a non-nil `leaderSession`.
* **Specs.**
  * `Election.Resign.spec` requires `⌜effIn (delEff (fun k => k = st.leaderKey)) T⌝`, here
    `delEff (· = [])`.
  * `Election.Campaign.spec` only has `⌜effIn (campaignEff pfx val id) T⌝`. Its delete clause is
    `delEff (fun k => pfx <+: k)`, and `[]` is not under a non-empty `pfx`. `NewElection` always
    gives `pfx ++ "/"`.
  * `effIn` is a pure statement over every `σ`. At a `σ` whose store holds the empty key,
    `delKey σ []` changes the state, and that step is no `campaignEff` step.
  * So at `T := campaignEff …` the premise cannot be discharged. `Campaign`'s sketch ("its
    failure: `Election.Resign.spec` and the error") does not close.
* **Fix.** Weaken `Resign`'s premise to `delEff (fun k => k = st.leaderKey ∧ k ≠ [])`. This is
  sound: no reachable state stores `[]` (`etcdLb_keyNonEmpty`), and the server refuses an empty
  key, so that step is `σ' = σ`.
  * Do not use `pfx <+: k` instead: a resumed election's key comes from a remote client and need
    not be under `pfx`.
  * `Proclaim`'s premise `putEff (· = st.leaderKey) …` has the same edge for v3election's resumed
    `Proclaim` with an empty key. That is not a failure inside this area, but the same sharpening
    (`k ≠ []`) helps that caller.

### F3 (1f). Queue snippets rely on facts the specs give only under the compaction condition, which their `Assumes` omit

* **Specs.** `Queue.Dequeue.spec` and `PriorityQueue.Dequeue.spec` gate both facts behind
  `EtcdModel.exactFrom` on every path:
  * the front fact (`frontByRev`, `frontByKey`): the deleted key is the front, and is under the
    prefix at all;
  * the value fact: `v = kr.value`.
* **Package comment.** `recipes/barrier.go`'s package comment assumes the compaction condition only
  for "the queues' Dequeue on an empty queue".
* **Snippets that do not close.** Each takes the read path, with the queue non-empty, and states no
  compaction assumption:
  * `ReqFIFO` (`v != "a"`);
  * `ReqEveryItemOnce` (`v1 == v2`: without `exactFrom` the spec does not tie `v` to the deleted
    record);
  * `ReqPriorityOrder`, `ReqSamePriority`, `ReqPQEveryItemOnce`.
  * `ReqDequeueWaitThenFed` is ambiguous: its dequeuer may find the queue non-empty.
* **Does the code need the gate?** On the read path, no. The facts hold unconditionally:
  * `claimFirstKey`'s successful `deleteRevReq k modRev` at `σ`, after the read at `σg`, gives
    `frontByRev` and `frontByKey` at `σ` without `exactFrom`. `claimFirstKey.spec`'s premise has
    every piece.
  * The value is the record's, because one mod revision means one record (`putOnce`).
  * Only the watch path needs the gate. That is because 1b's `watchStep` says nothing about a
    response's events without `exactFrom`, not even that their keys are in the watched range.
* **Fix (cheap).** Extend the package comment, or each `Assumes`, to every `Dequeue`. The pinned
  integration tests never compact. This is consistent with recorded decision A17, "Watch
  exactness gated on `exactFrom`".
* **Fix (stronger).** Ask 1b for two unconditional facts, both true of the server, where
  compaction affects only exactness: a watch response's events have keys in the watched range,
  and each event's key-value is the record its revision wrote. The Dequeue specs could then state
  "`k` under the prefix" and `v = kr.value` unconditionally. Today a nil `Dequeue` may, per the
  spec, have deleted an arbitrary key outside the prefix (`ReqDequeueClosed` closes only through
  the package-level assumption).

### F4 (1d, 1f; cross-cutting). Sentinel errors as opaque Lean constants cannot be realized

* **Vocabulary.** `concurrency/Api.lean:454` declares `opaque concErrVal (e : ConcErr) :
  GoInterface`; `recipes/Api.lean:313` declares `opaque recipeErr`.
* **Laws.** `concurrency` `init.spec` states
  `isPkgInit … ⊢ □ ∀ e, globalAddr e.global ↦□ concErrVal e`. `recipes` `init.spec` states
  `globalAddr ErrKeyExists ↦□ recipeErr .keyExists ∗ …`.
* **Why no realization can prove them.**
  * The globals are initialized by `errors.New`, whose Perennial spec (`Spec/errors/New.lean:25-32`)
    returns an arbitrary `err : GoInterfaceOk`. Its code allocates a fresh `*errorString`.
  * The package initializer's proof therefore holds `globalAddr ErrLocked ↦□ v` for an unknown `v`.
  * A Lean constant fixed before execution cannot be shown equal to `v`, and `GoGlobalContext`
    pins no global values (`Perennial/GooseLang/Lang.lean:380`).
  * W0's `errVal` is fine: rpctypes' errors are `EtcdError` struct values, computed
    deterministically.
* **Laws that depend on the constants.** `concErrVal_ok`, `concErrVal_notCanceled`,
  `recipeErr_ne`, `recipeErr_fresh` and `errorsIs_recipeErr` all depend on these constants.
  `recipeErr_fresh` (`callErr err k ⊢ ⌜err ≠ recipeErr e⌝`) also lacks a source for "not
  `context.Canceled`'s value": W0's `callErr_errorsNew` reduces it to that, and the law's left side
  has no heap fact about `Canceled`.
* **Effect.** Every 1d and 1f spec whose post names `concErrVal e` or `recipeErr e`
  (`TryLock`, `Lock`, `Unlock`, `Proclaim`, the recipes' `ErrKeyExists`/`ErrTooManyClients`
  arms), and the snippets that compare against the globals (`ReqTryLock`, `ReqLockUnlock`,
  `ReqHoldTwice`, the double-barrier ones), rest on an unprovable law.
* **Fix.** Use the cache's encoding (`cache/v3/Api.lean:448-454`):
  * `init.spec` gives `∃ v₁…vₙ, globalAddr Errᵢ ↦□ vᵢ ∗ ⌜distinct, non-nil, ≠ errVal _⌝`, provable
    at initialization from the fresh allocations' exclusive points-tos;
  * posts say `globalAddr ErrLocked ↦□ err`, or an opaque persistent `concErr e v` with an
    agreement law;
  * distinctness from `context.Canceled` is proved at initialization, while the new `*errorString`
    is still owned, and recorded in `isPkgInit`.
* **Same pattern elsewhere.** `etcdserver/errors` `srvErrVal` and membership `vErr` look the same
  (other areas; not checked).
* **Status.** This is not in `open-questions.md`. `integration-I1.md` checked these laws for
  *consistency* only.

## What is good

* **1d.**
  * The lent permission `etcdLent γ T P` (one exclusive write update per call, `P` back on every
    definite outcome) composes cleanly with W0's exclusive and persistent KV updates.
  * `fence.spec` is a true pure fact of the model.
  * `lockedSince` covers `issues/mutex-lock-recreated.md` without a disjunction.
  * `stmCommitted` matches the code level by level: `rset.cmps` for SS/S/RR, `wset.cmps(first()+1)`
    for SS, and the serializable empty-transaction case for RR.
  * `observe`'s in-place header write is correctly backed by 1b's `hdrDq` (owned when events are
    present).
* **1e.**
  * The header states plainly what the leasing KV does not meet, each point with its issue.
  * The leasing contract is a weakening with `kvAt_lkvAt`.
  * Writes take persistent updates, which accounts for the re-application of resent writes.
* **1f.**
  * `claimFirstKey`'s "absorb and retry" update is the right TaDa shape.
  * `rwHeld` is unconditional (reads only).
  * Time-free exclusion is honestly scoped to `leaseExpiry = false`.
* **1g.**
  * `getOk`/`getErr` are precise enough for every cache snippet, including `ErrFutureRev` and the
    range checks.
  * `store.Apply`'s certificate from the position, with `validateRevisions`, handles the stale
    applier that can run after a re-list (`cache.go:353-361` with `store.go:115-121`).
  * `cacheOpen` excludes `Watch`'s `Add` from `Close`'s `Wait`.
  * The btree specs restate the old proved ones; `ownBTree_persist` covers frozen clones.
* **sort/fmt.** The trust-boundary claims are plausible. Go's `pdqsort` and `heapSort` guard every
  index with bounds checks, so an inconsistent `Less` yields a permutation. `Sscanf` `%d` on a
  digit string below `2^63` gives its value.

## Proof plans (by batch)

The specs I followed step by step against the Go code and callee specs are marked ✓, with any
failing step; the rest are batched one-liners.

### 1d concurrency (63 files)

* `Mutex.tryAcquire` ✓ (`mutex.go:111-132`):
  * `isSession_client` gives the client and lease; `Sprintf` gives a key under `pfx`;
    `Compare`, `OpPut`, `OpGet` build the ops; `isClient_KV`, then `Txn.If/Then/Else`.
  * `Commit` (exclusive, `□?` false) is built from `etcdLent`'s `P -∗ AU`. Its `Step ⊆ mutexEff`:
    a successful put is `putKey`; refusals are `σ' = σ`.
  * The reply gives `Kvs[0]` on the else branch: compare false means the key is present, and the
    same transaction reads it.
  * Two responses on both branches give `firstCreate`.
* `Lock` ✓:
  * `tryAcquire`; then `waitDeletes(c-1)` (`c ≥ 2` by `etcdLb_init`), then a linearizable `Get`
    from `etcdPeek`.
  * `noOlder` carries over because new keys have later create revisions (a model fact). A
    re-created key gives `c ≤ createRev`.
  * Errors go to `Unlock(client.Ctx())`, whose `T` is within `mutexEff`. The header is made
    persistent by `rangeRespOwn_unfold` and `replyPersist`.
* `TryLock` ✓: the `ErrLocked` arm (`¬ noOlder`, then `Delete` within `mutexEff`).
* `Unlock`: F1.
* `waitDeletes` ✓: `WithLastCreate ++ WithMaxCreateRev(n)` with `n > 0` puts the filter on; an
  empty answer gives `noOlder (n+1)`; a loop.
* `waitDelete` ✓: post `True`.
* `NewSession` ✓:
  * `GetLogger`, `Ctx`, `sessOptAt_call`, then `Grant` (persistent update from `etcdPerm`).
  * `grantEff` matches `leaseStep .leaseGrant` (`Model.lean:1043-1053`); the reply's id is
    non-zero.
  * `WithCancel`, `KeepAlive`, a broadcast channel, then `wp_fork` (a fresh token).
* `Close` ✓ (`Orphan`, `WithTimeout`, `Revoke` within `revokeEff`); `Orphan` ✓; `Done` ✓.
* `Campaign`: F2; the rest closes (the `Proclaim` path's `putKey` keeps `cr`).
* `Proclaim` ✓, `Resign` ✓ (with a non-empty key); `Leader` ✓.
* `observe`/`Observe` ✓:
  * an SPSC channel;
  * the prefix watch from the `Get` header revision (no puts at `σg.rev`: the prefix is empty
    there);
  * `ObservedAt` is gated by `exactFrom`.
* `NewSTM` ✓, `runSTM` ✓ (the goroutine must not panic: `applyOk` admits only `stmError`
  panics, which `defer recover` catches), `mkSTM` ✓ (`isoValid`).
* `stm.commit`, `stmSerializable.commit` ✓:
  * equal mod revisions mean equal records, so `readsAgree` holds;
  * `first()+1 ≤ MaxInt64`;
  * with no writes, S and SS send linearizable `Else` gets, while RR sends an empty serializable
    transaction (its stale case).
* `fetch`, `Get`, `Rev`, `readSet.*`, `writeSet.*` ✓; `respToValue`, `isKeyCurrent`, the getters
  and the `With*` options: one line each, closing.
* The rest close as stated.

### 1e leasing (68 files)

* Checked step by step:
  * `NewKV` ✓: `monitorSession`'s `NewSession` gets `etcdPerm ProtoStep`, and `ProtoStep ⊇ readEff,
    grantEff`.
  * `leasingKV.get` ✓, `acquire` ✓; `txnLeasing.Commit`, `serverTxn` and `guard*` (indices
    guarded) ✓.
  * `leaseCache.Add`, `Update` (`Kvs[0]` after the append), `delete`, `EvictRange` (post `True`;
    the bug is in `issues/leasing-evictrange-key.md`), `lk.get` (guarded by `empty`).
  * `Do` (nil-safe `OpResponse()`) ✓.
* Read but not traced: the other leasing specs (`put`, `delete`, `rescind`, `revoke*`,
  `monitorLease`, `waitRescind`, `gatherOps`, `evalCmp`, `evalOps`). No contradiction seen against
  `kv.go`, `cache.go`, `txn.go` and `util.go`, but the 20 laws are only skimmed.

### 1f recipes (39 files) + fmt (2)

* `putNewKV`, `deleteRevKey`, `claimFirstKey` ✓. `newUniqueKV` and `newUniqueEphemeralKV` ✓
  (retry on `errors.Is(ErrKeyExists)`, which needs F4's fix).
* `newSequentialKV` ✓: `Split` is never empty; `Sscanf_d.spec`; the `Kvs[0]` index is guarded.
* `Queue.Dequeue` ✓ as stated (F3 concerns snippets); `PriorityQueue.Dequeue` likewise.
* `WaitEvents`, `WaitPrefixEvents`, `waitEvents` ✓: `ts ≠ []` guards `evs[i]`, and `0 < rev` holds
  at every call site.
* `Barrier.*` ✓, `RWMutex.*` ✓ (`rwmOwn … (some st)` guards the nil `myKey` in `Unlock`).
* `DoubleBarrier.Enter` ✓: `Kvs[count-1]` is guarded by the `count ≤ 0` early return.
  `Leave` ✓: `some st` guards `myKey.Key()`.
* `Sscanf_d` is a plausible trust spec.

### 1g cache (109) + btree (52) + sort (2)

* `Cache.Get` ✓:
  * `serverRevision` (linearizable count-only `Get`) gives `σ0 ≤ σ1`; `waitTillRevision`
    (`revCond` over `RLocker`) follows.
  * `store.getSnapshot` takes `DescendLessOrEqual`, with the gap after a snapshot quiet (`isStore`).
  * `ErrNotReady` cannot occur after `WaitReady`.
* `Watch` ✓ (rejected, closed and live arms; `enqueueResponse` fills a nil header;
  `IsProgressNotify` is nil-safe via `GetRevision`). `New` ✓ (`CfgValid`, `CfgBounded`).
* `store.Apply`, `Restore` ✓.
* `demux.*`: the specs read plausibly against `demux.go`:
  * `updateStoreLocked`'s `minRev` bookkeeping is correct under the lock;
  * a lagging watcher only causes extra resyncs, never a gap.
  * Not traced against `isDemux`'s full content (uncertain).
* Ring buffer, `ready`, `notifier`, progress requestor: one line each. `waiting` cannot overflow
  because `Get` takes `threadTok`.
* btree: all 51 specs restate `specs-ref`'s proved ones over the new opaque `ownBTree`; I checked
  `New` (`degree > 1`), `Clone`, `ReplaceOrInsert`, `Get` and `AscendRange` against the snippets.
* sort: `anyLessSpec` and `StringSlice.Sort` are plausible.

## Laws

Plausible and non-vacuous unless noted.

* **1d.**
  * `fence` is true of the model.
  * `observeAt_recv`, `observeAt_recvAu`, `stmAt_methods`, `stmAt_reads`, `isSession_client`,
    `sessOptAt_call`, `stmOptAt_call`, `electionSt_session` and `handles_persistent` are fine.
  * `init` and `concErrVal_notCanceled` are **unrealizable** (F4). `concErrVal_ok` can be
    satisfied alone, but only means something with `init`.
* **1e.** The 20 laws were skimmed; I saw no vacuous one (`lkvMarks`/`lkvClean` are exclusive and
  persistent with authority).
* **1f.** `handles_persistent` is fine. `init` and `recipeErr_fresh` cannot be proved (F4);
  `recipeErr_ne` and `errorsIs_recipeErr` are meaningful only with them.
* **1g.**
  * Fine: `cacheRevLb_*`, `cacheOpen_fractional`, `cacheWatchAt_recv`, `wrapsErr_*`,
    `isCache_ne_null`, and `init` (existential, done right).
  * btree: `ownBTree_{sorted,items,fractional,agree,persist,discard_persistent}` and
    `isFreeList_persistent` are fine.
* **fmt.** `scanErr_persistent` and `scanErr_ne_nil` are fine.

## Snippets (78)

* **concurrency (22).** All close except:
  * `ReqTryLock` and `ReqLockUnlock` (F1, F4);
  * every comparison against `ErrLocked`/`ErrLockReleased` depends on F4.
  * `ReqLocker` relies on `PanicV` outcomes plus a Goose `defer recover`; that is plausible but I
    did not check Goose's support (uncertain).
* **leasing (19).**
  * 12 in `lifecycle.go`, `reads.go`, `writes.go` and `txn.go` close (`ReqPutRevision`: every
    application writes `v`; the protocol steps stay under `pfx`).
  * The 7 in `unmet.go` are by design not provable: they record the issues.
* **recipes (17).**
  * Do not close as written (F3): `ReqFIFO`, `ReqEveryItemOnce`, `ReqPriorityOrder`,
    `ReqSamePriority`, `ReqPQEveryItemOnce`; `ReqDequeueWaitThenFed` is ambiguous.
  * `ReqHoldTwice` and the double-barrier snippets that compare sentinels depend on F4.
  * The others close: barrier, rwmutex (rwHeld is unconditional), `ReqDequeueClosed` under the
    package-level assumption, and `ReqWaitFirstDelete`.
* **cache (13).** All close under the package's common assumption, `exactFrom σ.kv 0`.
* **btree (7).** All close.

## Counts

* **Specs.** 335 spec files in the area.
  * About 75 traced step by step; the rest read or batched.
  * Of those traced, two fail a step (`Mutex.Unlock`'s precision, `Campaign`'s `Resign` premise),
    and F4 touches every spec naming `concErrVal`/`recipeErr`.
* **Laws.** 63. Under F4, four cannot be proved (1d's `init` and `concErrVal_notCanceled`, 1f's
  `init` and `recipeErr_fresh`). The pure distinctness laws (`concErrVal_ok`, `recipeErr_ne`) and
  `errorsIs_recipeErr` can be satisfied alone, but say nothing about the program without `init`.
* **Snippets.** 78 checked, of which 7 are leasing's unmet-by-design ones.
  * Of the 71 meant to close, about 55 close outright.
  * 7 do not close as written (F1: 2; F3: 5).
  * The rest rest on F4's laws and close once F4 is fixed.

## Ranking by need of revision

1. **1d concurrency:** F2, F1, F4.
2. **1f recipes:** F4, F3 (both mechanical fixes).
3. **1e leasing:** no finding, but the least deeply traced.
4. **1g cache, btree, sort, fmt:** no finding.

## Bugs in the Go code

No new ones. The leasing and recipes behaviours I met are already filed:
`issues/leasing-evictrange-key.md`, `issues/mutex-lock-recreated.md`,
`nonissues/election-campaign-key-check.md`, `issues/recipes-dequeue-closed-watch.md`.
