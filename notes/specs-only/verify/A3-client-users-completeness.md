# Verification round, area A3-client-users, kind **completeness** (2026-11-09)

Batches 1d (`client/v3/concurrency`), 1e (`client/v3/leasing`), 1f (`client/v3/experimental/recipes`),
1g (`cache/v3` and the k8s fork of `btree`). Reviewed at `HEAD` `1aa6fc1337`. I wrote the findings
below before reading the batch notes and `open-questions.md`. I read those afterwards only to mark which
findings are already recorded open decisions.

## Verdicts

| batch | verdict |
|---|---|
| 1d concurrency | **PASS WITH OPEN DECISIONS**: open question 1.13 (mutex = revision fencing), but its premise is wrong for `Mutex`/`Election` as specified (F2). A caller's specs (2e: v3lock, v3election) do not fit 1d's posts (F1): that is 2e's spec to fix, not 1d's. |
| 1e leasing | **PASS WITH OPEN DECISIONS**: 1.8 (weak contract or the fixes), 1.9. The `UNMET` snippets are the users the weak contract knowingly does not serve. |
| 1f recipes | **PASS WITH OPEN DECISIONS**: 1.10, 1.13. |
| 1g cache, btree | **PASS WITH OPEN DECISIONS**: 1.11 (cache). For the btree, Kubernetes' uses have no snippet (F4, second tier). |

Counts:
- **Specs read as their users see them:** 323. That is 62 for concurrency, 66 for leasing, 38 for recipes, 107 for the cache and 50 for the btree, plus the five `Api.lean` files.
- **Snippets read:** 78. That is 22 for concurrency, 19 for leasing (5 of them `UNMET`), 17 for recipes, 13 for the cache and 7 for the btree.
- **User call sites checked:** 41 (listed below). 38 close; the 3 that do not are F1's v3lock `Lock`, v3election `Campaign`/`Leader` and v3election `Proclaim` at revision 0.
- **Callers' specs checked:** 2e's v3lock and v3election (7 specs, 4 do not fit, see F1) and 3e's mvcc tree index (13 specs, which cite 1g only in their sketches; they fit).
- **Coverage:** every function with a spec in `specs-ref` for these packages has one here. The one exception is btree's `initialize`, which is replaced by the generated `SpecPlan.Spec.PkgInit` and is fine.

## First-tier findings

### F1 (caller's spec, batch 2e). v3lock's and v3election's posts use the request's name as the prefix, but 1d's facts are about `name ++ "/"`

- **The code.** `NewMutex(s, pfx)` stores `pfx + "/"` (`client/concurrency/mutex.go:46`), and so does `NewElection` (`election.go:45`). 1d's specs say so: `NewMutex.spec` gives `isMutex m s (pfx ++ "/")` and `NewElection.spec` gives `isElection e s (pfx ++ "/")`.
- **The posts.** So `Mutex.Lock.spec` returns `lockedSince (name ++ "/") k cr σ`, `Election.Campaign.spec` returns `waitedFor (name ++ "/") …`, and `Election.Leader.spec` returns `holdsAt (name ++ "/") …`. All three contain `noOlder (name ++ "/") c`.
- **What 2e claims instead:**
  - `SpecPlan/Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3lock/lockServer__Lock.lean` (post): `lockedSince name k cr σ`.
  - `.../api/v3election/electionServer__Campaign.lean` (post): `waitedFor name k cr σ`.
  - `.../api/v3election/electionServer__Leader.lean` (post): `firstCreate name σ.kv.store [v]`.
- **Why they are false of the code.** `noOlder name c` is strictly stronger than `noOlder (name ++ "/") c`: it also covers keys like `nameX/...`. Take election (or lock) `"a"` while an older key `"ab/1"` of election `"ab"` exists. `Campaign("a")`, `Lock("a")` and `Leader("a")` succeed, yet the posts claim no key under `"a"` is older.
- **Fix.** In 2e's three posts, write `name ++ "/"` (or `go!"/"` appended) in place of `name`. 1d is right.

### F1b (caller's spec, batch 2e). v3election's `Proclaim` post is false at `Leader.Rev = 0`

- **The claim.** `electionServer__Proclaim.lean` (post): `∃ r, σ.kv.store x.key = some r ∧ r.value = value ∧ r.createRev = uint.nat x.rev`.
- **What 1d gives.** `Election.Proclaim.spec` gives `(ownerCmp key rev).holds σ.kv.store` and `etcdLb γ (putKey σ key val id)`. At `rev = 0` an absent key passes the compare (Api header line 30; `nonissues/etcd-v3election-proclaim-rev-zero.md`). `putKey` then creates the key with create revision `σ.kv.rev + 1`, not `0`.
- **Fix.** Add `x.rev ≠ 0 →` to the create-revision clause, or `(x.rev = 0 ∧ r.createRev = σ.kv.rev+1)`. Or state only what 1d gives: the put landed in one revision after a state where the compare held.

### F2 (1d; recorded as open decision 1.13, but its premise does not hold). Exclusion between holders is unprovable from `Mutex`/`Election` even with `EnvCfg.leaseExpiry = false`

- **Who relies on it.** Users rely on two holders never holding at once:
  - `testMutexLock` ("lock %d followers did not wait", `tests/integration/clientv3/experimental/recipes/v3_lock_test.go:93`);
  - `TestMutexWaitsOnCurrentHolder` ("new owner obtained lock before first owner unlocked", `:271`);
  - `etcdctl lock`, which runs the command while holding the lock (`etcdctl/ctlv3/command/lock_command.go:lockUntilSignal`);
  - `etcdctl elect`.
- **Not covered.** No 1d snippet covers this; the recipes have one for `RWMutex` (`ReqNoTwoHolders` in `rwmutex.go`).
- **What open question 1.13 says.** That time-based exclusion holds under `leaseExpiry = false`. For the recipes it does: their updates are per-key TaDa AUs (`RWMutex.Lock.spec`'s `putNewReq k`).
- **Why it fails for 1d.** 1d's `Mutex.Lock.spec`/`TryLock.spec` take `effIn (mutexEff pfx id) T`. `mutexEff` (`concurrency/Api.lean:220`) permits putting or deleting **any** key under `pfx`. So a caller's invariant "`k1` stays present until `m1.Unlock`" is not stable under `T`, because `m2.Lock`'s cleanup may by spec delete `k1`. `campaignEff` (`:225`) is the same for elections.
- **What the code does.** It touches only the session's own key, `pfx + hex(lease)` (`mutex.go:115`, `:144`; `election.go:73`, `:138`).
- **Fix.** Key the effects to the session's key: `mutexEff pfx id := putEff (· = pfx ++ hexKey id) (· = []) id ∨ delEff (· = pfx ++ hexKey id)`, the same for `campaignEff`. The posts' `k` then becomes `pfx ++ hexKey id`.
- **Snippet to add.** `ReqMutexNoTwoHolders` under `leaseExpiry = false`: two sessions, `m1.Lock`, then `m2.Lock` in a goroutine, and a panic if `m2` returns before `m1.Unlock`. Its proof uses `lockedSince`, `fence`, and "only `Unlock(k1)` deletes `k1`".
- **If the user accepts 1.13.** If the user accepts revision fencing only, this becomes second tier. But 1.13's text should then stop claiming that `leaseExpiry = false` gives time exclusion for `Mutex`.

## Second-tier findings

- **F3 (2e coverage, not this area's).** `electionServer.Observe` is translated with a body (`Code/.../v3election.toml`) but has no spec here or in `specs-ref`. 1d serves it: `observeAt_recvAu.spec` was written for it, and `m.kvs = [_]` makes `resp.Kvs[0]` safe, `election.go:89`.
- **F4 (1g btree).** Kubernetes' users have no snippet:
  - `k8s.io/apiserver/pkg/storage/cacher/store/snapshotter.go` builds a tree of snapshot trees, keyed by an immutable `resourceVersion`. It uses `DescendLessOrEqual` stopping at the first item (`:117`), `Min` and `DeleteMin` in `RemoveLess`, and `Clear(false)`;
  - `btree.go:41-121` uses `Clone`, `Delete`, `ReplaceOrInsert` and `AscendGreaterOrEqual`.

  This package is translated with bodies (`Code/k8s_io/apiserver/pkg/storage/cacher/store.lean`), and `specs-ref` had specs of its functions (`btreeStore__*`, `snapshotter__*`). This branch has none. The btree specs do fit these uses: `ItemOrder.item` may hold the frozen inner tree's `ownBTree … DFrac.discard`, which is persistent (`ownBTree_persist`). But the API header lists only etcd's users. Add one snippet: a tree of frozen clones, keyed by revision, read with `DescendLessOrEqual`, stopping at the first item.
- **F5 (1g cache, small).** `TestCacheWithProgressNotify`'s safety half has no snippet and no clause in `cacheWatchAt_recv`: "no periodic progress notification on a watch without `WithProgressNotify`" (`tests/integration/cache_test.go`, subtest at about `:633`). `TestCacheServerRequestProgress` (`:492`) is liveness and out of scope.
- **F6 (1e, small).** The proxy's `Put` and `DeleteRange` go through `Do(PutRequestToOp(r))` and `Do(DelRequestToOp(r))` (`server/proxy/grpcproxy/kv.go:86,94`). Its `Range` and `Txn` through `Do` are covered, but the snippets cover these only as `lkv.Put` and `lkv.Delete`. Both are served by `LKV.DoTriple`, with a nil-safe `resp.Put()`/`resp.Del()`.
- **F7 (2e, weakening only).** `lockServer.Lock.spec` and `electionServer.Campaign/Proclaim/Resign.spec` take the lent token `P` but never give it back, although 1d returns it on definite outcomes.

## Users and patterns (one call site per pattern; ✓ = pre establishable, post sufficient)

**1d concurrency.** The users are v3lock, v3election, grpcproxy, leasing, recipes, etcdctl and the tests.

| pattern | call site | snippet | |
|---|---|---|---|
| session over a named lease, orphaned, then a mutex (`Key`, `Header`) | `v3lock/lock.go:34-50` | `ReqV3LockPattern`, `ReqSessionResumeLease` | ✓ (2e post: F1) |
| session with lease `-1` (no grant) for reads | `v3election/election.go:76,99,126` | `ReqSessionResumeLease` | ✓ (`etcdPeek` = `etcdPerm` of identity) |
| `Campaign` then `Key`, `Rev`, `Header`, `Lease` | `election.go:40-57` | `ReqCampaignProclaim` | ✓ (2e post: F1) |
| `ResumeElection`, `Proclaim`/`Resign` | `election.go:68,118` | `ReqResumedProclaim` | ✓ (2e Proclaim post: F1b) |
| `Leader` then `Kvs[0]` | `election.go:103-107` | `ReqLeader` | ✓ (`m.kvs = [v]`; 2e post: F1) |
| `Observe` in a select, `Kvs[0]` | `election.go:81-90`, etcdctl `observe` (`for range`) | `ReqObserve` | ✓ (the `for range` form not checked against Goose's `chan.for_range`: uncertain) |
| `WithTTL`, `Lease()` for an endpoint key, `Done()` in a select, `Close()` | `grpcproxy/register.go:42-78` | `ReqSessionLease/TTL/Done/Close/Loop` | ✓ |
| session re-made in a loop with the same options | `leasing/kv.go:129-157` | `ReqSessionLoop` | ✓ (`sessOptsAt` returned) |
| `Lock`, command run, `Unlock(TODO)`; `Done` detects expiry | etcdctl `lockUntilSignal` | `ReqLockUnlock` | ✓, except exclusion: F2 |
| two lockers, followers wait | `v3_lock_test.go:57-99`, `:194-284` | none | ✗ F2 |
| `TryLock`/`ErrLocked`, `IsOwner` in a `Txn`, `NewLocker`, relock on one session | `concurrency/mutex_test.go`, `v3_lock_test.go:174` | `ReqTryLock`, `ReqFencedWrite`, `ReqLocker` | ✓ |
| STM at each level, prefetch, abort | `v3_stm_test.go`, `example_stm_test.go` | `ReqSTM*` | ✓ |

**1e leasing.** The users are the gRPC proxy and `leasing_test.go`.

| pattern | call site | snippet | |
|---|---|---|---|
| `NewKV(client, pfx)` assigned to `client.KV` | `etcdmain/grpc_proxy.go:488` | `ReqNewKVProxy` | ✓ (`pfx ≠ []`: the proxy checks `len > 0`) |
| `Range` through `Do`, the reply cached by the proxy | `grpcproxy/kv.go:62-72` | `ReqDoProxyRange` | ✓ |
| `Txn` through `Do`, responses by position | `kv.go:116-130` | `ReqDoTxn`, `ReqTxnPositional` | ✓ |
| `Put`/`Delete` through `Do` | `kv.go:86,94` | (as `Put`/`Delete`) | ✓, F6 |
| `Compact` | `kv.go:144` | `ReqCompactThroughLeasing` | ✓ |
| read-your-writes, put once, cross-client reads | `leasing_test.go` | `UNMET*` | ✗ by design (open 1.8) |

**1f recipes.** The users are the integration tests only (no etcd, Kubernetes or examples code imports the package). Barrier (`v3_barrier_test.go`), double barrier with too many clients (`v3_double_barrier_test.go:99-163`), queue and priority queue (`v3_queue_test.go`), `RWMutex` (`v3_lock_test.go:300-360`), the closed watch (`v3_closed_watch_test.go`) and `WaitPrefixEvents`: each has a snippet ✓. The double barrier's failover (`:169-212`, `s0.Close()` releases the others) is liveness and out of scope.

**1g cache.** The users are `examples/etcd/cache/cachekv.go` and `tests/integration/cache_test.go`.

| pattern | call site | snippet | |
|---|---|---|---|
| `New` with the defaults or options; `WaitReady`; `Close` | `cachekv.go:126`, `cache_test.go` | `lifecycle.go` | ✓ |
| `Watch` from revision 2, exact gap-free puts, with the compactor on | `cachekv.go:134,collect` | `ReqWatchFromRev` | ✓ (puts only, so `exactFrom` holds) |
| `RequestProgress`, then the notification's revision is at most the last event's | `cachekv.go:162,checkProgress` | `ReqProgressQuiet`, `ReqProgressAfterEvents` | ✓ |
| `Get` at a revision agrees with the watch | `cachekv.go:174,checkGet` | `ReqGetAgreesWithWatch` | ✓ |
| the end of a watch, a lagging watcher, `WaitForNextResync` | `cache_test.go:1391-1470` | `ReqWatchEnds` | ✓ |
| rejected watch or get, out of scope, future revision, `WaitForRevision` | `cache_test.go:1335,1478,1524,740` | `get.go`, `watch.go` | ✓ |
| no progress notification without `WithProgressNotify` | `cache_test.go:633` | none | F5 |

**1g btree.**

| pattern | call site | snippet | |
|---|---|---|---|
| mvcc: `Get` then mutate in place, readers at fractions, stop early, `Compact` over a clone deleting from the original | `server/storage/mvcc/index.go:47-265` | `mvcc.go` | ✓ |
| cache: sorted map, frozen clone | `cache/store.go:42-166`, `snapshot.go:29-55` | `btree.go` | ✓ |
| Kubernetes: tree of frozen trees, `DescendLessOrEqual`, `Min`/`DeleteMin`, `Clear` | `apiserver/.../cacher/store/snapshotter.go:65-170`, `btree.go:28-121` | none | ✓ (fits), F4 |

## Callers' specs (other areas)

- **v3lock and v3election (2e).** The premises are establishable:
  - `isClient` gives `clientRest` (`isClient_rest`); `ctxOk` and `ctxPrin` are persistent.
  - The sessions' `effIn` holds: `lease = 0 ∧ grantEff 60`, and `-1` takes no grant.
  - `mutexEff name l ⊇ mutexEff (name ++ "/") l`.

  But four of their seven specs claim facts 1d does not give: F1 (Lock, Campaign, Leader) and F1b (Proclaim). Resign and session fit.
- **mvcc tree index (3e).** The sketches cite 1g's `New`, `Get` (the item returned, then mutated: the item predicate is only the key, persistent), `ReplaceOrInsert`, `Delete`, `Clone`, `Ascend`, `AscendGreaterOrEqual` (stopped early) and `Len`. They fit: `Clone` is taken under `ti.Lock()` (full ownership), and readers under `RLock` take fractions. The realization of `treeOwn` and `idxAt` over `ownBTree` is implied, not written: not verified in detail.
- **leasing and recipes over 1d** (`NewSession` in `monitorSession`; `Concurrency.isSession` with `Client()`/`Lease()`). They fit: `ProtoStep` includes `grantEff`, and `sessOptsAt` is given back for the loop.

## Bugs in the Go code

None found in this round.
