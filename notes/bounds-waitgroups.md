# The wait-group inventory (bounds plan B3, 2026-11-01)

*Amended on landing (2026-11-01):* step 2 (the client's watch stream) was done by B1's first batch
(`e79bb8d873`: the client constructors and watcher take `[ThreadBoundLe GF (2 ^ 31)]`). Step 1's
constant is the cache's exact bound, `[ThreadBoundLe GF (2 ^ 31 - cacheWgOwedMax)]`, not `2 ^ 30`:
`cache_end_to_end_client`/`_new` (`cache/v3/Results.lean`) restate the premise, and `2 ^ 30` would
weaken them; `cachekv` builds the instance from its `2 ^ 29` (`ThreadBoundLe.weaken`). The Go
finding is now `issues/etcd-cache-watch-during-close-waitgroup.md` and
`issues/etcd-leasing-get-during-close-waitgroup.md`.

Every Go `sync.WaitGroup` whose `Add` the proofs reason about, for B3 of `notes/bounds-plan.md`
(wait groups backed by thread tokens). Perennial's `WaitGroup.Add` spec
(`Spec/sync/WaitGroup__Add.lean`) asks for the new counter to stay below `2^31`; each entry says
where that bound comes from today and what B3 should do with it. Taken on `bounds-b3` (`lean`
`ceaa1c4731`, Perennial pin `2130bdb99`). Found with `grep -rln 'isWaitGroup\|WaitGroup.wp_Add\|
tokJoin\|WaitGroupJoin\|sync.join'` over `Proof Spec RaftWitness`, cross-checked against every proof
file that names a `WaitGroup`'s `go!"Add"` and against the Go sources. `RaftWitness/` has none.

Go paths are in the etcd fork (`.lake/go-src/etcd`, `249d76bea7`; the pin `633036387` adds one
commit on top of it, a guard in `etcdserver`'s snapshot merge, which moves no line below), the
examples in this repository (`examples/`), k8s in the module cache
(`k8s.io/client-go@v0.0.0-20261021054439`).

## The tools B3 has

- **`sync.join`** (`WaitGroupJoin.lean`): one owner (`ownAdder`, exclusive) adds and waits; `Add(1)`
  needs `num_added < 2^31 - 1`, the `Add`s since the last `Wait`. Right for a static or
  parameter-bounded count.
- **`sync.tokJoin`** (`WaitGroupTokJoin.lean`): the same single owner, but each `Add(1)` deposits
  the caller's thread token, so the counter is below `threadBound GF`. `isTokJoin` carries
  `⌜threadBound GF ≤ 2^31⌝` (`init` takes it). Lending (`lend_acc`/`unlend_acc`) lets a slot hold a
  receipt `L` instead, under a lending law. **Its adder is exclusive**: it holds the "no waiters"
  authority and the propositions' authority. A wait group that several goroutines `Add` to
  concurrently, with a closer that `Wait`s, does not fit it as it is. Four of the bespoke schemes
  below are of that shape (cache, leasing, `GoAttach`, the client's watch stream).
- **Thread-token facts**: `threadToks_lt`, `threadToks_add_one_lt`; a goroutine started after a
  token-backed `Add` runs **without a thread token** (its token is in the wait group; `Done` hands
  one back to exit with).
- **The pool's loan receipts** (B2's leasing pilot): `threadPool.loans_lt` (local,
  `Proof/go_etcd_io/etcd/client/v3/leasing/PoolLoans.lean:35`, for Perennial):
  `k` loans of a pool are fewer than `threadBound GF`. The answer when the started goroutine must
  hold a pool slot.
- **`ThreadBoundLe GF k`** (`ProgramLogic/Bounds.lean`, with `pow_succ`): the bound as an instance.
  Not used by any Spec file yet; B3's first targets can be its first users.

## The wait groups

### 1. The cache's `Cache.waitGroup` (`etcd/cache`)

- **Go.** Field `cache/cache.go:52`. Adds: `cache.go:96` (`Add(2)`: the watch loop and the
  progress requestor, once, in `New`), `demux.go:45` (`Add(1)`: the demux's resync loop, once,
  `NewDemux`), `cache.go:142` (`Add(1)` per `Watch` call), `cache.go:357` (`Add(1)` per iteration
  of the watch loop's retry loop). Done: `cache.go:98,102,144,359`, `demux.go:47`. Wait:
  `cache.go:309` (`Close`).
- **Counts.** 3 static goroutines for the cache's life, plus one per open `Watch` and one per
  watch-loop iteration (unbounded over time; bounded by the live goroutines at any moment).
- **Scheme.** Bespoke `cacheWgInv` (`Proof/go_etcd_io/etcd/cache/v3/InvCache.lean:451`): `k`
  deposited thread tokens (`Watch`, `wp_cacheWg_Add` `:511`; the loop's iterations,
  `wp_cacheWg_AddRunning` `:641`) plus `d ≤ cacheWgOwedMax = 3` "owed" goroutines that keep their
  own token (`:435`; `wp_cacheWg_AddOwed` `:574`, `InvNew.lean:129` `wp_cacheWg_Add2`, the demux
  through the abstract `wgSlotProtocol`, `InvDemux.lean:696`). Multi-adder: `Watch` from any thread
  with a fraction of the "open" token `cacheOpen`, `Close` with all of it.
- **Bound.** `k < threadBound GF` (tokens) and `d ≤ 3`, with the premise
  `threadBound GF + cacheWgOwedMax ≤ 2^31` (`cacheWg_ctr_bound`, `:499`).
- **Bound premises in specs.** `Spec/go_etcd_io/etcd/cache/v3/New.lean:43`,
  `newCache.lean:40` (2 spec-thread). `Results.lean:158,192` restate them. The caller,
  `cachekv/Main.lean:129`, derives it from its own `threadBound GF ≤ 2^29`.
- **Vestigial budget.** Besides the tokens, each `Watch` and each owed `Add` spends a token of a
  lifetime budget (`cacheWgBudget = 2^31 - 1`, `γwb`, `:204`): `cacheWgSlot` is half of
  `cacheWatchSlot` (`:1123`, with the demux handle), which `Cache.Watch`'s spec consumes, and
  `newCache` hands out `maxReaders - 2` of them. No bound uses it since the thread tokens came
  (`cacheWg_ctr_bound` takes `k` and `d` only). It is an arithmetic leftover.
- **B3.**
  - Retire the budget: drop `γwb`, `cacheWgBudget`, `cacheWgSlot` (from `cacheWatchSlot`, from
    `wp_cacheWg_Add`/`AddOwed`/`Add2`, from the demux's `Pslot`).
  - Replace the premise by `[ThreadBoundLe GF (2 ^ 30)]`, which gives `+ 3 ≤ 2^31` by `omega`
    inside `InvCache`.
  - Keep the owed count (it is static and local; see "Not tokJoin" below).
  - **Statements that change**: `New.spec`/`newCache.spec` (a premise becomes an instance),
    `cacheWatchSlot`'s body (one conjunct fewer; `Cache.Watch.spec` reads the same).
  - **Closed results**: none weakened. `cache_safe` runs under `n + 2 ≤ 2^29`, and `2^29` gives
    the `2^30` instance by `pow_succ`. `cachekv/Main.lean`'s proof builds the instance instead of
    `by omega`.
  - Rebuild: `InvCache.lean` reaches 383 modules (`etc/importers.py --count`).

### 2. The leasing KV's `leasingKV.wg` (`client/v3/leasing`)

- **Go.** Field `client/v3/leasing/kv.go:41`. Adds: `kv.go:68` (`Add(2)` in `NewKV`: the session
  monitor and `clearOldRevokes`), `kv.go:341` (`Add(1)` in `get`, per successful acquisition: a
  lease monitor). Done `:70,74,343`. Wait `:82` (`Close`).
- **Counts.** 2 static, plus one per cached lease key (a monitor lives as long as the lease).
- **Scheme.** Bespoke `leasingWgInv` (`InvLeasingKV.lean:197`), as the cache's but each running
  monitor's slot holds the reader-slot pool's **loan receipt** (B2's pilot), `d ≤
  leasingWgOwedMax = 2` owed (`:77`). Multi-adder with `leasingOpen`. Lemmas:
  `InvLeasingKVLemmas.lean:219` (`wp_leasingWg_Add`, `loans_lt` at `:235`),
  `InvLeasingNewLemmas.lean:37,100,144`.
- **Bound.** `k < threadBound GF` (`loans_lt`), `d ≤ 2`, and `isLeasingKV`'s
  `⌜threadBound GF + leasingWgOwedMax ≤ 2^31⌝` (`InvLeasingKV.lean:259`), derived by `NewKV` from
  its `threadBound GF ≤ 2^30 - 1`.
- **Spec premise.** `Spec/go_etcd_io/etcd/client/v3/leasing/NewKV.lean:39`,
  `threadBound GF ≤ 2 ^ 30 - 1` (1 spec-thread). It is there for the pool, not the wait group (the
  pool's `init` needs `threadBound ≤ slots + 1`). The wait group's `+ 2` rides on it.
- **B3.**
  - Done in substance.
  - Optionally replace `isLeasingKV`'s pure conjunct by deriving `+ 2 ≤ 2^31` from the instance
    B1 gives `NewKV`. That changes a definition (rebuild) and no statement.
  - The spec premise is B1/B2's (the pool's `2^30 - 1`).
  - **Closed results**: none (no example uses the leasing KV).

### 3. The client's watch stream `watchGRPCStream.wg` (`client/v3`)

- **Go.** Field `client/v3/watch.go:184`. Adds: `:577` (`run`, per new watcher), `:975`
  (`newWatchClient`, per resuming substream), `:1010` (a `waitCancelSubstreams` goroutine whose
  watch's context is done). Done `:816` (`serveSubstream`), `:1012`. Wait `:544` (`run`'s
  teardown).
- **Counts.** One per watcher substream, plus one per cancelled resuming substream: per watcher,
  unbounded over time.
- **Scheme.** Bespoke `wgsWgInv` (`Proof/go_etcd_io/etcd/client/v3/InvWatchWg.lean:60`): one
  deposited thread token per goroutine added, `run` the adder (`wgsWgAdder` `:78`). The adder is
  shared with `waitCancelSubstreams`' goroutines by `wgsWgShared`/`wgsShareTok`
  (`InvWcJoin.lean:74,80`).
- **Bound.** Tokens, and `⌜threadBound GF ≤ 2^31⌝` carried in `wgsWgAdder` (`:80`),
  `wgsWgShared`/`wgsShareTok` (`InvWcJoin.lean:77,82`), `InvWatcherCore.lean:46`,
  `InvWatch.lean:1301`; `wgsWg_init` (`:96`) takes it.
- **Spec premises (6 spec-thread).** `Spec/go_etcd_io/etcd/client/v3/New.lean:46`,
  `newClient.lean:38`, `NewWatcher.lean:39`, `NewWatchFromWatchClient.lean:37`,
  `watcher__newWatcherGRPCStream.lean:40`, `client/v3/kubernetes/New.lean:38`, all
  `threadBound GF ≤ 2 ^ 31`, there only for this wait group. (The client's `2^30` for its
  credentials lives inside `clientAuthPre`, a Proof definition.) Downstream:
  `examples/common/NewClient.lean:35`, `NewClients.lean:42`, and every example `Main`'s chain.
- **B3.**
  - Keep the invariant: it is already token-backed and needs no arithmetic beyond the power of two.
  - Replace the pure `threadBound GF ≤ 2^31` by `[ThreadBoundLe GF (2 ^ 31)]` in the five client
    specs, kubernetes `New`, and the four invariants.
  - **Statements that change**: those six specs (a premise becomes an instance).
  - `examples/common`'s two specs keep their premise until B1 reaches the examples. Their proofs
    build the instance (`examples/common` is on the snapshot branches: one line each).
  - **Closed results**: none weakened (all are under `2^31` or `2^29`).
  - Rebuild: `InvWatchWg.lean` reaches 468 modules, `Spec/.../client/v3/New.lean` 287.

### 4. `waitCancelSubstreams`' local `wg` (`client/v3`)

- **Go.** `client/v3/watch.go:989` (local). Add `:994`, one per resuming substream. Done `:996`.
  Wait `:1021`, in a goroutine. This is the fork's F4 (`issues/etcd-watch-resume-waitgroup-overflow.md`).
- **Counts.** One per resuming substream (per watcher).
- **Scheme.** `sync.tokJoin` with lending (`InvWcJoin.lean`, namespace `wcjN`). A goroutine that
  adds to the stream's wait group (3) lends its slot's token there. The receipt is the stream's
  running token, and the lending law is `wcj_law` (`:273`).
- **Bound.** Tokens; `wcj_init (Hb : threadBound GF ≤ 2^31)` (`:302`, used at
  `watchGRPCStream__waitCancelSubstreams.lean:49`), from the same client premise as (3).
- **B3.**
  - Keep: it is already `tokJoin`, the target scheme.
  - The `Hb` follows (3)'s instance.
  - Perennial's `tokJoin.init`/`isTokJoin` could themselves take `[ThreadBoundLe GF (2^31)]`
    (a small Perennial change; optional).

### 5. The server's `EtcdServer.wg` (`GoAttach`)

- **Go.** Field `server/etcdserver/server.go:276`. Add `:2447` (`GoAttach`, under `wgMu.RLock`,
  after checking `stopping`). Done `:2449`. Wait `:827` (`run`'s shutdown, after closing
  `stopping` under `wgMu.Lock`).
- **Counts.** One per `GoAttach` call: the apply thread's alarm and compaction goroutines,
  `sendMergedSnap`, `Start`'s monitors. Per request or event, unbounded over time.
- **Scheme.** Bespoke `goAttachInv` (`Proof/go_etcd_io/etcd/server/v3/etcdserver/InvGoAttach.lean:98`):
  `threadToks k` with `k` the counter. Multi-adder: the `wgMu` readers, with the `open` flag
  and the `stopping` channel. `wp_goAttach_Add` (`:173`) takes `Hbound`.
- **Bound.** Tokens, and `⌜threadBound GF ≤ 2^31⌝` in `srvGoAttachOk` (`:114`), from
  `goAttach_init` (`InvStart.lean:351`), from `InvBuild.lean:362`, from `NewServer.spec`.
- **Spec premises.** `Spec/go_etcd_io/etcd/server/v3/etcdserver/NewServer.lean:170,337,513`
  (`NewServer.spec`, `specCompact`, `specM`: 3 spec-thread), then every `examples/common`
  constructor and example `Main`.
- **Note.** `f` runs without a thread token (`EtcdServer.GoAttach.spec`: `{{ P }} f() {{ True }}`;
  the caller's token is in the wait group). `notes/bounds-locks.md` says GoAttach'ed goroutines
  "have tokens"; they do not. When B2 pools the server's locks, a GoAttach'ed goroutine that
  read-locks one needs the leasing pilot's loan-receipt scheme (the plan already names `GoAttach`
  as the general case).
- **B3.**
  - Keep the invariant.
  - The premise becomes `[ThreadBoundLe GF (2 ^ 31)]` with B1's server step: `NewServer` is on
    `snap-j8a`, so not in B3 now.
  - The loan-receipt change belongs to B2's server step.
  - **Closed results**: none weakened.

### 6. rafthttp's `pipeline.wg`

- **Go.** Field `server/etcdserver/api/rafthttp/pipeline.go:60`. Add `:67`
  (`Add(connPerPipeline)`, `= 4`, once in `start`). Done `:95` (`handle`). Wait `:83` (`stop`).
- **Counts.** Static 4 per pipeline.
- **Scheme.** `sync.join`. `Add(4)` is a local workaround of `join`'s `Add(1)`-only spec
  (`rafthttp/WaitGroupAdd.lean`, `wgJoin_wp_Add4_of`, `num_added < 2^31 - 4`; the general `Add(n)`
  is in `notes/perennial-changes.md`). Init: `startPeer.lean:198-200`, `startRemote.lean:57-59`.
  Use: `pipeline__start.lean`, `pipeline__handle.lean:219`, `pipeline__stop.lean:51`,
  `Handle.lean:84` (`ownAdder … (W32 4)`).
- **Bound.** Static (`0 < 2^31 - 4`).
- **Spec premises.** None numeric. `Spec/.../rafthttp/pipeline__start.lean` and
  `pipeline__handle.lean` name `sync.join.ownAdder`/`ownDone`.
- **B3.** Keep. When Perennial's `Add(n)` lands, drop `WaitGroupAdd.lean`.

### 7. v3rpc's `serverWatchStream.wg`

- **Go.** Field `server/etcdserver/api/v3rpc/watch.go:160`. Add `:188` (`Add(1)`, once per
  stream: the send loop). Done `:191`. Wait `:668` (`close`).
- **Counts.** Static 1 per stream.
- **Scheme.** `sync.join`, the linked `sync.join.WaitGroup.wp_Add` (`watchServer__Watch.lean:139-167`,
  `serverWatchStream__close.lean:48`). `Spec/.../v3rpc/serverWatchStream__close.lean` names the
  adder.
- **Bound.** Static.
- **B3.** Keep.

### 8. mvcc's `watchableStore.wg`

- **Go.** Field `server/storage/mvcc/watchable_store.go:75`. Add `:86` (`Add(2)`, once in `New`:
  `syncWatchersLoop`, `syncVictimsLoop`). Done `:225,271`. Wait `:114` (`Close`).
- **Counts.** Static 2.
- **Scheme.** A small bespoke invariant, `wsWgInv` (`InvWatchSync.lean:122`: counter = done tokens
  out), `wp_wsWg_Add2_init` (`NewWatchableLemmas.lean:76`, from counter 0),
  `mvcc.wp_wsWg_Wait` (`watchableStore__Close.lean:29`).
- **Bound.** Static (`0 + 2`).
- **B3.** Keep. It could be `sync.join` (with `Add(n)`), but that gains nothing, and `watch-cmp`
  is active on mvcc.

### 9. The backend's interval wait group `readTx.txWg`

- **Go.** `server/storage/backend/read_tx.go:51`, a fresh one per batch interval
  (`read_tx.go:137` `reset`, `backend.go:255`). Add `backend.go:305` (`ConcurrentReadTx`, under
  `readTx.RLock`). Done `read_tx.go:151` (`concurrentReadTx.RUnlock`). Wait `batch_tx.go:392`
  (the rollback goroutine of an ended interval).
- **Counts.** One per outstanding concurrent read transaction (per request).
- **Scheme.** Bespoke `wgBody`/`wgInv` (`InvBackend.lean:534,547`), `wp_rdAdd`
  (`ReadLemmas.lean:642`). Each reader deposits a token of the readers' budget `γ.rdt`
  (`rdMax = 2^31 - 2`, `InvBackend.lean:158`; the authority is discarded). The token comes
  bundled in the reader's `crTok` (`:1022`, with a `txMu` slot) and goes back at `RUnlock`.
- **Bound.** The budget (`hlt` at `ReadLemmas.lean:669`). The budget tokens are handed out with
  the `rdTok` stock (`actualMaxReaders` of them, `NewAlloc.lean:170` `rdMax_split`, `:600-620`),
  so the counter is bounded by the reader stock.
- **Spec premises.** None. The `rdTok` stock is B2's (backend stock 12).
- **B3.**
  - Keep. Under B2 the `rdTok` bundle becomes one pool item and the budget token rides in it
    unchanged.
  - Later, optionally, retire `γ.rdt`/`rdMax`/`rdMax_split` for `loans_lt` (each outstanding read
    holds a loan).
  - No statement changes.

### 10. k8s workqueue's `Typed.wg`

- **Go.** `k8s.io/client-go/util/workqueue/queue.go:220`. "Add" `:180` (`t.wg.Go(...)`, only
  with metrics). Wait `:311,331` (`ShutDown`, `ShutDownWithDrain`, deferred).
- **Counts.** 0 under the proof's `noMetrics` (no goroutine), else 1.
- **Scheme.** No `Add` is reasoned about: `wgInv` (`Proof/k8s_io/client_go/util/workqueue/Defs.lean:240`)
  keeps the counter at 0. The bound the proof needs is on **waiters**
  (`alloc_wait_token`, below `2^31`). It comes from a stock of `shutdownPool = 2^31 - 2` shutdown
  tokens (`Defs.lean:129`), one lent per `ShutDown*` call (`WaitGroup.lean`, `wp_wgWait`).
- **Spec premises.** No `threadBound`. `shutdownToks γ 1`/`shutdownToks γ shutdownPool` appear
  in 10 workqueue Spec files (not counted by `bounds-check.py`: not a `List.replicate` stock).
- **B3.**
  - Out of scope (no `Add`).
  - Candidate follow-up: back the waiters by thread tokens (each waiter is a live goroutine). That
    needs a Perennial lemma (a wait token allocated against a deposited `threadTok`). The
    `ShutDown*` specs would then take `threadTok` instead of `shutdownToks γ 1`. Low priority.

### 11-16. The examples' joins

All six use `sync.join` (`init`, `wp_Add_of`, `wp_Done_of`, `wp_Wait_of`), with resources `True`.

| # | example | Go | Adds | bound from |
|---|---|---|---|---|
| 11 | cachekv `Main` | `examples/cachekv/cachekv.go:123-132` | `nw` writers | spec premise `sint.Z nw < 2^31` (`Spec/.../cachekv/Main.lean`), closed result `cache_safe` `H31` (`Results.lean:71`) |
| 12 | watchkv `Main` | `examples/watchkv/watchkv.go:83-92` | `nw` writers | `nw < 2^31`, `Results.lean:70` |
| 13 | authkv `Main` | `examples/authkv/authkv.go:410-424` | `len(Principals()) = 4` | static |
| 14 | linkv3p `MainWatch` | `examples/linkv3p/linkv3p.go:330-337` | `nw` writers | `nw < 2^31`, `linkv3p/Results.lean:157` |
| 15 | kvreconf `Run` | `examples/kvreconf/check.go:138-166` | `cfg.Proposers` + 1 | `Run.spec`'s `Proposers' < 2^31 - 1`, met by `RandomConfig` (`≤ 3`): static in the closed result |
| 16 | lintest `Run` | `examples/lintest/lintest.go:67-75` | `clients` | `0 ≤ clients < 2^31` (`Spec/.../lintest/Run.lean:54`), restated by every closed result over it: `linkv3p/Results.lean:119`, `k8setcd3/Results.lean:77`, `linkvtxn/Results.lean:71`, `lintest/counter/Results.lean:61` |

Proof sites: `cachekv/Main.lean:477-550`, `watchkv/Main.lean:411-480`, `authkv/Main.lean:332-393`,
`linkv3p/MainWatch.lean:489-549`, `kvreconf/Run.lean:82-247`, `lintest/Run.lean:59-156`.

- **B3.** Keep all six. They are joins, and their counts are static or a workload parameter.
  - The `< 2^31` premises are workload premises: B5's D4 `Workload` record bundles them; it does
    not remove them.
  - **Option, not recommended now**: `tokJoin` would drop `nw < 2^31` from the three writer
    examples (11, 12, 14), whose writers use plain `wp_fork` and need no token. That
    *strengthens* three closed results, but it leaves the writers token-less, which blocks any
    later client spec that takes `threadTok`.
  - It does not work for `lintest.Run` (16): its clients keep their fork's token
    (`wp_fork_tok_body`, `runClient` takes `threadTok`, `logkvrw`'s pool). So `clients < 2^31`
    stays.
  - The snapshot branches touch these examples' proofs.

## Not tokJoin: the multi-adder shape

The plan's "move the ones counted by live goroutines to `sync.tokJoin`" fits none of the bespoke
schemes as they stand:

- **cache, leasing, `GoAttach`**: `Add` comes from any goroutine (a fraction of an "open" token, or
  a `wgMu` read lock), and one closer `Wait`s with the whole. `tokJoin`'s `ownAdder` is exclusive.
- **the client's stream**: `run` adds, and `waitCancelSubstreams`' goroutines add concurrently
  through a local shared adder (`wgsWgShared`), which `InvWcJoin` builds on top of `wgsWgInv`'s
  internals. The lending law `wcj_law` counts the stream's running tokens, each backed by a
  deposited thread token there. If the stream used `tokJoin`, that law would need a `tokJoin` fact
  "`k` `ownDone`s are fewer than `threadBound`", which does not exist (an `ownLent` holds no token).
- **cache and leasing** also start goroutines with `Add(2)` *before* the `go` statements
  ("owed"): the caller has one token for two slots. Lending cannot cover the gap, because a receipt
  for "the next fork's token" is not something a lending law can count. So their `+ 3`/`+ 2` stays
  a static count, absorbed by a `2^30` instance.

Retiring the four bespoke invariants for one library would take a Perennial change:
`sync.tokGroup`, a thread-token-backed wait group with
- a fractional adder (`Add` with a fraction, `Wait` with the whole);
- a fixed number of owed slots (given at `init`, with `[ThreadBoundLe GF (2^31 - K)]` or a power of
  two);
- `tokJoin`'s lending.

It has four users, so it is general (CLAUDE.md, "Changes to Perennial"). It is worth proposing on
its own, after the cheap steps below. It removes several hundred lines of near-duplicate invariants and
lemmas (`InvCache.lean:420-760`, `InvLeasingKVLemmas.lean:219-300`,
`InvLeasingNewLemmas.lean`, `InvGoAttach.lean:86-260`, `InvWatchWg.lean`) and changes no
statement.

## Summary

| # | wait group | counts | scheme today | bound from | spec premises (spec-thread) | B3 |
|---|---|---|---|---|---|---|
| 1 | cache `Cache.waitGroup` | 3 static + per Watch + per loop iteration | bespoke `cacheWgInv`, tokens + 3 owed + vestigial budget | `threadBound + 3 ≤ 2^31` | cache `New`, `newCache` (2) | **retire budget; premise → `ThreadBoundLe (2^30)`** |
| 2 | leasing `leasingKV.wg` | 2 static + per cached lease | bespoke `leasingWgInv`, pool loans + 2 owed | `loans_lt`; `threadBound + 2 ≤ 2^31` in `isLeasingKV` | (NewKV's 1 is the pool's) | done; optional internal tidy |
| 3 | client `watchGRPCStream.wg` | per watcher | bespoke `wgsWgInv`, tokens | `threadBound ≤ 2^31` | client 5, kubernetes 1 (6) | **premise → `ThreadBoundLe (2^31)`** |
| 4 | client `waitCancelSubstreams` local | per resuming substream | `tokJoin` + lending | `threadBound ≤ 2^31` (as 3) | (as 3) | keep |
| 5 | server `EtcdServer.wg` (`GoAttach`) | per `GoAttach` | bespoke `goAttachInv`, tokens | `threadBound ≤ 2^31` | `NewServer` ×3 (3) | keep; instance in B1's server step; loan receipts in B2 |
| 6 | rafthttp `pipeline.wg` | static 4 | `sync.join` + local `Add(4)` | static | none | keep |
| 7 | v3rpc `serverWatchStream.wg` | static 1 | `sync.join` | static | none | keep |
| 8 | mvcc `watchableStore.wg` | static 2 | bespoke `wsWgInv` | static | none | keep |
| 9 | backend `readTx.txWg` | per outstanding read txn | bespoke `wgBody`, budget `rdMax` | budget in `rdTok` (reader stock) | none | keep (B2 carries it) |
| 10 | workqueue `Typed.wg` | 0 (no metrics) | counter 0; waiter stock | `shutdownPool` waiters | none (`shutdownToks` in 10 specs) | out of scope; follow-up candidate |
| 11 | cachekv `Main` | `nw` | `sync.join` | `nw < 2^31` (workload) | none | keep |
| 12 | watchkv `Main` | `nw` | `sync.join` | `nw < 2^31` | none | keep |
| 13 | authkv `Main` | 4 | `sync.join` | static | none | keep |
| 14 | linkv3p `MainWatch` | `nw` | `sync.join` | `nw < 2^31` | none | keep |
| 15 | kvreconf `Run` | `Proposers + 1` (≤ 4) | `sync.join` | `Proposers < 2^31 - 1` (met statically) | none | keep |
| 16 | lintest `Run` | `clients` | `sync.join` | `clients < 2^31` (workload) | none | keep |

16 wait groups. Two need B3 work now (1, 3); one is done (2, B2's pilot); one is deferred to
B1/B2's server steps (5); twelve stay as they are. No closed result is weakened by any of the
recommended steps. None strengthens one either; only the option on 11, 12 and 14 would.

## Recommended B3 order

Active branches (2026-11-01): `snap-j8a`/`snap-j8b`/`snap-bootmeta` touch `etcdserver` (71 Proof,
33 Spec files), `client/v3/ServeFromStart*.lean` and the examples (`cachekv/Main.lean` among
them); `watch-cmp` touches mvcc (`CompactNoDup.lean`); `lease-renew` is done. None touches
`cache/v3/`, the client's watch files, `InvWcJoin`, leasing or kubernetes.

1. **The cache (1).** No active branch touches the package, and it has one caller.
   - Retire the `γwb` budget.
   - Replace `threadBound GF + cacheWgOwedMax ≤ 2^31` by `[ThreadBoundLe GF (2 ^ 30)]` in `New`
     and `newCache`. This is the first Spec use of `ThreadBoundLe`, so it settles how a spec
     states the instance and how `Link.lean`/`Results.lean` thread it, for B1.
   - `cachekv/Main.lean` changes by one line: coordinate with the snapshot branches, or land after
     them.
2. **The client's watch stream (3, with 4).** Replace the pure `threadBound GF ≤ 2^31` by the
   instance in the four invariants and six specs. `examples/common`'s `NewClient`/`NewClients`
   proofs build it, and their specs wait for B1. The rebuild is large (468 modules): run it after
   step 1 has fixed the pattern.
3. **Optional, any time: leasing's internal `+ 2`** (2), from the instance B1 gives `NewKV`.
4. **With B1's server step (after `snap-j8a`): `GoAttach` (5).** `srvGoAttachOk`'s conjunct and
   `NewServer`'s three premises become an instance.
5. **Proposal, independent: Perennial `sync.tokGroup`** (above), then port cache, leasing,
   `GoAttach` and the client stream onto it, with no statement change. Also proposed separately:
   `tokJoin.init` under `ThreadBoundLe`, and the general `Add(n)` (drops rafthttp's
   `WaitGroupAdd.lean`).

## Expected `etc/bounds-check.py` change

- spec-thread 52 → 50 after step 1 (cache 2 → 0).
- spec-thread 50 → 44 after step 2 (client/v3 5 → 0, kubernetes 1 → 0).
- Step 4 is B1's: `etcdserver` 11 → 8.
- The examples' and `common`'s mentions (`threadBound` chains) are B1/B5's.
- No other kind moves.
  - stock: `cacheWatchSlot` stays stocked for its demux handle.
  - len-literal: `ThreadBoundLe GF (2 ^ 30)` is not a length.
  - The `ThreadBoundLe` instances are not counted (the regex is `\bthreadBound\b`).
- The `γwb` budget and `rdMax` are Proof-side; no kind counts them.

## A finding in the Go code (reported, not yet in `issues/`)

`Cache.Watch` concurrent with `Cache.Close` can panic, and so can the leasing KV's `Get` (its
`wg.Add(1)` at `kv.go:341`) concurrent with the close function `NewKV` returns.

- In both, the `Add(1)` can run while `Close` is in `Wait` and the counter reaches 0. Go 1.27's
  `WaitGroup` (`src/sync/waitgroup.go`) panics in that window.
  - The last `Done` stores 0 and wakes the waiter. An `Add` between the store and the waiter's
    check makes `Wait` panic "WaitGroup is reused before previous Wait has returned".
  - An `Add` between the last `Done`'s decrement and its re-check panics "Add called
    concurrently with Wait".
  - Outside the window, `Close` can return while the new goroutine runs. That breaks `Close`'s
    documented "blocks until all goroutines return".
- Neither package documents that `Watch`/`Get` must not overlap `Close`. The server's `GoAttach`
  guards the same pattern with `wgMu` and `stopping`.
- The proofs sidestep it with a precondition: the fractional `cacheOpen`/`leasingOpen` token.
- `notes/decisions.md` ("The wait group and `Close`", near line 1130) says "Go's own
  implementation would not panic here … not a finding". That sentence is wrong.
