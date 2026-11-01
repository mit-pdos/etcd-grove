# Bounds localized: thread counts, reader slots, counters and sizes in one place each (plan, 2026-11-01)

**Status:** accepted, 2026-11-01: the user took the recommendation on each of D1-D4 ("follow your
recommendations on D1-D4; start with B0"). B0 done (2026-11-01): `etc/bounds-check.py` (532 at the start) in the gates and CI, the
lock inventory `notes/bounds-locks.md`. B2's leasing pilot done (2026-11-01, branch `bounds-b2-leasing`: stock 2 → 0 in leasing; "The leasing
pilot's design" below). Next: B2a.

## The problem

Go panics or misbehaves when certain counts or sizes grow too large. Today the proofs that rule this
out are spread over every layer, not kept with the code they protect. Measured on `lean` `176549d2e2`:

- **Thread bounds as premises everywhere.** 46 Spec files take a premise on `threadBound GF`, and they
  use five different forms (`≤ 2^31`, `≤ 2^30 - 1`, `≤ 2^29`, `+ cacheWgOwedMax ≤ 2^31`,
  `≤ actualMaxReaders`). The same three-premise chain, `threadBound GF ≤ 2^31 → receiptBound GF ≤ 2^48
  → receiptBound GF ≤ N + 1`, is restated in 20 Spec files: every example `Main` and every `common/`
  constructor. `NewServer.spec`, `specCompact` and `specM` each carry the same five bound premises.
- **Reader slots counted out by hand.** 92 Spec files mention an `RWMutex` reader resource. They pass
  around `E.RD` (89 mentions), `srvLgReader` (59), `storeReader` (45), `srvLeadTimeReader` (20),
  `lessorRdOf`, `watchReader`, `quotaRd`, `srvReadReader`, `srvBemuReader` and `srvWgReader`. 70 places
  in the proofs hold a counted stock of them (`[∗list] _ ∈ List.replicate 64 (), …`).
  - The constants are arbitrary: 64, `64 - 2`, `actualMaxReaders`.
  - Splitting the stocks takes lemmas such as `etcdGrpcSlots_of_started` (four counts, `3 * N ≤ K`) and
    `watchRunSlots_of`.
  - Each example (`cachekv`, `watchkv`, `authkv`, `linkv3p`, `common/Served`) repeats the same split by
    copy-paste.
  - Two packages already avoid the counting: the lessor and `logkvrw` borrow from a thread pool.
- **Size arithmetic repeated.**
  - Server configuration: `etcdMaxRequestBytesOk`, `maxTxnOpsOk` and `boot.length ≤ 2^60` are
    restated three times in `NewServer`, and discharged by a `simp` block copied into three examples.
  - Literal bounds: `key.length ≤ 2^27/2^28`, `val.length ≤ 2^28` and `pfx.length ≤ …` appear over 90
    times between them.
  - Message-size lemmas: there is one per arity (`opSizeOk.put_lt`, `strsSizeOk.lt_1/2/3`), and 57
    `unfold`/`simp` calls on `wireSlack`/`grpcMsgMax` sit in 23 files, mostly in the per-function
    leasing proofs.
  - Revision bounds: the client's `σ.rev + 3 < 2^63` is restated in about 10 files.
  - Workload premises: each closed result restates its own premises (`grpcRepliesFit`,
    `backendUnderQuota`, `authRecordsFit`, `n + 2 ≤ 2^31`, `clients * ops < 2^60`).

The cost is that an agent proving an ordinary function has to reconstruct this reasoning (how many
slots, which power of two, which premise to thread) even though the function itself has nothing to do
with it. And whenever a bound changes, every layer that restates it has to change too.

The machinery to keep these bounds local already exists:

- Perennial's `threadPool` (`Perennial/Proof/ThreadPool.lean`) and `RWMutexThreads.lean` (reader tokens
  in a pool, borrowed with a thread token);
- `WaitGroupTokJoin.lean` (a wait group's counter backed by thread tokens);
- the time receipts (`GooseLang/Receipts.lean`), which already back every lifetime counter;
- the lessor (`isLeaseObj`, `InvLessor.lean:510`), which shows the reader-pool pattern on a real package.

## The rule

Each bound is reasoned about in exactly one of three places:

1. **The adequacy theorem** fixes the global constants (the thread bound `T`, the step bound `N`, the
   workload) once, in `examples/common/Adequacy.lean`.
2. **The owner of the bounded object** turns a global constant into a protocol of unbounded use. The
   owner is the package invariant that allocates the `RWMutex`, the `WaitGroup` or the counter. The
   protocol lives inside the owner's invariant: a pool of reader slots, a wait group backed by thread
   tokens, a counter ticked by receipts. It is proved once, in the owner's `Inv*`/lemma files.
3. **Clients** see only resources that need no arithmetic: `threadTok` (each goroutine has one; Fork
   provides it), the persistent handles of the owners' invariants, and one named predicate per
   boundary for sizes (`…Fits`).

No spec between the adequacy theorem and the owners mentions `threadBound`, `receiptBound`,
`actualMaxReaders`, a count of reader slots or a power-of-two size literal. A check enforces this (B0).

## Stages

Each stage is independent, can land on its own, and shrinks the B0 counts. The stages that change
statements go through the spec-first discipline: draft, `spec-reviewer`, the user's approval,
regenerated interfaces. None of them weakens a result or adds to the trust base. What changes is how
the premises are packaged and which resources the specs take.

### B0. The check and the inventory (no approval needed)

- **`etc/bounds-check.py`.** It counts, per package, the Spec mentions of `threadBound`,
  `receiptBound`, `actualMaxReaders`, `List.replicate` stocks of a reader resource, and size literals
  `2 ^ (2[6-9]|3[01]|4[08]|6[0-4])`. It skips an allowlist of owner modules and the adequacy files.
  - `--check` compares against `etc/bounds-baseline.txt` and fails if any count grows. Counts may
    shrink (`--update` records the new baseline), so new code cannot add leaks.
  - It is added to `etc/gates.sh`.
- **The lock inventory** (`notes/bounds-locks.md`). For each `RWMutex` whose reader resource reaches a
  spec, record:
  - its owner;
  - its reader resource;
  - who stocks it today;
  - whether any goroutine holds its read lock while holding another read lock (**nested**), from the
    Go code.

  B2 needs the nesting column: one thread token pays for one loan at a time (`ThreadPool.lean`'s
  header).

### B1. The bounds as instances, discharged once (D1)

- Perennial's `ThreadBoundLe GF k` and `ReceiptBoundLe GF k` (`ProgramLogic/Bounds.lean`, landed
  `6e3ca6ca3`, the D1 change), with `pow_succ`: an instance at `2 ^ e` gives one at every larger
  power of two by instance search.
- **Each spec states the power of two its own proof needs** (`[ThreadBoundLe GF (2 ^ 31)]` for a
  wait group's counter, `2 ^ 30` for an `RWMutex`'s readers, `[ReceiptBoundLe GF (2 ^ 48)]` for the
  id generator), as an instance among its section's variables, not as a premise of the triple. A
  caller under a smaller power meets it with no step of its own. A bound that is not a power of two
  (`2 ^ 30 - 1`, `threadBound GF + 3 ≤ 2 ^ 31`) is restated as the next power of two where that
  costs no result anything, or derived inside the owner from the instance.
- **No result is weakened.** The first version of this stage fixed one constant for the whole
  repository (`2 ^ 29` threads), which would have weakened every closed result proved under
  `n + 2 ≤ 2 ^ 31` (the examples' adequacy theorems take `threadBound GF = n + 2`). Corrected on
  2026-11-01 before any spec moved: each closed result keeps its own premise and builds its
  instance from it (`ThreadBoundLe.of_eq`, then `weaken`).
- `receiptBound GF ≤ N + 1` is not a smallness bound: it ties the write-token stock to the step
  bound. It stays until B4.
- **First batch done (2026-11-01, branch `bounds-b1-specs`).** Each converted spec takes the bound
  as a leading instance binder (`∀ [ThreadBoundLe GF (2 ^ k)] …`): the same strength as the
  premise, and `Link.lean`, the callee hypotheses and the `Results` restatements stay as they were.
  A caller with a pure premise adds one `haveI`. Converted: the client's `clientv3.New`, `newClient`,
  `NewWatcher`, `NewWatchFromWatchClient` and kubernetes `New` (`2 ^ 31`), credentials'
  `NewPerRPCCredentialBundle` (`2 ^ 30`), leasing's `NewKV` (`2 ^ 29`, from `2 ^ 30 - 1`: no closed
  result reaches it), mvcc's `New`, `NewStore` and `newWatchableStore` (receipts `2 ^ 48`), and
  client-go's informer chain (receipts `2 ^ 63`, `pop` `2 ^ 61`). `newWatcherGRPCStream`'s premise was
  redundant (`isClientWatcher` carries the bound) and is dropped, which makes the spec stronger.
  **Left:**
  - the cache's `New`/`newCache` (`threadBound GF + 3 ≤ 2 ^ 31`; `2 ^ 30` would weaken the cache's
    exported `cache_end_to_end_*` results, which restate it);
  - the lessor's `Remaining`, `Less` and `Leases` (`2 ^ 30 - 1`; their caller `LeaseLeases` is in
    etcdserver, whose statements wait for the snapshot branches);
  - v3rpc's `GetProgressReportInterval` (its bound travels in `watchRunSlot`, B2's v3rpc pool).

### B2. Reader slots in pools owned by their package (D2)

For each lock in the inventory:

- The owner's invariant holds `threadPool.isThreadPool` over the lock's reader tokens, built at
  allocation by `init_RWMutex_threadPool`.
- The reader resource becomes the owner's persistent handle.
- A spec that read-locks takes `threadTok` in and out, as `Lease.Keys`/`checkLease*` already do.

This deletes the counted stocks (70 places), `etcdGrpcSlots_of_started`, `watchRunSlots_of`,
`leasingMaxReaders`'s stock, and the 64/`64 - 2` split in six examples.

- **Thread tokens at the gRPC boundary.** gRPC handler goroutines need a `threadTok`. If the gRPC
  server's handler contract does not hand one to each handler, B2a adds it. That is a trust-boundary
  spec change and needs approval; Go runs each stream's handler on a goroutine of its own, so the
  model is faithful.
- **Nested read locks (D2).** Where a goroutine holds two read locks at once, one thread token cannot
  pay for both. There are two options:
  - (a) The inner lock keeps a counted stock, local to the one call path that nests.
  - (b) A Perennial change: a lock **level**. A thread token splits into per-level tokens,
    `threadTok ⊣⊢ [∗ l < L] levelTok l`, and a pool at level `l` charges `levelTok l`. Lock order
    gives the levels.

  I recommend (a) unless the inventory shows more than two or three nesting sites; (b) is then the
  general fix, proposed to Perennial on its own.
- **B0's inventory (2026-11-01, `notes/bounds-locks.md`).** 23 reader locks have counted stocks.
  Every nesting stays inside one owner (auth's permission check, mvcc's `store.Read`, the backend's
  `readTx` over `txMu`), where one thread token covers the owner's bundle as one pool item, except at
  three sites that cross owners, each on one long-lived goroutine:
  - the apply thread (mvcc's `store.mu` over `lessor.mu`/`Lease.mu`);
  - the storage-version monitor (`bemu` over the backend's `readTx.mu`);
  - `GoAttach` (`wgMu` over `lgMu`, depositing the caller's thread token in the wait group inside
    that section, so `wgMu` stays counted).

  Three sites is few, so D2's (a) holds: each keeps a counted slot. **No gRPC or `net/http` handler
  gets a thread token today**, so B2a comes before every request-path pool (order below).
- **Order** (as the inventory recommends; it supersedes the order first written here).
  1. Pilot on the leasing client (`client/v3/leasing`: one lock, `lkvReader`, not touched by any
     active branch).
  2. ~~B2a: a `threadTok` for each gRPC run~~ **replaced (2026-11-01, the user's choice): run slots
     built in `NewServer`.** `grpc.serve` runs a handler in the calling client's thread, so the only
     sound source of a handler's thread token is the caller's, which would put `threadTok` on
     `Invoke`'s axiom, the 13 generated stubs, the client library and the examples' calls. Instead
     `grpc.serve`'s `n` per-run slots stay, and `NewServer` builds them itself from its locks' stocks
     (counted inside the one owner) and hands out `n` ready bundles: the examples' splits,
     `etcdGrpcSlots_of_started` and `watchRunSlots_of` go. No trust-boundary change. Pools stay for
     the unbounded goroutines (lease monitors, `GoAttach`, the watch loops). After `snap-j8a`.
  3. The auth store's `E.RD` (the most mentions).
  4. The server's own locks (`lg`, `leadTime`, `read`, `bemu`, `wg`, quota).
  5. mvcc's `storeReader`/`watchReader`, after `m2-b2-mvcc` lands.
  6. The examples' slot plumbing, last.
  7. Any time: the cache's three locks, client-go's two.

- **The leasing pilot's design (2026-11-01, branch `bounds-b2-leasing`).**
  - **The pool.** The leasing KV's invariant (`isLeasingKV`) holds a `threadPool` of every reader
    slot of `leaseCache.mu` but the one `NewKV` reads `waitSession` with, under a new name of
    `LeasingNames`. `NewKV` builds it, under `threadBound GF ≤ 2^30 - 1`; that premise replaces `threadBound GF + leasingWgOwedMax ≤ 2^31`, which
    it implies, until B1. `newKVResult` hands out no slots.
  - **The exported methods** (`Get`, `Put`, `Delete`, `Do`, `txnLeasing.Commit`) take and return a
    `threadTok` instead of `lkvReader`s. Each borrows a slot at entry and gives it back on return.
    The internal functions keep `lkvReader`, a slot their caller holds.
  - **A goroutine started on a token-backed wait group has no token to borrow with**: its token is
    in the wait group. This is the general case, also found in the server's `GoAttach`. The
    resolution: the wait group's running slot holds the pool's **loan receipt** (`ownThreadLoan`)
    instead of a thread token. `get` hands its borrowed slot to the lease monitor and deposits the
    loan at `Add(1)`, and the `go` statement gives `get` a fresh token. The monitor's `Done` returns
    the receipt, and the goroutine gives the slot back for the token it exits with. The counter's
    bound comes from a general lemma (`threadPool.loans_lt`: `k` loans of a pool are fewer than
    `threadBound`, since the pool holds a thread token for each). That lemma is a Perennial change,
    local and marked until it lands (`notes/perennial-changes.md`).

### B3. Wait groups backed by thread tokens

- Inventory the `WaitGroup`s whose counter is bounded by an `Add` count.
- Move the ones counted by live goroutines to `sync.tokJoin` (`WaitGroupTokJoin.lean`).
- Retire the cache's own `cacheWgInv` arithmetic. Its premise `threadBound GF + cacheWgOwedMax ≤ 2^31`
  goes away under B1.
- Low priority: few sites, and they are already local.
- **Status (2026-11-01).** Inventory done (`notes/bounds-waitgroups.md`: 16 wait groups, twelve kept,
  leasing done by the pilot, the client's watch stream by B1's first batch, `GoAttach` with B1's
  server step). `sync.tokJoin` fits none of the hand-written schemes (one adder only); a shared-adder
  wait group in Perennial is a separate proposal. **The cache done** (branch `bounds-b3-cache`):
  `New.spec`/`newCache.spec` take `[ThreadBoundLe GF (2 ^ 31 - cacheWgOwedMax)]` (the exact bound:
  `cache_end_to_end_client`/`_new` keep their premise and build the instance); the budget tokens
  (`γwb`, `cacheWgSlot`) stay, since `cacheWatchSlot`, in `Cache.Watch.spec`, carries one.

### B4. Counters and stocks from receipts

The receipts already are the single budget for lifetime counters. What leaks into specs:

- **`receiptBound GF ≤ N + 1` and the `N + 7` write tokens.** This is the same work as "one token
  count goes with restore in compaction mode" (`notes/decisions.md`). Do it there, owned by the
  backend's stock (`srvWTStockInv`), not as a premise of `NewServer`. Not duplicated here.
- **The client's `σ.rev + k < 2^63`.** State it once as a law of the client's model
  (`etcdState_rev_lt`, from the server's receipt-backed revision bound) and delete the about 10
  restatements.
- **`boot.length ≤ 2^60`.** Moves into B5's configuration bundle.

### B5. Sizes: one predicate per boundary (D3, D4)

- **Configuration (D3).** `cfgScopeOk cfg` bundles `etcdMaxRequestBytesOk`, `maxTxnOpsOk`, the
  compaction-mode clause and `boot.length ≤ 2^60`. It is defined once next to `NewServer`.
  - `NewServer.spec`/`specCompact`/`specM` take it once each.
  - `examples/common` proves it once for the examples' configuration (`cfgScopeOk_default`), replacing
    the three copied `simp` blocks.
- **Message sizes.** One generic lemma from component bounds to `wireLen < grpcMsgMax`, over
  `OpShape`. It replaces the per-arity `opSizeOk.*_lt`/`strsSizeOk.lt_*` lemmas. The leasing proofs use
  it instead of unfolding `wireSlack`.
- **Key, value and prefix lengths.** Named predicates (`keyOk`, `valOk`, `pfxOk`) over the key-length
  and value-length laws' constants, in place of the literal powers of two.
- **Workload (D4).** One record `Workload`, defined in `examples/common`, holds `grpcRepliesFit`,
  `backendUnderQuota`, `authRecordsFit`, `n + 2 ≤ 2^31` and the example's `clients * ops < 2^60`
  (the last as a field per example). Every closed result takes `Hw : Workload …` instead of four or
  five hypotheses.
  - The statements say the same.
  - The `Results` restatements and `tcb-report`'s listing get shorter.

## Interaction with the work in flight (2026-11-01)

| Stage | Can start | Waits for |
|---|---|---|
| B0 | now (a script and a note) | |
| B1 | the Perennial branch, now | the spec side: `snap-j8a` (J8a-3/5/6) and `m2-b2-mvcc` to land, since it touches `NewServer` and the example `Main` specs |
| B2 | the leasing pilot, now | the server locks: `snap-j8a`; mvcc: `m2-b2-mvcc` |
| B3 | now (cache package) | |
| B4 | | restore in compaction mode |
| B5 | | `snap-j8a` (its `NewServer` premises) |

Use `etc/importers.py --count` before each statement change for the rebuild budget.

## Done when

- B0's counts outside the allowlist are zero: no Spec file mentions `threadBound`, `receiptBound`,
  `actualMaxReaders` or a reader-slot count, and no example splits slots.
- `etcdGrpcSlots_of_started`, `watchRunSlots_of` and the per-arity size lemmas are deleted.
- The rule above is a principle in `.claude/skills/spec/PRINCIPLES.md`, with a short pointer in
  CLAUDE.md.

## Decisions (2026-11-01, the user's: the recommendation on each)

- **D1: a Perennial change** (landed `6e3ca6ca3`, with `pow_succ` after it). The constants: each spec
  states its own power of two (B1), not one constant for the repository, which would have
  weakened results.
- **D2: a counted stock at the nesting site**, unless B0's inventory shows many sites (then the
  lock-level split, proposed to Perennial on its own).
- **D3: yes**, `cfgScopeOk`.
- **D4: yes**, one `Workload` record.

The questions as they were put:

- **D1.** Is the bounds class a Perennial change (recommended; local stopgap until it lands) or local
  to this repository? Are the constants (`2^29` threads, `2^48` receipts) right?
- **D2.** For nested read locks: a counted stock at the nesting site (recommended unless the inventory
  shows many sites), or the lock-level split of thread tokens in Perennial?
- **D3.** Bundle `NewServer`'s configuration premises into `cfgScopeOk`?
- **D4.** Bundle the closed results' workload hypotheses into one `Workload` record? This changes how
  every closed result's statement reads, not what it says.
