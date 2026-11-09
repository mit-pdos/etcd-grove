# Proving mvccfull adequate: the plan (Scope, 2026-11-09)

The user (2026-11-09): "Fix the test, then prove the test case adequate. Make sure to minimize
backtracking in the proof effort (come up with specs before setting out to prove them, ...,
invariants before proofs)". So: `notes/spec-first-plan.md`'s order:

> Scope → Draft (every spec and invariant in full, only the listed glue proved) → Review → Test →
> Probe → **Freeze (the user's)** → Prove

No proof beyond Draft's glue and Probe's named proofs before the Freeze tag. The test was fixed
first (revision 2, `notes/mvccfull.md`). This file is the Scope: what the result says, what it
needs that does not exist, and the decisions that are the user's.

## The top-level statements

**`Run.spec`, for every configuration.** The tester's entry point. For every `cfg : Config` within
the program's resource bounds:

> {the package initialized; `fileHolds p ∅` for each `p ∈ FilePaths cfg`; `envVerifyOff`;
> `threadTok`} `Run(cfg)` {the report}

So `Run` never panics: every check passes in every execution. Its premises over `cfg` are only:

- the resource bounds the adequacy theorem fixes (the thread bound `2^28`, receipts):
  `2·Readers + 2·(2·Streams) + 3 ≤ 2^28`, `Ops < 2^38`, and the like (`notes/bounds-plan.md`);
- the stage's scope premise, below.

**`mvccfull_adequate`**, the closed theorem, as `mvccrand_adequate`, for `Main()` (`MainConfig`):

> for every real execution from a fresh state: the main thread's result, if any, is `#()`, no
> thread is stuck, and none has panicked.

Its hypotheses are mvccrand's:

- `dbOpenOk`, `dbCloseOk`;
- `dbFilesAbsent prog (FilePaths MainConfig)`, a computed list of `Ops + 2` names;
- `verifyEnvOff`, `ckptEffectsOk`;
- `keySized`;
- `sort.Slice.spec`, now also `sort.Strings`' (`notes/mvccrand.md`);
- the package assumptions, and `n + 2 ≤ 2^28`.

**Coverage.** Over all configs, every execution the tester has. `Mix` weights of 0 rule
alternatives out *per config* (`config.go`, corrected in this stage), so `Run.spec` for every
`cfg` covers each alternative.

## What exists, what does not

The tester calls about 60 mvcc, lessor and backend functions. Against `lean` (`037bf21c75`,
2026-11-09):

| Need | Status |
|---|---|
| mvcc's API: `Read`, `Write`, `Rev`, `FirstRev`, `Range`, `Compact`, `Commit`, `Restore`, `Close`, `NewWatchStream`, the `Txn` methods, `NewReadOnlyTxnWrite`, the `WatchStream` methods (id 0) | **proved** (`Api.lean`; compaction over etcd's backend since M2) |
| The watch guarantee the receiver checks (`wsRecvOk`: events, per-watcher and stream progress with `w.k ≤ j`, compaction responses, monotone progress) | **proved**; revision 2's checks are exactly its clauses |
| The nonblocking receive with a sent lower bound (the receiver's stamp) | **proved** (`wsChan_recv.law`'s second form, v3rpc's drain) |
| `mvcc.New` on a **fresh** backend | **proved** (`New.spec` at `mvccStart`) |
| **`mvcc.New` on a backend with data** (a restart; Run's final reopen and full read) | **missing**: the restart plan's item **B3** (`notes/restart-plan.md`, R2d'b, "not started", 1.5-2 weeks est.). `store.restore` is proved (through `Restore`) |
| The image after a close (`mvccImage_stop.law`), reopening (`backend.Close` → `fileHolds`, `backend.New`, `etcdStorage_open.law`) | **proved / laws exist** |
| Snapshot install: `Lessor.Recover`, `Restore` from the builder's closed file | **proved** (`lessor.Recover` proved 2026-11-04; `KV.Restore.contract`) |
| `lease.NewLessor` (axiom), `Grant`, `Revoke`, `Lookup`, `Keys`, `GetLease`, `Leases`, `Stop` | **exist** (mvccrand uses them; `Leases` new to us) |
| **Hashing**: `HashByRev`, `Hashes` | **missing entirely**; details below |
| `primitive.RandomUint64`, `time.Sleep`, `sync`, atomics, select with default | Perennial |
| `sort.Strings` | specified, unproved (a hypothesis, as mvccrand's `sort.Slice`) |

### Hashing, in detail (the survey of 2026-11-09)

- **Not translated.** `hash.go` (`newKVHasher`, `kvHasher.WriteKeyValue/Hash`, `unsafeHashByRev`),
  `store.hashByRev`, `hashStorage.HashByRev/Hashes/Hash` are names only in `mvcc.toml`. The
  hasher's four functions are axioms that say nothing of the value (`kvHasherOk` is opaque;
  `Hash` returns any `KeyValueHash`).
- **The compaction job's hash** is specified as "any". `scheduleCompaction`'s proof threads only
  `kvHasherOk`; its spec must give the value. That reopens a frozen, proved spec (about 760
  lines of proof), and `hashStorage.Store` must keep a ghost list (`Hashes`).
- **No `UnsafeForEach` spec** anywhere (backend `readTx`, bbolt `Bucket.ForEach`, or the mvcc
  key-backend contract `isKeyBackendG`). The hash is order-sensitive, so the spec needs the key
  order under `keySafe`, as `rtRange_safe` gives it for ranges.
- **crc32 has no model** (not in Perennial). It needs a trust-boundary spec of `hash/crc32`'s
  `Hash32`: `Sum32` an opaque function of the bytes written. That is Perennial's standard
  library: proposed there, a marked local axiom until it lands (CLAUDE.md, "Changes to
  Perennial").
- **The statement** (the survey's design):
  - `hashInput log c rev`: the history's entries in key order, those with main revision in
    `(c, rev]`, plus those at or below `c` that `Keep(rev)` keeps (`kiKeep`), minus a tombstone at
    `c`. The values are `kvEncode` (already a function of the key-value: `proto.Marshal`'s spec).
  - `HashByRev(r)`, when some key is live at its revision: `⟨kvHash c rev (hashInput σ.log c
    rev), c, rev⟩`.
  - A compaction's stored hash: the same at `(prev, c)`.
  - Both new issues are exactly the "no live key" exclusion.
  - The pure lemma pack relates `kiKeep`, `keepAt` and `KeyDel` (`kiKeep_eq`, `kiAvail_down` and
    `KeyDel_mono` exist), plus an upper bound on the compaction revision at the hasher's read
    (`crevUB`, which `Keep` already takes).
- Estimate: 3-4 weeks. It is the largest single piece, and it is new API, so it goes through the
  `spec` skill and fresh reviewers before any proof.

### The tester's own proof

mvccrand's proof is 13.8k lines. Its pure model (about 1,100 lines: `Model`, `Pending`,
`WriteModel`, `WatchModel`) carries over nearly verbatim. Its invariants do not: they bake in
`crev = -1`, one store, one stream, no filters and no cancel. mvccfull's Go is 1.8 times
mvccrand's, with compaction, two members plus a builder, restarts, restores, cancel, filters and
stamps. Estimate: 25-30k lines.

## The invariants (design, to be written in full in Draft)

- **The log.** The global history (`states`, `changes`, `comps`), the RWMutex-guarded
  `histR`, as mvccrand's, plus the compaction list. A ghost append-only list of the log's
  operations and of each operation's model effect (revision, compaction revision, leases after
  it): the leader appends, the follower and the builder read prefixes.
- **A member (`memberInv m`)**, generalizing mvccrand's `worldInv`, one per member:
  - its current incarnation's `mvccState γ σ`, with `σ.log` the global history's prefix at the
    member's operation count and `σ.crev` the model's;
  - the atomics `revLo/revHi/cmpLo/cmpHi` with ghost halves: `revLo ≤ σ.rev ≤ revHi`,
    `cmpLo ≤ σ.crev ≤ cmpHi`, each lo a monotone lower bound, each hi above what any write in
    flight can show;
  - `γ` (the incarnation) behind a ghost variable: **a restart changes `γ`**, so readers name the
    member, not the store;
  - the `life` RWMutex protocol: a reader slot carries `isMvcc kv γ`, one `mvccReaders γ 1` and
    the bounds' invariant for the current incarnation; the writer's exclusive lock collects every
    slot (all reader tokens back, which `mvccClosed_rest.law` needs), closes, reopens, and refills
    the slots for the new `γ`.
- **The builder**: a member with no readers or streams; at its close, `mvccImage_stop.law` gives
  the image of its history, which is the global history's prefix at the leader's count.
- **A stream (`smuInv s`)**, generalizing mvccrand's `cmuInv`:
  - the registry ghost map `id ↦ (*watcher, info)` with filters, cancelled (marked before
    `Cancel`; ghost: not marked ⇒ live in `wsState`), compacted;
  - the receiver's `wsRecv rs` half;
  - each watcher's position (`posOk` after `recvEvs rs id`), its floating window for start 0;
  - **stamped ⇒ `w.k ≤ |rs|`**: the stamp is set only when the nonblocking receive reports the
    channel empty with `wsSentLb ι n`, `n ≥ w.k` for every watcher registered (under the lock)
    before the poll;
  - the largest eventless revision received.
- **Readers' floors and bounds**: mvccrand's `reader_au` pattern per member, with `cmpLo/cmpHi` for
  `FirstRev` and `ErrCompacted`.
- **`onceUpTo`**: the global history changes each key at most once per revision. That is a pure
  invariant of the generated log: a txn's puts are distinct and outside its deletes, deletes
  repeat nothing, and a revoke deletes distinct keys. The watch guarantee needs it at every
  compaction revision.

## Decisions for the user (decided 2026-11-09: each the recommended option; `notes/decisions.md`)

1. **Stages.** *Recommended:* two stages.
   - **F1**: `Run.spec` for every `cfg` whose `Mix.Read` gives the hash read weight 0 and some
     other read positive weight (the scope premise: no hash comparisons).
   - **F2**: hashing, which lifts the premise; the closed theorem is restated over `MainConfig`
     at F2.
   - F1 needs everything above but hashing, including B3.
   - The alternative is one stage, with hashing's 3-4 weeks inside it.
2. **B3** (`mvcc.New` on a backend with data) belongs to the restart plan (R2d'b, not started,
   another session decides it). The tester cannot avoid it: every restart, and `Run`'s final
   reopen, call `mvcc.New` on a used file. *Recommended:* take B3 into F1, with its spec drafted
   to the restart plan's needs too (one spec, both clients), and tell the restart plan's owner.
   *Alternative:* wait for R2d'b.
3. **crc32** (for F2): a marked local trust-boundary axiom (`Sum32` an opaque function of the
   bytes written) with a Perennial proposal, or a crc32 model in Perennial first.
   *Recommended:* the axiom and the proposal.

## Risks, probed first in Draft (to avoid backtracking)

1. **The restart chain.** B3's statement (`New` from `mvccStorageFor B Pk L c u` at any image,
   with the receipt) and the `life` protocol around it (incarnation `γ` swap, all reader tokens
   back for `mvccClosed_rest`, the census for `backend.Close`).
2. **The stamp.** The nonblocking receive under the stream lock giving `w.k ≤ |rs|` for every
   registered watcher. The law exists; the lock discipline is new.
3. **The builder → `Restore` handoff.** `mvccImage_stop` at the builder, `backend.New` +
   `etcdStorage_open` on its file, `Restore`'s `σ.log <+: σ'.log` from the global history, and
   `Recover`'s premises (records each what `Grant` wrote; no revoked id granted again: true,
   since `nextLease` only grows).
4. **The two-member hash read** (F2): HashByRev on the other member under both `life` locks.

# Draft (F1): the invariants in full (2026-11-09)

Written before any Lean, per `notes/spec-first-plan.md` ("Invariants written in full"). The file
names are the Draft's Lean modules under `Proof/github_com/mit_pdos/etcd_grove/examples/mvccfull/`.
Carried over from mvccrand unchanged (copied, renamed `mvccfull`): the pure model (`Model`,
`Pending`, `WriteModel`, `WatchModel`: `stMatch`, `pendOf`, `expChs`, `posOk`, ...), `History`
(`histR`, `histRd`, `histW`; the history struct gains `comps`, a writer-owned slice under the same
lock), `revOk` and `histOkM`.

## G. Ghost names (`FullNames`)

`h : HistNames` (the history: `γ.h.g` its cells, `γ.h.l` the mono list of revisions) and, for each
member `m ∈ {0, 1}`, `MemberNames`:

| name | type | halves |
|---|---|---|
| `inc` | `ghostVar (MvccName × Loc)`: the current incarnation (store name, `kv` value) | the member's invariant ½, the `life` lock's resource (fractional) ½ |
| `σ` | `ghostVar MvccState` | invariant ½, writer ½ (as mvccrand's `γ.σ`) |
| `rev` | `monoNat` of `σ.rev` (the store's revision only grows) | auth in the invariant; readers take lower bounds |
| `crev` | `monoNat` of `σ.crev + 1` | as `rev` |
| `bnd` | `ghostVar (w64⁴)`: the four atomics' values | invariant ½, writer ½ |
| `pool` | ghost map `slot ↦ PoolSt` (the reader-token pool, below) | invariant auth; each reader thread its slot's fragment |

The builder needs no ghost state of its own: the writer owns its `mvccState`, `mvccOpen` and
backend outright (no other thread touches it).

## M. A member's invariant: `memberInv h γ m` (namespace `memberN m`)

```
∃ (γk : MvccName) (kv : Loc) (σ : MvccState) (rl rh cl ch : w64) (Hl : List HRev),
  ghostVar m.inc ½ (γk, kv) ∗ mvccState γk σ ∗ ghostVar m.σ ½ σ ∗
  ownInt64 (revLo m) rl ∗ ownInt64 (revHi m) rh ∗ ownInt64 (cmpLo m) cl ∗ ownInt64 (cmpHi m) ch ∗
  ghostVar m.bnd ½ (rl, rh, cl, ch) ∗
  monoNatAuth m.rev σ.rev ∗ monoNatAuth m.crev (σ.crev + 1) ∗ monoListLbOwn γ.h.l Hl ∗
  ⌜rl ≤ σ.rev ≤ rh ∧ cl ≤ σ.crev ≤ ch ∧ histOkM σ Hl ∧ onceUpToAll σ.notifiedLog⌝
```

Who changes what:
- **The writer** alone changes `σ` (every update of a write, `Compact`, `Restore`) and the atomics.
  It holds the other halves, so it knows them exactly.
- **Readers'** updates (`Read`, `Rev`, `Watch`, progress) commit `σ` unchanged. They load `revLo`
  (a floor via `monoNat` lower bounds) and `revHi` after.
- **`σ.rev` and `σ.crev` never decrease** (a write adds a revision; `Compact` raises `crev`;
  `Restore`'s premise `σ.log <+: σ'.log ∧ σ.crev ≤ σ'.crev`; a restart keeps both). So a value
  seen at time `t₁` is bounded by `rh` loaded at `t₂ > t₁`: `rh(t₂) ≥ σ.rev(t₂) ≥ σ.rev(t₁)`.
  That is why the `hi` atomics may go down (a write that changed nothing).
- **`onceUpToAll L`** (pure): every revision changes each key at most once. The generator's
  invariant (txn puts distinct and outside its deletes; a revoke's keys distinct) is kept by each
  of the writer's `End` updates. It gives the watch guarantee's `onceUpTo` at any compaction
  revision.

**A restart** swaps the incarnation (`γk`, `kv`) under the `life` lock (L): the closed store's
`mvccState γk σ` is dropped (ghost), and the reopened one's `mvccState γk' σ'` goes in.
`σ' = ⟨σ.log, σ.crev, none⟩` comes from B3's `New` over the image `mvccImage_stop` gave.

## L. The `life` lock: `isRWMutexGuard (life m) (lifeR γ m)`, with token pools

`lifeR γ m q` (fractional):
```
∃ γk kv, ghostVar m.inc (q/2) (γk, kv) ∗ (m.kv field) ↦{q} kv ∗ isMvcc kv γk ∗ inv (memberN m) …
```
(`isMvcc` and the invariant are persistent.) A reader's `RLock` gets `lifeR γ m q` for its slot's
`q`, so the incarnation is fixed while it reads.

**The reader-token pool** (`poolInv γ m`, namespace `poolN m`): for each reader slot `i` of the
member (the readers of both members, since a reader locks both members, `lockAll`; the
receiver's and the registrar's tokens come from the epoch, below):
```
PoolSt := in | out (q : Qp)
∃ γk, ghostVar m.inc ? … ∗ [∗ map] i ↦ s ∈ P,
   (s = in ∗ mvccReaders γk 1) ∨ (s = out q ∗ lifeR γ m q)
```
- A reader holding `lifeR γ m q` and its fragment `i ↦ in` takes the token: it moves its fraction
  into the entry (`out q`).
- Before `RUnlock` it must return the token and take the fraction back.
- The writer holding `lifeR γ m 1` (after `Lock`) shows every entry is `in`: an `out q` entry plus
  the writer's `1` exceed `1`. So it collects all the tokens; with the epoch's (E) and the
  writer's own, that is `mvccReaderN` for `mvccClosed_rest.law` and the census.
- It reopens and refills each entry with a token of the new `γk'`, from `New`'s
  `mvccReaders γk' mvccReaderN`.

## E. An epoch's streams: `streamInv γ m ι s` (namespace `streamN`) and the stream lock `smuInv`

Per stream, generalizing mvccrand's `worldInv` (stream half) and `cmuInv`.

**`streamInv`:**
```
∃ (S : StreamState) (W : GMap w64 (Loc × RegInfo')) ,
  wsState ι S ∗ ghostVar s.cl ½ S.closed ∗ ghostMapAuth s.reg ½ W ∗ ⌜regOk' S W⌝
```
- `RegInfo' = (key, end, endNil, start, filter, k, cancelMarked)`: `k` is the stream's sent count
  at registration (`Watch`'s `wsSentLb ι k`).
- `regOk' S W`: each registry entry is a watcher of `S` with its range, `fs` the filter's
  predicate (`[]`, `[isPut]` or `[isDel]`) and `w.k = k`. **If not cancel-marked, it is live.**
  Other watchers of `S` have empty ranges.

**`smuInv`** (`s.mu`'s lock):
```
∃ rs W Hl P,
  watchers map ↦$ … ∗ order slice ↦* ids ∗ ghostMapAuth s.reg ½ W ∗ ghostVar s.rcv ½ rs ∗
  monoListLbOwn γ.h.l Hl ∗ ownInt64-free field eventless ↦ P ∗
  ⌜rcvKnown rs W ∧ (∀ i y, rs[i] = y → y.evs = [] → y.rev ≤ P …)⌝ ∗
  [∗map] id ↦ x ∈ W, watcherOwn' Hl rs id x
```
`watcherOwn'` extends mvccrand's: the floating window (`floatLo`, `rev`) for a start of 0,
`stamped → k ≤ |rs|`, `compacted → (the watcher received a compaction response)`, and
`posOk` after `recvEvs rs id` *filtered*.

**The stamp's argument (`recvOne`):** under `s.mu`, the select's default branch is
`nonblockingRecvAuAlt`'s `Ψ`. It is called with `wsSentLb ι n` for `n = max k` over the registry,
a lower bound each registration left. The law gives `n ≤ |rs|`, so every registered watcher may
be marked stamped. Registration happens only under `s.mu` and records `k ≤` the sent count.

**The epoch's tokens:** the registrar and the receiver each hold `mvccReaders γk 1` of the
epoch's incarnation, returned through their wait groups (`regDone`, `recvDone`) to the writer at
`endEpoch`, before any restart.

## W. The writer's resources (`writerOwn`, generalizing mvccrand's)

For each member:
- the halves `m.σ ½ σ`, `m.bnd ½ …`, `m.inc ½`;
- `mvccOpen γk`, `mvccBackend γk 1 B Pk`;
- its own `mvccReaders γk 1`;
- the lessor's resources (`leaseOwn`, `lessorRdOf`, `rdOwn`, `isLessor`);
- the backend's stop channels and the census pieces for `backend.Close`;
- the hook's `applying`/`saved` atomics, owned outright (as mvccrand's).

For the leader only: `histW γ.h Hs` (the history's writer part).

The model: `m.ops ≤ |log|`, `σ.log = histLog (take m.ops)` (the history's revisions up to the
member's), `σ.crev = cmpAfter m.ops`, `m.leases = leasesAfter m.ops`. These are pure functions of
the operation log, which the writer owns (`x.log`, a slice of `*op` it alone reads).

## R. Readers

Per read, mvccrand's `reader_au` per member: `revLo` loaded first (a `monoNat` lower bound of
`σ.rev`), the operation's update at `σ` unchanged, returning `σ.rev`/`σ.crev` and `histOkM`.
`revHi`/`cmpHi` are loaded after (above `σ.rev(t)` by monotonicity). The checks compare against the
snapshot, which extends `Hl`.

**Probe targets** (the risks, from the Scope): B3 + L's pool at a restart (the writer's `restart`),
E's stamp (`recvOne`), and the builder → `Restore` handoff (`restore`).

## Draft: B3's candidate (2026-11-09)

The candidate statement is in `Spec/go_etcd_io/etcd/server/v3/storage/mvcc/ApiNewRestoring.lean`
(`New.specR`, `NewStore.specR`). It typechecks.

- **The generalization.** From `mvccStart` to any `σ` with `MvccReachable σ` and `σ.pending =
  none`, at `mvccStorageFor B Pk σ.log σ.crev u`.
- **The leases.** The lessor's owner part `leaseOwn γl Ls ∅` is lent, with `Restore`'s item premise
  (`lid ∈ Ls`), and comes back at `pendItems σ.log []`.
- **The resumed compaction**, gated by `u`, with `Restore`'s hook and commit-request resources.
- Today's spec is its instance at `mvccStart`, `u = false`, up to lending `leaseOwn γl [] ∅`. Both
  callers (mvccrand, `NewServer`) hold it. The alternative, the lease part conditional on items,
  gives an exact instance with an uglier statement: for Review.

What the survey found:

- **B2 is not a prerequisite.** The `lateWB` merge already happened (`InvRestart.lean:351`); the
  restart plan's B2 row looks stale, for its owner to confirm.
- **The proof** generalizes the internal `NewStore.spec` (the `ns = false` restore path, the
  image's records in place of `kbNoCmp`), `newWatchableStore` and `New` (the log through the
  watcher groups) and the API proofs (`restore_of_storage`'s bridge in place of `imageOk_start`).
  About 800-1300 lines, 1.5-2 weeks.
- **The risks:**
  - the index's ghost allocated at a non-initial log;
  - the receipt budget from `⧖ (logCh L)` (`Restore`'s `restoreRcptM`);
  - the resumed job's `Post ∗ Y`, as `Restore`'s;
  - the reader-token count with a resumed job.

**Blocker for both clients: `lease.NewLessor` on a bucket with records.** Its trust-boundary axiom
(`Spec/.../lease/NewLessor.lean`) requires an empty lease bucket and returns `leaseOwn γl [] ∅`.
Every restart with live leases (the tester's, the server's) reopens a non-empty one.

- Proving `NewLessor` means translating and verifying `runLoop` (expiry, checkpoints): a stage of
  its own.
- *Draft's choice:* restate the axiom over a lease bucket with records, its recovered state
  mirroring the **proved** `lessor.Recover` spec (`Spec/.../lease/lessor__Recover.lean`: the same
  `initAndRecover`; records each what `Grant` wrote; the live set the records' ids; one fresh
  lease per record, no items).
- This restated trusted text goes on the Freeze list, attacked first by the `axiom` skill. The
  restart plan (R2d'b) needs the same restatement, so it is done once for both.

## Draft: B3's internal chain (2026-11-09)

Side-by-side candidates: `mvcc.NewStore.specR` (`Spec/.../mvcc/NewStoreR.lean`),
`mvcc.newWatchableStore.specR` (`newWatchableStoreR.lean`) and `mvcc.New.specR` (`NewR.lean`, with
the API glue `mvcc.api.New.specR_of_internal`, a `sorry` with its outline). They typecheck.

- **Real backend only.** `kb = some d`; no caller uses `none`.
- **The pre at the image.** `L' = [[],[]] ++ R` at the records `r`:
  - `restoreImageM` in place of `kbView ∅ ∗ kbNoCmp`;
  - the contract with the records (`isKeyBackendGR … (kbRecs …) r`);
  - a clean read `keyCleanReadR … RC` (restore's `ns = false` path);
  - `restoreRcptM`;
  - the certificate map at `M` (`certOk`'s shape);
  - the permit at `r.finRev`/`r.crev`;
  - the lessor's owner part;
  - `resumeCtxM` gated by `r.resumes`.
- **The posts** at `L'`/`r.crev`, with the mode-indexed closers (`storeCloserM`, `wsCloserM`).
- **The fresh specs are not exact instances** (`spec_of_specR`, `sorry`): `kb = none` is dropped,
  the view must be clean, the lessor part is lent, and mode on gets `compactRightR` at `-1`, which
  every mode-on caller makes at once. So callers move to `specR`. Splitting on an empty image would
  prove the code's path twice.
- **Size.** About 300-500 changed lines in `NewStore`'s proof, 100-200 in `newWatchableStore`/`New`,
  300-400 in the API proofs.

**The risks:**

- **R1, the main one.** `NewStore`'s batch session (`CreateBucket`, `Unlock`, `ForceCommit`) runs
  before `restore()`, so the registration is fixed and `dlInit` is gone. `Restore`'s
  `restoreFixM -∗` cannot be reused: a new backend lemma is needed, a clean read over the fixed
  registration from `dlsOwn ∅` (nothing deleted since the open).
- **R2.** The view stays clean through that session (nothing written to `Key`): a backend fact,
  not yet in the contract.
- **R3.** The index ghost at a non-initial log versus its compactor names (`idx_renew`'s pattern).
- **R4.** The reader count with a resumed job (`nJobRd`), against `compactLockfree`'s budgets.
- **R5.** `compactRightR` is made before `restore` in mode on.
- **R6.** `NewLessor` on a bucket with records, the restated axiom above.
- To confirm: the server's restart supplies the certificate map's `M`.

R1 and R2 are the Probe's first targets for B3.

## Draft revision: readers per epoch; no `life` lock (2026-11-09)

**Replaces L.** Writing L in Lean showed that it needs agreement on store names. The pool's token
and the reader's `isMvcc` must be of the same incarnation. A store name (`MvccName`, which is
`StoreNames`, with the backend's parameters, functions on bucket names) is not countable, so no
Perennial ghost variable, map or saved predicate can hold it. No API law gives `isMvcc kv γ ∗
isMvcc kv γ' ⊢ ⌜γ = γ'⌝` either.

The `life` lock existed because a reader could stay alive across a restart. That is not an etcd
execution: a restart is the member's process restarting, and its requests in flight end with it.

**The Go change** (tests pass):

- Readers run per epoch, like the streams. `startReaders` starts them (up to `Reads` each, until
  stopped; a `ReadPause` sleep in `Mix`); `stopReaders` stops them and waits.
- A restart stops every reader (both members', since a reader may hash the other member in F2)
  and the restarting member's streams, closes, reopens, and starts them again.
- `life`, `lockAll` and `unlockAll` are gone.

**The vocabulary** (`Members.lean`, typechecked):

- **One cancelable invariant per incarnation**, `memberInv … ι`. It holds `memberState`, or the
  incarnation's retirement token, which the writer swaps in at a restart, when no reader or stream
  of the incarnation is left. The store name `γk = ι.kv` is a parameter.
- **Each goroutine is handed its incarnation's handles at its start** (`isInc`, persistent) and a
  reader token (`incRd`), returned through its wait group.
- **Across incarnations**, `m.σ`'s half, the monotone counters and the atomics leave one
  incarnation's invariant for the next.

## The Freeze list so far (statements that change outside the tester)

| # | Change | Kind | Status |
|---|---|---|---|
| 1 | `mvcc.New`/`NewStore` on any image (B3): `New.specR`/`NewStore.specR` (API) and the internal chain `NewStore`/`newWatchableStore`/`New.specR` | proved spec widened; callers move (mvccrand, `NewServer`, server results) | drafted, typechecks |
| 2 | `lease.NewLessor` on a lease bucket with records: `NewLessor.specR` | **trusted** (an axiom restated); the `axiom` skill before the Freeze | drafted; its instance lemma's proof to fix |
| 3 | `errVars.law` gains `ErrWatcherNotExist` (`errors.New("mvcc: watcher does not exist")`), which the tester's `Cancel` checks compare with, and **the error variables distinct**: `checkStoreRange` tests `err == ErrCompacted` while `err` may be `ErrFutureRev`, and `errorsNewVar` gives no distinctness. A new conjunct at the end of mvcc's package fact (`etc/gen-init.py`'s `SPECIAL`), so existing patterns are unchanged | API law, proved from mvcc's package initialization (distinct `errors.New` allocations) | drafted: `errVars2.law` (`ApiErrVars2.lean`), `errVars_of_errVars2` proved; needs a 43rd conjunct of `mvccInit` (gen-init's mvcc `SPECIAL`: the cells of `ErrEmptyWatcherRange`/`ErrWatcherNotExist`), one pattern (`store__setupMetricsReporter.lean` l.32) gains `, -` |
| 4 | `pick.specW` (the tester's own: a positive weight's choice) | tester | in progress |
| 5 | `WatchStream.Watch.contract` takes the caller's update only for a non-empty range (`⌜empty range⌝ ∨ au`): today the update is required even when the code registers nothing (and handed back unused), so a client cannot keep an invariant that excludes unregistered watchers (the tester's `Watch(k, k)` check; its `w != nil` check on progress responses) | API spec weakened in its pre: every caller unchanged | drafted: `Watch.contractR` (`ApiWatchR.lean`), `contract_of_contractR` proved; its proof changes about 5 lines, two clients a line each |

Each changed statement goes through the `spec-reviewer` (Review), and the restated axiom through the
`axiom` skill, before the user's Freeze.

## Draft: the readers (2026-11-09)

`Readers.lean` and eight specs (`pick.specW`, `genKey`, `genEnd`, `genRange`, `checkStoreRange`,
`readOne`, `startReaders`, `stopReaders`), each with a `sorry` proof whose header has its outline.
They typecheck.

**Found:**

1. **A retired incarnation.** A goroutine holding only `isInc` and a reader token cannot rule out
   `memberInv`'s retired case. So every live goroutine holds a share of the retirement token
   (`incLive`, `incRdL`), all collected back through the wait groups before the writer retires
   the incarnation. A reader also holds a share of the member's `kv` field. `Members.lean`'s
   `incRd` and its header are to be updated to match: one definition, not `incRd` beside
   `incRdL`.
2. **The error variables' distinctness**: the Freeze list's item 3.
3. **`readMixOk`**, the F1 premise: hash weight 0, some positive weight, and the positive weights'
   sum below `2^63` (otherwise `pick`'s total wraps and it falls through to index 5).
4. **`readOne` takes both members' parts**, ready for F2's hashes.
5. **`Run.spec`** must persist the runner's read-only fields and the weight slices before the
   first `startReaders`.
6. **The writer supplies `histRds (2·Readers)`**, the history lock's reader slots, returned per
   epoch.

## Draft: the streams (2026-11-09)

`Streams.lean` and eleven specs (`startEpoch`, `endEpoch`, `act`, `pick`, `watch`, `cancel`,
`expect`, `covered`, `recvOne`, `receive`, `complete`). They typecheck. `Streams.lean` reuses the
readers' vocabulary (`incLive`, `rF`, `ctrInv`, `readQ`).

- **The registry** (`Reg`): each entry records `lo`, the sent count `k` at registration, and the
  cancel mark.
- **`regOk' S W C`.** Liveness follows `C`, the ids `Cancel` was called on, whose halves are held
  by `streamInv` and the registrar. Marking happens under `s.mu`; `Cancel`'s commit happens
  outside it.
- **`watcherOk`**: the floating window (`wPosOk'`), `stamped → k ≤ |rs|`, `compacted →` a
  compaction response received.

**The stamp** (`recvOne`):

1. Under `s.mu`, take `n` = the registry's largest `k`, with its `wsSentLb` (`wsSentLb_zero`
   when the registry is empty).
2. Apply `wsChan_recv`'s nonblocking form. Its empty branch gives `n ≤ |rs|`, so every entry may
   be stamped (`stamp_ok`).
3. A later −1 response is `rs[j]` with `j ≥ |rs| ≥ k`. Unmarked means live, so `wsRecvOk`'s clause
   3 applies.

**Found:**

1. **The empty-range `Watch`**: the Freeze list's item 5.
2. **The notified log** reaches `revHi + 1` (a pending revision's response). `memberState` now
   says `|σ.notifiedLog| ≤ revHi + 1`; the writer stores `revHi` before the write.
3. **`ErrWatcherNotExist`**: item 3.
4. **`time.Sleep.spec`** is taken as a hypothesis (the lease expiry's precedent).

**Left `sorry` in the vocabulary:** `recv_facts` and `maxK_attained`. `complete` says nothing of
its answer, by design.

## Draft: the writer (2026-11-09)

`Writer.lean` and 25 specs (`apply`, `begin`, `end`, `view`, `writeRange`, `writeSub`, `txn`,
`compact`, `checkHook`, `gen`, `genLease`, `genSubs`, `newVal`, `checkLeases`, `openBackend`,
`open`, `shut`, `newMember`, `restart`, `restore`, `write`, `checkAll`, `noCluster.Version`,
`Run`, `Main`). All 76 modules build with the candidates (`/home/ubuntu/.claude-F/jobs/…/buildall.sh`
lists them).

- **The log model.** `opStep`, `runM` and `σOf` give each member's state as a function of the log
  prefix it applied. `logOk`/`opValid`: every operation is valid where it applies (a revoke's or
  put's lease live, a compaction's revision positive, a grant's id above every earlier one).
- **The lease bucket's invariant.** `leaseRecsOk r L`: the bucket holds `leaseRecEnc` of the live
  leases, TTL ≥ 3600. It is held in `lessorW`, kept by `Grant`/`Revoke`, carried by
  `backend.Close`'s `rbOwn` to `NewLessor.specR`'s records.
- **`writerOwn`**: per member `memW` (the incarnation's writer part `incW`, `mvccOpen`,
  `mvccBackend`, `bkKeep` with the census wand, `lessorW`); `lentOk` (the shares lent to readers
  and streams sum to 1, and the reader tokens to `mvccReaderN`); the unused builder files; the
  readers' and streams' join handles.
- **The restart chain:**
  - retire (`inc_retire`: everything back, `memberState` out, `memberCarry` split off);
  - close (`KV.Close`, `mvccClosed_rest` + census, `lessor.Stop`, `backend.Close`,
    `mvccImage_stop`, the lease records);
  - reopen (`backend.New`, `etcdStorage_open`, `NewLessor.specR`, `New.specR` at the image,
    the hook set and frozen, `inc_alloc` from `memberCarry`).
- **The restore chain:** the builder (`newMember` on its file, the log applied up to the leader's
  point, retired, closed), then `backend.New` on its file, `Recover` with the records,
  `KV.Restore` (the follower's log a prefix of the builder's: `runM_mono`), the hook, and the old
  backend closed through the census.
- **The builder has an incarnation invariant of its own** (`memberN 2`), so `apply` has one spec
  for every member: a deviation from the plan, which said the builder needs none.

**Go fixes the writer area forced** (tests pass, retranslated):

1. **`Run` hashed unconditionally at the end.** Now it hashes only if `hashing(Mix.Read)`: the
   readers' pick can choose the hashes, or every weight is 0.
2. **`MainConfig`'s hash read weight is 0 until F2.** The tuned test configs, with unset `Read`
   weights, still exercise hashing.
3. **`restore`'s range deleter captures `kv := f.kv`**, rather than reading the field at each call
   (`mvccDeleter`'s triple fixes the store).

`NewLessorR`'s instance proof is `sorry` for the Draft; its Iris steps are fixed in Probe.

**Premises inherited from callees:**

- `limOf cfg ≤ 2^57` (the backend's `P.Wf`);
- the key count, `|keysOf depth| ≤ 2^62`;
- `[ReceiptBoundLe 2^48]` internal against `Run`'s `2^38`, as mvccrand's.

**To check in Review:**

- `backend.Close`'s `∃ path, bFile γ path ∗ fileHolds path D` against `bkKeep`'s `bFile`: is there
  an agreement lemma?
- `NewLessor` never ties `lessorCfg`'s `minLeaseTTL` to `cfg.MinLeaseTTL`; TTL ≥ 3600 suffices here.
- Streams could adopt `incRd` with the `kv` share, which would drop `qk` from `lentOk`.

## Review round 1: `NewLessor.specR` (`notes/review/mvccfull-f1-newlessor-r1.md`)

Every clause is true of the Go code; it mirrors the proved `Recover`'s post at a fresh lessor.

**First-tier:**

- **F2.** `etc/bounds-check.py --check` fails: the copied `replicate … actualMaxReaders`. There
  are two axioms for one function. *Repair:* `specR` becomes the only axiom (the
  `NewLessor.wp_proof` axiom restated); the original is a theorem from it (`spec_of_specR`,
  proved); the collections resting on the stronger claim are listed; the reader slots are given
  through the owner's handle if possible.
- **F1.** The axiom asserts the receipt `⧖ |recs|` (`lessorMu`'s `⧖ |M|`), which the original
  never did. **For the user at the Freeze:** (a) keep it, arguing that Go's loop runs `|recs|`
  iterations; or (b) take `⧖ |recs|` in the pre. The client must then show it executed that many
  steps.

**Second-tier:** S1 (citation lines; one write-back is stronger than `initAndRecover`'s two), S5
(prove `spec_of_specR` first), S2/S3/S6/S7 optional, S4 (the server's records only in
lease-granting auth-off mode: a note for R2d'b).

## Review round 1: the mvcc API candidates (`notes/review/mvccfull-f1-api-r1.md`)

All four are true of the Go code.

**First-tier:**

- **F1.1.** Today's `New`/`NewStore` specs are instances only with the lease part lent. *Repair:*
  `New.spec_of_specR`/`NewStore.spec_of_specR` (lent and given back), and the Freeze list names
  the exported statements that change: `server_kv_backend`, `server_kv_watchable`,
  `server_kv_backend_hooks` (etcdserver `Results.lean`), `mvccApi_New_wp_proof`,
  `mvccApi_NewStore_wp_proof` (`ApiResults.lean`). One call line each in `NewServer.lean` and
  mvccrand's `runChecks.lean`.
- **F2.1.** The internal `NewStore.specR` takes `RC`, the clean read and the whole
  `restoreImageM`, while its glue outline splits `RC` out of the image. That is B3's R1. *Repair:*
  settle R1's bridge lemma in Probe first, or restate so that `RC` comes from the image inside the
  proof. The internal text is not frozen before then; the API text is unaffected.

**Second-tier (to apply):**

- F1.2/F2.3: pure premises inside the triples.
- F1.3: inline `newResumePre`/`Post`.
- F1.4: `New`'s post gives the receipt `⧖ (logCh σ.log)`, as `Restore`'s update does.
- F2.2: the Freeze list names `NewStore_backend`'s change and the internal re-proofs.
- F3.1: the error variables' apartness stated by name.
- F3.2: `errVars2` replaces `errVars`.
- F4.1: drop the vacuous give-back of `Watch.contractR`'s empty branch.

Noted: the tester's `Watch(k, k)` check assumes a non-empty key (`keysOf` gives none).

## Draft: the glue list (2026-11-09)

By `notes/spec-first-plan.md`'s definition: glue decides nothing over shared state (no lock, no
invariant opened, no ghost update, no loop over protocol state) and only calls its callees and
passes their results on; leaves (getters, pure helpers, constructors) are not glue. Linked by
`etc/gen-link.py --mvccfull` (`etc/link-lean-first-mvccfull.txt`; `api.New.specR` and
`lease.NewLessor.specR` are `?`, hypotheses of `open` and what reaches it).

**Glue** (4):

- `Main`: `MainConfig` then `Run`. **Blocked by a spec**: `MainConfig.spec`'s `mainMixOwn` still has
  the read weights `[1, 1, 2, 1, 1, 2]` (hashes `2`), so `Run`'s `runCfgOk` (`readMixOk`) fails; the
  Go (`config.go`; "Draft: the writer", Go fix 2) now has `[1, 1, 2, 1, 1, 0]`, at which it holds. The proof is
  written up to that one obligation (`sorry`). `Main.spec`'s header ("not provable in F1") is stale.
- `runner.writeRange`: `view`, `tw.Range` (through `shapes.law`), `checkRangeAt`. **Blocked by a
  spec**: `Txn.Range.contract` takes and returns `traceutil.ownTrace trace te`, which
  `runner.writeRange.spec` does not carry (nor does `runner.writeSub.spec`, for `Put`/`DeleteRange`).
  Otherwise the chain closes as mvccrand's `writeOp` range arm (`pendOk`, `HistRevs`, `stateAt_pend`).
- `runner.openBackend`: `DefaultBackendConfig`, the run's batch settings, `backend.New`. **Proved**
  (with a local copy of `mvccrand.wp_DefaultBackendConfig`, which carries mvccrand's package
  assumptions).
- `stream.covered`: `expect`, `check`. **Proved.**

**Not glue** (each with its reason):

- Leaves (pure helpers, getters, constructors): `check`, `choose`, `pick`, `pick.specW`, `itoa`,
  `normalize`, `walkKeys`, `MainConfig`, `FilePaths` (a loop over `Ops` building paths),
  `memberPath`, `buildPath`, `copyState`, `inRange`, `checkKV`, `checkRangeAt`, `watcher.matches`,
  `noCluster.Version` (returns `nil`), `runner.genKey`, `genEnd`, `genRange`, `genLease`, `newVal`,
  `genSubs`, `gen` (the choices, over the writer's own model), `runner.view` (a getter of the history).
- The history and the pending model (ghost updates, the history's lock): `history.snapshot`,
  `appendRev`, `changesAt`, `addComp`, `pending.put`, `pending.del`.
- Atomics in a member's invariant: `inBounds` (`hi.Load`), `runner.checkHook` (`saved.Load`),
  `runner.begin` (`revHi.Store`), `runner.end` (history append, `revLo`/`revHi`, the counter),
  `runner.checkStoreRange` (`cmpHi.Load`), `runner.compact` (`cmpHi`/`cmpLo`, the history).
- The writer's chain (ghost updates of the incarnation and the census): `runner.open`
  (`inc_open_backend`, `inc_alloc`), `shut` (`inc_census`, `inc_stop_image`), `newMember`
  (a constructor: the member, its hook, its atomics), `restart` (`inc_retire`,
  `memberState_split`, the counter's invariant), `restore`, `apply` (the model step),
  `txn` and `writeSub` (they keep `pendOk`, the tester's agreement with mvcc's transaction),
  `checkLeases` and `checkAll` (loops over the model's keys and leases, the revisions),
  `write` (the writer's loop over the log), `Run` (allocates the run, its invariants).
- Goroutines, wait groups, locks: `startReaders`, `stopReaders`, `readOne`, `startEpoch`,
  `endEpoch`, `stream.act`, `watch`, `cancel`, `pick` (under `s.mu`), `recvOne`, `receive`,
  `complete` (`s.mu`), `expect` (a loop over the history with the reader slot).

## Review round 1: the tester (`notes/review/mvccfull-f1-tester-r1.md`)

Every check in `receive`, `readOne`, `checkStoreRange`, `apply`'s helpers, `act`, `watch`,
`cancel` and `endEpoch` is provable from the invariants and mvcc's contracts, except two.

**First-tier:**

- **F1.** `receive`'s `resp.Revision ≤ revHi`: a response can be at the pending `σ.rev + 1`, and
  nothing records that the notified log only grows (`revHi` goes back down). *Repair:* a monotone
  counter `m.nrev` at `|notifiedLog|` in `memberState`/`memberCarry`, exported through `readQ`, with
  an `nrevHi_acc` law.
- **F2.** `memberState` needs `1 ≤ revLo` (`watch`'s `floatLo`) and an absolute ceiling
  `revHi < 2^62`, kept by the writer from `Ops < 2^38`. `revHi ≤ σ.rev + 1` would not do: `restore`
  raises it first.
- **F3.** `MainConfig.spec` is false: its read weights now end in 0, and `Main.spec` is provable
  in F1.
- **F4.** `hashing` needs a spec (false under `readMixOk`) and a link entry; `Run`'s header is
  stale.
- **F5.** `writerOwn` needs `1 ≤ nw`, the writer's own reader token.

**Second-tier:**

- S1: stale headers.
- S2: one `pick` spec, `pick.spec` from `pick.specW`.
- S3, S6: headers giving the reasons.
- S4: the stream progress check over compacted watchers rests on `onceUpToAll`; keep it stated.
- S7: noted.
- **S5, a race in the tester's Go:** `watch` checked the watcher count and then incremented it,
  so a member's streams could pass 512 watchers. *Fixed:* `regs.Add(1) > Watchers` refuses, so a
  registration counts before it happens. Tests pass.

## Repair round 1: the candidates (2026-11-09)

Of "Review round 1: the mvcc API candidates" and "Review round 1: `NewLessor.specR`". Every file
touched builds (`lake build` of the seven modules; the tester's importers not rebuilt here: its
`Streams.lean` is mid-edit). Names kept.

**mvcc API (`ApiNewRestoring.lean`).**
- **F1.1:** `New.spec_of_specR`, `NewStore.spec_of_specR` **proved**: today's `New.spec`/`NewStore.spec`
  with `lease.leaseOwn γl [] ∅` added to pre and post (instance `σ = mvccStart`, `u = false`,
  `Ls = []`; `pendItems_mvccStart`). The docstring says why the part is lent (the restore loop
  re-attaches through it) and who holds it (server's `Hlown`, mvccrand, the tester). **Exported
  statements that change** (in the file's header, for the Freeze list): etcdserver `Results.lean`'s
  `server_kv_backend`, `server_kv_watchable`, `server_kv_backend_hooks` (gain `leaseOwn γl [] ∅` in
  pre and post); mvcc `ApiResults.lean`'s `mvccApi_New_wp_proof`, `mvccApi_NewStore_wp_proof`
  (re-stated); call lines `NewServer.lean` l.845, mvccrand `runChecks.lean` l.172. The
  conditional-lease alternative was not taken (the reviewer's recommendation; for the user at the
  Freeze).
- **F1.2:** `⌜batchLimitOk … ∧ MvccReachable σ ∧ σ.pending = none⌝` inside both pres.
- **F1.3:** `newResumePre`/`newResumePost` removed, inlined as `Restore`'s `if u then … else True`.
- **F1.4:** both posts give `⧖ (logCh σ.log)`; provable (`mvccStorageFor` holds it, persistent;
  step 8 of `NewR.lean`'s glue outline).

**Internal chain (`NewStoreR`, `newWatchableStoreR`, `NewR`).**
- **F2.1:** not restated (R1 unsettled). `NewStoreR.lean`'s header marks the internal statement
  "NOT TO FREEZE BEFORE R1's LEMMA", explains the conflict (`RC = dlsOwn d.γB ∅` lives inside
  `restoreImageM`), and gives the restatement once the lemma holds (option (a): `RC` gone, the read
  lending `storeRT γ ∗ (if d.cm then dlsOwn d.γB ∅ else True)`, the proof splitting it off the
  image). **The bridge lemma**, Probe's target, in `NewR.lean`: `mvcc.NewStore.cleanRead_of_image`
  (`sorry`): from the backend's read specs, `bridgeParams d.P`, `d.cm = true`, `recsSign r`:
  `isPkgInit backend ∗ isPkgInit schema ∗ isBackend d.γB d.P (lateW d.gx) Pk d.be ∗ keySized … ∗
  storeDlReg d.γB γi ⊢ ∀ γ, ⌜γ.bucket = γb ∧ γ.kb = some d ∧ γ.idx = γi⌝ → keyCleanReadR (iface
  d.be) (bucketViewC γ) iprop(storeRT γ ∗ backend.dlsOwn d.γB ∅) (kbRecs γ.kb γ.bucket r) r`
  (`keyCleanRead_of_backendC` with the registration fixed and the deleted-entries half at `∅` lent
  in place of `dlInit`). The glue outline's step 4 cites it.
- **F2.3:** `⌜batchLimitOk … ∧ restoreLogOk R⌝` inside the three pres.
- **F2.2:** not done (Freeze list wording; the internal corollaries stay `sorry` until R1).

**`errVars2.law` (`ApiErrVars2.lean`).** **F3.1:** apartness over the variables:
`□ ∀ X Y, ⌜X ∈ errVarNames ∧ Y ∈ errVarNames ∧ X ≠ Y⌝ -∗ errVarApart X Y` (`errVarNames` the four
names); `errVarMsgs` gone (the messages are the proof's). A client discharges `X ≠ Y` by
`simp [ErrCompacted, ErrFutureRev]` (`decide` fails: the names take section instances).
`law_of_ext`, `errVars_of_errVars2`, `compacted_ne_future` proved. **F3.2:** not done (it edits
`Api.lean` and callers; at the Freeze).

**`Watch.contractR` (`ApiWatchR.lean`).** **F4.1:** the empty branch's give-back dropped;
`contract_of_contractR` proved.

**`NewLessor.specR` (`NewLessorR.lean`).**
- **S1:** citations fixed (`:231`, `:245`); the one write-back argued from `UnsafeCreateBucket`'s
  `pending++` (`batch_tx.go:144`), `Unlock`'s write-back/commit (`:328-333`, `:355`),
  `ForceCommit` = `lock`, `commit`, `Unlock` with `commit`'s reset (`:300`, `:362-366`); one token
  said to be stronger than `initAndRecover.spec`'s two.
- **S2:** post gains `lease.lF "minLeaseTTL" lp ↦□ cfg.MinLeaseTTL'` (true: set at `:231`, never
  written again).
- **S5:** `spec_of_specR` **proved** (the instance at `recs = []`, `Lr = []`).
- **S7:** docstring: only buckets whose every value is exactly `leaseRecEnc` (a scope restriction).
- **F1 (the receipt `⧖ |recs|`):** for the user; the file's header states (a) and (b) precisely:
  (b) adds `⧖ recs.length` to the pre; suppliers: the tester's writer (a per-operation receipt
  carried across `shut`/`open`, its live leases each one `Grant`), the server's restart (the image's
  `⧖ (logCh L)` with a law that each record is a grant applied at a revision of `L`).
- **F2** (one axiom, the bounds gate): not done, at the Freeze switch. S3, S4, S6, S8: not done.

## Repair round 1: the tester (2026-11-09)

Every finding of `notes/review/mvccfull-f1-tester-r1.md` repaired but S5 (fixed earlier, in the Go)
and S7 (a header line). `buildall` builds every mvccfull module and the candidates;
`etc/gen-link.py --mvccfull` regenerates `Link.lean` (it now links `hashing`), which builds.

- **F1** (the notified length): `MemberNames.nrev`, a monotone counter at `|σ.notifiedLog|`, its
  auth in `memberState` and `memberCarry`; `readQ` exports `monoNatLbOwn m.nrev |σ.notifiedLog|`;
  new law `nrevHi_acc` (`Readers.lean`: `incLive ∗ monoNatLbOwn m.nrev n` gives `n ≤ revHi + 1` at
  the load; `sorry`). `stream.receive`'s header and proof outline use it for `resp.Revision ≤
  revHi` (the spec statement unchanged: `recv_facts` already gives `readQ`).
- **F2** (the bounds): `memberState`/`memberCarry` gain `1 ≤ revLo` and `revHi < 2 ^ 62`;
  `revLo_acc` returns `1 ≤ v`, `revHi_acc` (and `nrevHi_acc`) `v < 2 ^ 62`. The writer: `begin`'s
  premise is now `σ.rev + 2 < 2 ^ 62` (was `2 ^ 63`; its callers have `Ops < 2 ^ 38`); `end` keeps
  both from the invariant (the new revision is between `σ`'s and `begin`'s `revHi`); `restore`'s
  header says the builder's revision is below `2 ^ 62`. `cmpHi` needs no ceiling (no check uses one).
  `watch`'s header names both.
- **F3**: `mainMixOwn`'s read weights are the code's `[1, 1, 2, 1, 1, 0]`; `Main.spec`'s header
  rewritten; **`Main.wp_proof` proved** (`mainConfig_ok`: `runCfgOk` at `mainConfigM`, by `decide`
  after the fields; the keys of depth 4 are 120).
- **F4**: `Spec/.../mvccfull/hashing.lean` (`hashing.spec`: the result is `hashingM` of the weights;
  `hashingM_of_readMixOk`, proved: `false` under `readMixOk`), `Proof/.../hashing.lean` (`sorry`, a
  leaf), `hashing:` in `etc/link-lean-first-mvccfull.txt` and in `Run:`'s callees, `Run.wp_proof`
  takes `wp_hashing`; `Run.spec`'s header and `Run`'s outline rewritten (`hashes` skipped).
- **F5**: `writerOwn`'s member conjuncts gain `1 ≤ nw` (the header: `Run` has it from `runCfgOk`'s
  `2·Readers + 4·Streams + 3 ≤ 2 ^ 28` against `mvccReaderN = rdStockN - 7 = 536870776`,
  `RdPool.lean`'s `rdStockN_val`).
- **The glue gap (the trace)**: `runner.writeRange.spec` and `runner.writeSub.spec` take and give
  back `traceutil.ownTrace trace te` (a new `te`); `txn`'s and `apply`'s outlines say they thread
  the trace their `traceutil.TODO()` makes (their specs do not mention it: the trace is local).
  **`runner.writeRange.wp_proof` proved** (as mvccrand's `writeOp` range arm: `view`, `Range`,
  `checkRangeAt` at `m.cmp = σ.crev`, with local `viewRev_writeRev`, `viewSt_match`).
- **S1**: `restore`'s stale "Go change needed" replaced (the capture is in, `a4c071c7dd`); `Run`
  and `Main` (F3, F4).
- **S2**: `pick.spec_of_specW` (`pickW.lean`, proved); `pick.wp_proof` is
  `pick.spec_of_specW (pick.wp_proofW wp_choose)`, so `pick` has one proof (`pickW.lean`'s, `sorry`).
  Callers keep whichever spec they use.
- **S3**: `checkStoreRange`'s header says why checking at `clo` loses nothing. **S6**: `receive`'s
  header says `histOkM` rules out `changesAt`'s panic. **S4**: `receive`'s header states the
  dependency on `onceUpToAll`. **S7**: `open`'s header says which halves `memberCarry` holds.
- **`incRd` for the streams** (done: it drops `qk`): `Streams.lean`'s `epRd E q` is `incRd` of the
  epoch's incarnation; `regOwn`/`rcvOwn` hold one `epRd` each, `epochTok E q` the receiver's history
  slot and two `epRd E (q/2)`; `epRd_split` (proved) splits it into a reader token, `epLive` and the
  `kv` share (what `receive`'s and `endEpoch`'s unchanged specs take). The streams do not read
  `m.kv`, but with every goroutine's part one shape, the writer's shares of the retirement token and
  of `kv` are equal: `lentOk` loses `qk` and its second equation, `memCore`/`memW` their `qk`
  parameter (`apply`, `txn`, `compact`, `checkLeases`, `checkAll`, `end`, `open`, `newMember`'s
  specs lose it), and `startEpoch` takes the `kv` field at the writer's share `qw` (it had the whole
  field, which the streams' shares now exclude).

# Probe (F1, 2026-11-09)

The Probe set (named in "R. Readers"): B3 at the writer's `restart`, the stamp (`recvOne`), the
builder → `Restore` handoff (`restore`). Three agents, one worktree; details in
`notes/mvccfull-probe-{r1,stamp,writer}.md`.

**B3, R1/R2 (about 3 h): settled by restatement, no backend change.**
- The first probe proved R1's bridge lemma over a backend fact, `rtHeldDlsLaw` (a held reader misses,
  of the clean view, only entries deleted since the open). True of the Go code, but not provable over
  today's `rtHeld`/`dlsOwn`: a strengthening (`dlsOwn` a half of a ghost map, `dlCov` in `rtCore`) is
  prototyped in `backend/RtHeldDls.lean` and kept only as the recorded alternative: it changes
  client-visible ghost state (the user's) and rebuilds backend and mvcc.
- The cause was a wrong claim in `NewR.lean`'s outline (step 4): `NewStore`'s batch session needs
  no fixed registration (`batchTxInitSpec`, `ForceCommit`; neither names `NC` or `Del`). So
  `NewStore.specR`, `newWatchableStore.specR`, `New.specR` are restated on `store.Restore`'s
  pattern: the session contract `storeSessT` (any `Del`), `restoreRegM d` (unfixed),
  `restoreFixM -∗ storeBackendTR`, the clean read lent `storeRT ∗ restoreRegM d`, i.e. the proved
  `keyCleanRead_of_backendC`; `RC` gone. `ApiNewRestoring.lean` (the API candidate) unchanged.
  Proved: `NewStoreSess.lean`, `NewStoreSessReal.lean` (`storeSessT_of_backendC`),
  `NewStoreLineup.lean` (session → `restore()`'s inputs → the fix). `NewCleanRead.lean` deleted.
- R2 holds under today's contract (the session never takes the client's clean view).
- **For B3's proof:** the fresh proof registers the writer at the session's `Unlock` at `[[],[]]`,
  impossible over an image; B3 leaves the registration pending (`kbRegRight ∗ writerRes`) and builds
  `writerRes` at the restored log after `restore()`, as `store.Restore` does.

**The stamp (about 1.5 h): proved, invariants sufficient.** `stream.recvOne` and the easy companion
`stream.complete`, no `sorry`, no spec or invariant change, no cross-package unfold. Added:
`streamCtx_persistent`. Cleanups for the next edit of shared files: `Persistent` instances for
`isInc`, `ctrInv`, `runnerKeys`, `runnerH`; drop `Streams.lean`'s `maxK_attained` (`maxK_attained'`).

**The writer (round 1): `runner.restart` proved (both members); `restore` two-thirds.** Laws proved:
`memberState_split`, `inc_retire`, `inc_census`, `inc_stop_image`, `inc_alloc`; `RestoreLemmas.lean`
(`restore_au` at the follower's live incarnation, `bnd_acc`), `WriterShares.lean` (`shares_join`,
`shares_split`, the prefix lemmas). Found and fixed (mvccfull files only):
1. mvccrand's duplicate `Countable` instances for `MvccState`/`Change` broke `ghostVar_agree`
   (`attribute [local instance high]`; to do: remove mvccrand's duplicates);
2. `lessorW` could not follow `Recover` to the snapshot's backend: it holds `lessorApplyOk lp` too
   (given by `NewLessor.specR`);
3. `runner.restore.spec` gains `ops.length ≤ Ops`, `Ops < 2^38`;
4. the receipt bound `2^48` → `2^38` in `open`, `newMember`, `restart`, `restore`, `write`
   (`inc_open_backend` needs `receiptBound + k + 4 ≤ 2^40 - 1`).
Cross-package unfolds (each a missing law, the Freeze needs them gone or justified):
`apply.bkRT` (`inc_census`), `backend.bStopView`/`rbOwn` (`inc_stop_image`).
Round 2 (in progress): the rest of `restore` (`Recover`, `KV.Restore`, the old backend's close).
