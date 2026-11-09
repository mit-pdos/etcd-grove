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
