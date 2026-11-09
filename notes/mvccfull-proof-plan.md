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

The tester calls about 60 mvcc, lessor and backend functions. Against `lean` (`9fd1f8b6`,
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

## Decisions for the user

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
