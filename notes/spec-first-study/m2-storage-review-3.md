# M2, the storage side: review round 3 (2026-10-30)

Reviewed: branch `m2-storage`, commit `8d3a172a18`. This is round 3 for step 1's statements and
round 1 for step 2's (restore in compaction mode).

**Targets**
- Every Draft module: mvcc `M2StorageDraft`, `M2StorageDraftSupply`, `M2StorageDraftRestore`;
  etcdserver `M2StorageDraft`, `M2StorageDraftRestore`; v3rpc; client/v3; cache/v3;
  examples/common, watchkv, linkv3p.
- The internals already switched (`git diff lean...HEAD -- Proof Spec`, the Drafts excluded):
  `writerOwn`/`writerOwn_off`, `bootBackend_of_newPost`'s `fkV`, `InstanceLaws`, and
  `store__Restore`/`NewServer` moved to `writerOwn_off`.
- `notes/m2-storage-plan.md`'s Q2 list (items 1-22), compared with `lean`.

**Method.** I judged against `.claude/skills/spec/PRINCIPLES.md` and `notes/spec-first-plan.md`'s
two tiers, checked against the Go source at the pin (`.lake/go-src/etcd`, `249d76bea7`) and the
callers' proofs. I formed my view before reading rounds 1 and 2.

**What I did not do.** I built nothing and ran nothing. Nothing in the repository changed except
this file.

**Go.** No new Go bug. The liveness bug the step found is real and recorded
(`issues/etcd-restore-pending-compaction-unclosed.md`). The behaviour I checked: `compactBarrier`
returns without `close(ch)` (`kvstore.go:137-154`), and the `Physical` RPC waits only on that
channel (`v3_server.go:402`). One benign corner is noted under S3; I did not file it.

**Abbreviations.** `mvcc/` = `Proof/go_etcd_io/etcd/server/v3/storage/mvcc/`, `etcdserver/` =
`Proof/go_etcd_io/etcd/server/v3/etcdserver/`, `schedule/` = `Proof/go_etcd_io/etcd/pkg/v3/schedule/`.

## The brief's questions, in short

**Is the restorable right sound against Go's order?** Yes, for a job in flight and for queued
jobs. This covers `compactRightR`, `storeStopR`, `storeStopR_reclaim` and `fieldShare_reclaim`.
- **The order.** `Restore` holds `s.mu`, closes `stopc`, then calls `fifoSched.Stop()`. `Stop`
  cancels the context, runs every pending job, then waits for `donec`. Only after that does
  `Restore` write the four fields (`kvstore.go:292-314`, `schedule.go:150-184`).
- **Why the jobs' reads are safe.** A job's `Do` holds `schedRunning`, which is the full
  `dghostVar γ.run 1 ()` (`schedule/Defs.lean:79`). So while any job runs, `storeStopR`'s
  invariant (`M2StorageDraftRestore.lean:108-110`) cannot be in its `schedDoneD` disjunct
  (`schedDoneD_excl`), and the job reads through the eighth.
- **Why the stopper gets the eighth back.** `Stop`'s drafted post returns the run token. The
  stopper swaps it in, which needs no job's cooperation.
- **Recombining.** `fieldShare_reclaim` puts the two eighths back together by `curAt_agree`
  (`:181-197`).
- **`sch` is physical.** It is a field of `PhysNames` (`InvStore.lean:248-260`, `withPhys_sch`), so
  the new scheduler gets fresh names, and the old invariant can keep the old run token forever.
- **Old reads finish before the swap.** Every read of the fields by an old job happens before
  `donec` closes. In `applySnapshot`, `kv.Restore` comes before `s.be = newbe`
  (`server.go:1089-1100`).
- **The old job's batches and the hook.** The old job's batches use `LockOutsideApply`
  (`kvstore_compaction.go:56`), so they never run the post-lock hook after `ci.SetBackend`. Only
  `SetScheduledCompact` uses `LockInsideApply` (`store.go:39`). The new backend's hook is set only
  after `Restore` (`server.go:1093`).
- **Not established: the dead branch.** The design rests on `compactBarrier`'s re-schedule branch
  being dead. The drafted mechanism cannot show this under today's job contract (F2).

**Can `applySnapshot`'s caller meet `Restore.specM`'s premises?**
- *The new backend's stock before `Restore`*: yes (`snap_supply_before`, from the walk's
  `wbInit - 5` fresh tokens; `hrbw` gives `receiptBound ≤ wbInit - 6`).
- *`restoreImageM` (on)*: no. It lacks the two things `restore()` and the new store need (F1).
- *`c ≤ c'`*: not with the drafted vocabulary. `srvKVCloserM s E c` leaves `c` unrelated to the
  applied log, and `keyImageM` is undefined (S1). In one corner the premise is false even under
  Q5 (a)'s argument (S3).

**Do the off-mode laws give back today's statements exactly?**
- *Exactly:* the step-2 laws `store.Restore.spec_of_specM`, `watchableStore.Restore.spec_of_specM`
  (at `c = c' = -1`) and `srvEnvOkD_off` (an iff); `srvKVCloserM_off` up to a `⌜c = -1⌝`.
- *Not as today, and not marked:* `srvWTPoolR` changes in every mode, and its take laws need a
  later credit (S5).
- *Not as today, and documented:* step 1's create token, and `NewServer.spec`'s new `E₀.cmp`
  premise, read differently off (round 2 accepted the price).

**Is anything vacuous?** No. The disjunctions (`storeStopR`, `wsWatchFrozen`) are invariants, not
guarantees to callers, and each side is reachable. `noCompactor` cannot be made in compaction mode,
because the authority's other half is the right's.

**Is the Q2 list complete?** No. Six statements the switch changes are missing (S2), and items 15,
16 and 19 are not final (F1, F2).

## First tier

### F1. `Restore.specM` in compaction mode: the image premise does not fix `c'`, and it gives no write right for the new store's compaction keys. The statement is false as written.

Today's off branch hands `restore()` `kbNoCmp (some d') γb'`. The drafted on branch,
`mvcc.restoreImageM` (`M2StorageDraftRestore.lean:256-261`), hands it only three things: a view of
the `Key` bucket (`kbViewC`), the bit `fkV d'.γB true`, and pure facts relating `c'` to the log
(`imageAt L c' m`, `NoDelPutAt L c'`, `c' < |L|`). Two things are missing.

**1. Nothing ties `c'` to the image's `Meta` records, which is what Go reads.**
- `restore()` sets `compactMainRev := finishedCompactRev` (if found; `kvstore.go:330-333`). It then
  resumes `scheduledCompactRev` when that is larger and non-zero (`:342`, `:389-411`), and
  `updateCompactRev` sets `compactMainRev` to it.
- The store's invariant ties the physical value to the logical authority:
  `revMuBody`'s `compactMainRev ↦ c ∗ crevUB γ.idx ¼ c` (`InvStore.lean:2770-2771`).
- The post's `restoreRightPostM … c'` gives the right at `c'`, so the post forces
  `compactMainRev = c'` after `Restore`.
- But `c'` is the caller's choice, constrained only by the pure facts.
- **Counterexample.** Take an image with no compaction record and the full bucket
  (`imageAt_full`), `c = -1`, `c' = 0`; `NoDelPutAt L 0` holds because revision 0 of
  `[[], []] ++ R` is empty. The premises hold. The post claims the compaction revision is 0, but Go
  leaves `compactMainRev = -1`.
- The converse also fails: an image recording `finishedCompactRev = 5`, with `c' = -1` chosen.
- The vocabulary cannot say it today. The backend's flag records only "none / some" (`fkInit D` is
  0 or 1, `backend/Model2.lean:433`), and `bridgeParams` hides `Meta` from the view (`Image.lean`'s
  header).
- The plan's `keyImageM` ("its meta records with that revision") is at the D22 level, on the data
  `D`. Nothing carries it into the store's spec.

**2. No compaction-key write right for the new backend.**
- In compaction mode the new store's `physCmp` needs `mwInv`, which holds `kbMW (some d') γb'`
  (`physCmp_allocD`, `M2StorageDraftSupply.lean:94`; `mwInv`, `InvStore.lean:2397`).
- `restore()`'s resumed `updateCompactRev` writes `scheduledCompactRev` through it.
- Off, the right comes from `kbNoCmp`, which `restore` returns as `kbMW` (`store__restore.lean`'s
  post).
- On, `restoreImageM` has no `fkOwn d'.γB _`. The walk does hold it, from `OpenBackend`'s
  `fkCl γB P D` (`fkCl_wf`), but the spec never asks for it.

**Who is affected:** items 15 and 16 of the Q2 list, and D22's walk (`SnapApplyWalk.lean:391-400`,
which must build the premise).

**What the plan says.** It does call `store.restore.spec`'s generalization "the first thing to
design before `Restore.specM` can be proved". But items 15 and 16 present `Restore.specM`'s text
for approval, and it is its pre that is wrong, not only the trusted callee's.

**Restatement.** `restoreImageM`'s on branch should carry:
- the client's half of the flag, `backend.fkOwn d'.γB (fkInit D)` (or `kbMW (some d') γb'`);
- a statement of the two records, with `c'` defined as `restore()` computes it:
  `c' = max(fin or -1, sched if sched ≠ 0)`.

That needs a backend-level fact about `Meta`'s two keys, given by the opener over `D` (beside
`fkCl`), and the walk would derive it from `keyImageM`. Hold items 15, 16 and 18 together until
`store.restore`'s generalization is designed; its pre decides this text.

### F2. Q6's drafted mechanism cannot reach the barrier under today's job contract. Item 19 understates the change, and it touches the server's `run`.

Without `schedLive`, `compactBarrier`'s re-schedule branch must be shown dead:
- A job reaches that branch when it sees its context cancelled while `stopc` is open
  (`kvstore.go:138-150`). The branch takes `s.mu` and calls an untracked `Schedule`, which needs
  `schedLive`.
- The plan says `Stop` takes a persistent payload ("stop channel closed") that "a job finding its
  context cancelled learns".
- But a job's contract quantifies over every context:
  `jobDoSpec γ jt Pre Prev Post := □ ∀ ctx cd, {{ schedRunning γ ∗ Pre ∗ Prev ∗ isContext ctx cd }} …`
  (`schedule/Defs.lean:150-156`).
- A job that observes `ctx.Err() ≠ nil` learns `ContextClosed cd.Done_gn` for an arbitrary `cd`,
  which nothing relates to the scheduler's context or to `Stop`'s payload.
- So the payload can reach the job only if the job contract changes. Either `jobDoSpec` takes the
  scheduler's context description (or a `□ (cancelled → payload)` row keyed by `γ`), or
  `schedRunning` carries it. The payload must also be fixed where the context is created
  (`NewFIFOScheduler`), or recorded in `isFifo`.

**Who is affected:**
- `schedule.jobIs`/`jobDoSpec`, `NewJob.spec`, `Scheduler.Schedule.spec`, probably
  `NewFIFOScheduler.spec`.
- Their callers outside mvcc: the server's apply loop uses `jobIs` (`EtcdServer__run.lean`, the
  module that holds SNAPSHOT-SORRY #8).

Item 19 lists only `Stop.spec` and `fifo.Stop`. The design itself is sound in Go (Restore and
Close close `stopc` before `Stop`). The statement list is what is incomplete, and as listed the
barrier's proof cannot be done.

**Restatement.** Item 19 should read: "`Scheduler.Stop.spec`: the post gains `schedDoneD γ`;
`NewFIFOScheduler.spec` fixes the cancellation payload (`□ Pay`, persistent), which `Stop` takes;
`jobDoSpec`/`jobIs` give a job the scheduler's context, so that `ctx.Err() ≠ nil` yields `Pay`;
`NewJob`/`Schedule` follow; `run`'s jobs ignore it."

Two alternatives:
- Keep untracked barriers out of `compactBarrier`'s cancelled path by changing what the barrier
  job's `Pre` carries. As far as I can see, that also needs the context tied.
- Say why a job can learn the payload without it.

## Second tier

### S1. `c ≤ c'` has no source at SNAPSHOT-SORRY #8, and the drafted vocabulary does not prepare one

- `specSnap`'s new premises `hcc : c ≤ c'` and `hkI : keyImageM …` are discharged by `run`'s
  snapshot job (`EtcdServer__run.lean:811`, `:1332`).
- `srvKVCloserM s E c` (`etcdserver/M2StorageDraftRestore.lean:257`) takes `c` as a free parameter.
  Only the right's authority pins it, and nothing in the server's state relates it to the applied
  entries.
- `keyImageM` is undefined, and item 21 names it in `specSnap`'s text.
- The plan calls this "the apply side's obligation, as `L <+: L'`". But `L <+: L'` has a source
  (`x.log` in `srvApplyKV`, the KV model `kvRaftOf`), and `c` has none.
- Today, with no compaction arm, `c` stays `-1` until the first install. After it, `c` becomes that
  image's `c'`, and the second install needs `c'₁ ≤ c'₂`. This is monotonicity of the images'
  revisions in the snapshot index, which only a model of the log's compaction revision gives.

**Restatement.**
- Define the KV model's compaction revision `crevOf` of an applied prefix.
- Hold the closer at it in `run`'s state (`srvKVCloserM s E (crevOf A)`).
- Define `keyImageM d.cm R c' D` with `c' = crevOf A'` (S-j1's, beside `hA'`).
- Then `hcc` is a lemma, `crevOf_mono`.

This is planned work (Q5 (a)), but the statements should name the link now: a free `c` is how the
compaction revision got lost from the KV model in the first place.

### S2. The Q2 list omits statements the switch changes

1. **`store.Compact.spec` / `mvcc_store_Compact` (item 17):** the pre also loses
   `mvcc.storeStop s γ` (`Spec/.../store__Compact.lean:73`). `storeStop` discards a `curAt`
   fraction, which `Restore` can then never gather. The same goes for `updateCompactRev` and
   `compactLockfree`. The plan's prose says "`storeStop` and `schedLive` go", but the item does not.
2. **`mvcc_NewStore_backend_cmp`'s post** (exported, `mvcc/Results.lean:367`): becomes
   `compactRightR s γ (-1)` instead of `compactRight γ (-1) ∗ storeStop s γ`. Item 5 lists only its
   pre. Its docstring's route to the reader's token (`storeStop_open`'s discarded `curAt`, `:329-332`)
   becomes the `fieldShare` quarter's own `curAt` (`storeReader_retire` takes any `dq`).
3. **`schedule`'s job contract** (F2).
4. **`store.Close.spec`.** The plan says "the same holds for `Close`, so Q3 dissolves". But
   `Close.spec` takes `storeCloser`, whose queue is at `-1`, and `compactQueue_mono` only goes up. A
   compacting store at `c > -1` cannot meet it. Q3 dissolves only after `Close.spec` takes the
   closer at `c` (or `restoreRightM`). This is unreachable today (`run` never returns); say so
   instead of "dissolves".
5. **`mvcc.isWatchableStore_withPhys`** (`etcdserver/RestorePre.lean:101-104`) is proved by `rfl`
   and used by `rw` in D22's walk (`SnapApplyKVLemmas.lean:113`, `SnapApplyOptsLemmas.lean:213`).
   - Step 1's redefinition makes `Hfrz` read `wsFrozenM γ.st`, i.e. `kbCmpM γ.st.kb`, and `kb` is a
     physical name (`withPhys` sets it).
   - The equation then holds only under `kbCmpM p.kb ↔ kbCmpM γ.st.kb`: a conditional law, and two
     walk sites must supply `d'.cm = d.cm`.
   - Neither the switch's cost list nor item 6/21 names it.
   - Option: a logical mode field in `StoreNames` (set by `NewStore`, kept by `withPhys`) for the
     gated predicates to read. Then every `withPhys` law stays `rfl`, and `d'.cm = d.cm` is needed
     only where the backend record is built.
6. **Items 6 and 20 overlap.** Item 6 still lists `compactRight_of_wsCloser` as a new exported name,
   and item 20 replaces it with `wsCloserR_of_wsCloser`. Consolidate: drop it from item 6, and from
   the step-1 Draft (`mvcc/M2StorageDraft.lean:277-285`).

### S3. A reachable corner where Q5 (a)'s premise is false: a scheduled, unfinished compaction at revision 0

- `restore()` treats `scheduledCompactRev = 0` as absent (`kvstore.go:342`, `:389`, `:411`). An
  image with `scheduled = 0` and no finished record restores to `compactMainRev = -1`.
- A follower that applied `Compact(0)` itself has `c = 0`, so `c ≤ c'` fails if `c'` is defined as
  `restore()` computes it (which F1 needs).
- `Compact(0)` is accepted by the store (`updateCompactRev`: `0 > -1`) and by the RPC path
  (`key.go:139`, no check). The auto-compactors never issue it (`v3compactor/revision.go:82`
  `rev <= 0`; the periodic one takes `rg.Rev() ≥ 1`).
- Physically harmless, since compaction at 0 deletes nothing. Not filed.

**Restatement.** Either the model's `crevOf` counts a compaction at 0 as none, or the compaction arm
excludes `rev = 0` (a premise from the compactor). State which in the Q5 (a) text.

### S4. The jobs' share holds `∃ o`, not a pinned `o`: a proof risk in re-proving the chain (uncertain)

- Today's `storeStop` gives the job one discarded `curAt γ □ o`.
- `storeStopR`'s invariant gives, at each opening, *some* `o` with `fieldShareAt s γ q8 o`, and the
  job holds no fraction to relate two openings.
- `scheduleCompaction` reads `s.b` several times (`LockForSafeRangeDelete`, `BatchTx` per batch,
  `Unlock…`, `Size`). It must use each read's own `physOk` facts, which are by ghost names (so
  likely enough), and never equate the objects.
- I did not check that every step of today's `scheduleCompaction` proof survives this.
- A cheap fallback: a persistent pin of the objects keyed by the physical names (sound, because
  `Restore` allocates fresh `PhysNames`), e.g. S3-S5b's `objsPin` re-keyed by `γ.phys`.

### S5. `srvWTPoolR` changes the off server's statements

- Q4 (a)'s stock is sound. Each take raises the shared counter, and a stock's lower bound keeps
  `receiptBound ≤ m + n + 1` (`srvWTStock_take`, `:92-116`, checked).
- But it moves the off server's tokens too, and every take law needs `£ 1`. This affects
  `specSnap`'s `srvWTPool` and D22's eight take sites in every mode.
- That is a fair cost, but the plan's "compaction-off statements read as today" does not hold for
  item 21. Say so there.

**Missing law.** `kbWTSupplyM_of_stock` needs `srvWTStockInv γp d` for the current backend, which
sits under the pool's `▷`. The compaction arm will need
`srvWTPoolR E γp ∗ srvBeOwn s E ∗ £ 1 ={⊤}=∗ srvBeOwn s E ∗ mvcc.kbWTSupplyM E.γ.kb`
(as `srvWTPoolR_take_extra_d` does for a token). Add it; it is item 20's real source.

### S6. Stale rationale and references (docstrings that now say something false)

- `mvcc.wsFrozenM` (`mvcc/M2StorageDraft.lean:74-80`): "no restore in compaction mode, so it never
  changes". It now holds by `d'.cm = d.cm`, and `γs.kb` is a physical name (S2.5).
- `compactRight_of_wsCloser`'s docstring ("a compacting store is never closed") contradicts step 2.
  So do `crevRightM`'s and `New.specD`'s references to it (`:91`, `:350`) and the etcdserver Draft's
  header (`:15`).
- `store.Compact.specD`'s supply paragraph names `kbWTSupplyM_of_srvBeOwnD` (F2's, withdrawn;
  `M2StorageDraftSupply.lean:191`). It should name `kbWTSupplyM_of_stock`.
- `writerOwn_off`'s and `writerOwn`'s docstrings (`InvStore.lean`, switched): "`store.Restore`,
  never in compaction mode, sees `2`". `kbCmpM`'s docstring ("`false` for D22's received backends,
  'no restore in compaction mode'") is stale too, on `lean`.

### S7. Abstraction and unfolds

- `restorePre_of_applyM` adds an unfold of mvcc's `isWatchableStore` (to get `Hfrz`,
  `etcdserver/M2StorageDraftRestore.lean:338`). The law exists (`isWatchableStoreD_frozen`); use it,
  or today's-predicate twin `isWatchableStore_frozen`. Its other unfolds (`apply.kvOwn`,
  `txn.kvWriter`, …) are inherited.
- `compactRightR`, `storeCloserR`, `storeStopR`, `q8` and `wsCloserR` become exported mvcc names
  that the server holds in `srvKVCloserM`. Clients use only `wsCloserR_split/_join`,
  `restoreRightM_on/_off` and `restoreRightPostM_on/_off`, so seal the bodies (`@[no_expose]`).
- `mvcc.imageAt` shares its short name with etcdserver's `imageAt` (`InvImage.lean:91`). Rename it
  (`bucketThinnedAt`).

## Rounds 1 and 2: status at `8d3a172a18`

| Finding | Status |
|---|---|
| R1 F1 (where "no watchers in compaction mode" is enforced) | Resolved (the create token, `noCompactor`). |
| R1 F2 (the supply's server source) | Superseded twice: `srvBeOwnD` (round 1's repair) was withdrawn with P4; now `kbWTSupplyM_of_stock` (Q4 (a)). The arm's actual law is missing (S5). |
| R1 S1-S10 | Resolved as round 2 recorded; S9's docstring is stale again (S6). |
| R2 N1 (the mode's route to the watching examples) | Resolved as a draft: `AEnv.cmp`, `envAgreeD`'s mode clause, `memberBootD`, `isWatchServerD_noCompactor(_env)`, the three examples' glue. Its vehicle differs from round 2's suggestion (a field on the stand-in rather than a pure fact in `memberBuilt`), which round 2 left open; it keeps `memberBuilt`/`memberUp` unchanged. |
| R2 S1', S2' | Moot (F2 withdrawn). |
| R2 S3' (positional destructuring) | Resolved (appended last; projections `watchMemberFactsD_noCompactor/_kv/_st`). |
| R2 S4' (`crevFrozen` in client contracts) | Resolved (`noCompactor`, sealed). |
| R2 S5' (two readings of the mode) | Resolved for step 1 (`envAgreeD`'s clause; `srvEnvOkD_mode_step` keeps it across an install). Reopened in a new form by step 2: `wsFrozenM` reads a physical name (S2.5). |
| R2 S6' | Mostly resolved: `txn.storeWTs_someD` added; `createArm_T` kept, marked Draft-only. The `backend.wbTok` unfold is kept (a kernel recursion problem, recorded). |
| R2's uncertain `srv_be_swap` / no-snapshot question | Moot (restore works in compaction mode). |

**Churn.**
- **The supply's server source** has moved three times: `kbWTSupplyM_of_srvWTPool` with a
  discarded `E.γbe` part, then F2's frozen `srvBeOwnD`, then Q4's stocks. Each move followed a user
  decision (P4 withdrawn), not a reviewer reversal.
- **The compaction right** has moved twice: discard-based `compactRight_of_wsCloser`, then step 2's
  `wsCloserR_of_wsCloser`. The Q2 list still lists both (S2.6).
- **No finding of rounds 1-2 was reversed by this round.**
- **The underlying cause.** Step 1's mode-gated predicates were designed under "no restore in
  compaction mode". Step 2 now has to re-justify them (S2.5, S6). Fixing the mode in the logical
  names once would stop this class of churn.

## Per target

**mvcc `M2StorageDraftRestore`** (`compactRightR`, `storeStopR`, the reclaim laws, the `…M` predicates, `Restore.specM`s, `wsCloserR`)
- Good:
  - It removes P4's root cause (discard) with a split.
  - The reclaim needs no job's cooperation.
  - Every law is proved, with no `sorry`.
  - The off laws are exact.
  - `d'.cm = d.cm` replaces two `cm = false` premises with the right invariant.
- Findings: F1, S2.4, S4, S7.

**schedule (drafted in prose: `Stop` returns the run token, a payload, tracked barriers)**
- Good: the run-token swap is the right primitive (`schedDoneD_excl`).
- Findings: F2.

**etcdserver `M2StorageDraftRestore`** (`srvWTStockInv`, `srvWTPoolR`, the take laws, `srv_be_swapR`, `srvEnvOkD`, `srvKVCloserM`, `restorePre_of_applyM`, `snap_*`)
- Good:
  - Q4 (a) is sound and minimal: no token doubling, and the swap still gathers all of `E.γbe`.
  - Dropping the old tokens from the swap matches the walk, which discarded them anyway
    (`SnapApplyWalk.lean:461-462`).
  - `restorePre_of_applyM` closes D22's `sorry`.
  - `snap_closer_after` composes in either mode.
- Findings: S1, S3, S5, S7.

**mvcc `M2StorageDraft`** (step 1)
- Good: as round 2 found. `noCompactor` is sealed with the laws its clients need.
- Findings: S2.5, S2.6, S6.

**`M2StorageDraftSupply`**
- Good: the chain is proved and linked against the drafted specs.
- Findings: S2.1 (step 2's further change to the same statements), S6.

**etcdserver `M2StorageDraft`, v3rpc, client, cache, examples (common, watchkv, linkv3p)** (N1)
- Good:
  - Each change is a one-arm or one-conjunct change, appended.
  - The mode reaches the examples through what they already hold (`envAgree E E₀`).
  - Clients take `noCompactor` through v3rpc laws, without unfolding.
  - `memberBuilt`/`memberUp` keep their texts.
- Findings: none new beyond item 11's `E₀.cmp` premise. It is a mode selector, recorded as a change
  to an off statement.

**Switched internals** (`writerOwn` at `2 + nJobRd`, `writerOwn_off`, `fkV` from boot, `InstanceLaws`)
- Good: correct, and consistent with step 2 (`Restore.specM`'s post at `γ.withPhys p'` keeps
  `nJobRd` by `d'.cm = d.cm`).
- Findings: S6 (docstrings). `kbWTSupplyM_alloc` still has no caller.

## Ranked by need of revision

1. **mvcc `M2StorageDraftRestore`'s `Restore.specM` / `restoreImageM`** (F1): hold items 15, 16 and
   18 until `store.restore`'s generalization fixes the pre.
2. **The `schedule` changes (item 19)** (F2), with S2.1-S2.4 for the compaction chain's list.
3. **etcdserver `M2StorageDraftRestore`**: S1 (`c`'s source), S3, S5 (the missing supply law; the
   off-mode change stated), S7.
4. **mvcc `M2StorageDraft`**: S2.5 (`isWatchableStore_withPhys`), S2.6, S6.
5. **`M2StorageDraftSupply`**: S6's docstring.
6. **The switched internals**: S6's docstrings.
7. **N1's drafts** (etcdserver `M2StorageDraft`, v3rpc, client, cache, examples): no change needed.
