# F-raft-storage: re-review of raft, the storage backend and schema, and bbolt (2026-11-09)

Reviewer: fresh and independent, read-only. HEAD `7394a3ca7e`. Regressions are checked against
`41c6c3a39f`. Go: `.lake/src/{raft,server,bbolt}`. I wrote the verdicts on N3, S-e, NR1 and NR2
before reading `repair2-raft.md`, `repair2-crash.md`, `repair3-boot.md` (items 6-7) and `cleanup.md`.
Reading them afterwards changed no verdict.

`etc/lean-check.py -a` reports 0 errors on these files:
- raft: `Api.lean`, `raft__hasUnappliedConfChanges.lean`;
- backend: `Api.lean`, `Durable.lean`, `New.lean`, `backend__Close.lean`;
- bbolt: `Open.lean`.

The proof of F1 below was checked by Lean, from a scratch file outside the repository
(`/tmp/rvchk/Eta2.lean`, run with `lake env lean`).

## Verdicts

| batch | verdict | why |
|---|---|---|
| **R1** (raft node API: `Api.lean`, `Model.lean`) | **FAIL** | **F1.** `raftState_gen.spec`, together with `exclusive.spec`, proves `raftState γ id D ∗ crashed ⊢ |={⊤}=> False`. Every crash frame becomes trivially provable. `raftState_crash.spec` has the same form. Apart from F1, the batch has open decisions only: 2.8 (`crashScopeOk`/`confAboveOk`), C33, C34, 5.1. |
| **R2** (raft core: `ApiCore`, `raft.go`) | **PASS WITH OPEN DECISIONS** | N3 and S-e are resolved. The open decisions are 2.1, 2.2 (`ConfigOk`), C32 (`coreIdle`) and 5.1 (the term/index bound). |
| **R3** (raftlog snippets) | **PASS WITH OPEN DECISIONS** | NR1 is resolved. The second-tier laws line is also fixed. R3's earlier open decisions are unchanged. |
| **4a** (storage backend) | **PASS WITH OPEN DECISIONS** | NR2 is resolved. `beOpenUpd` and `beCloseUpd` close against 4c's `Open`, `DB.Close`, `boltRelease` and `fileHolds_alloc`, with one exception: F2. `backend.Close.spec` cannot be proved when the file was created in the same generation. This is a recorded gap (top.md K6, `backend__Close.lean`), but it has no entry in `open-questions.md`. Other open decisions: C2, C42/C43 (rename, directory sync), 4.1/4c-D1. |
| **4b** (schema) | **PASS** (no change) | No schema file changed since `41c6c3a39f`, and none cites a changed backend law (`beNew`, `beHist`, `beFile`, `beOpenUpd`, `beCloseUpd`: grep). The mvcc and lease/auth specs cite none of them either. |
| **4c** (bbolt) | **PASS WITH OPEN DECISIONS** | Only `Open.lean`'s header changed (the client note). The `emp` branch is right for etcd. Open decisions: 4.1 (4c-D1), C2, C42/C43, C48 (`ForEachBucket.spec_del`). |

## Findings rechecked

| finding | status | evidence at HEAD |
|---|---|---|
| **N3** (RR-raft-core) `hasUnappliedConfChanges` panics with a snapshot pending | **Resolved** | The premise is now `⌜o.log.us.snap = none ∧ o.log.compactFloor ≤ o.log.applied⌝` (`raft__hasUnappliedConfChanges.lean:33`). With `snap = none`, `Wf` gives `lastIndex ≥ committed`, so `scan`'s `hi ≤ lastIndex + 1` holds. The only caller is `hup` (`raft.go:1001`), which calls it only after `promotable()` (`raft.go:997`). `promotable`'s spec gives `o.log.us.snap = none` from `!hasNextOrInProgressSnapshot()` (`raft.go:1949`; `log.go:288-290`: `unstable.snapshot != nil`). `hup`'s sketch says this (`raft__hup.lean:10-12`). |
| **S-e** (RR-raft-core) `base ≤ applied` without a source | **Resolved** | `coreIdle_floor`'s conclusion now also gives `us.snap = none → base ≤ applied` (`ApiCore.lean:678-681`). This is true of Go at every step boundary (details below). |
| **NR1** (RR-raftlog-bbolt) `ReqCompactApplied` lacks `applied ≥ base` | **Resolved** | `ready.go:70-76`: Assumes now has "applied >= the log's base … so compactFloor is the applied index", and the laws line now lists `raftLog_publish` and `logFloor_stored`. One aside about NR1's own premise: `stableSnapTo` runs only inside `appliedSnap` (`raft.go:766-769`, called at `:1197`, `:1220` on `MsgStorageAppendResp`), so "applied lags base after stableSnapTo" happens only inside one step. The Assumes line ("outside appliedSnap") is right. |
| **NR2** (RR-raftlog-bbolt) `boltOpenOptions_init` stated `NoFreelistSync` off | **Resolved** | `Durable.lean:185`: `{ OptsM.dflt with mmapFlags := …, noFreelistSync := true }`. This matches `config_linux.go` (`MmapFlags: syscall.MAP_POPULATE, NoFreelistSync: true`), and the docstring is updated. `newBackend` copies `*boltOpenOptions` and does not touch the field (`backend.go:216-231`). So `Open`'s update slot is `emp` for `New`, for defrag's reopen (`b.bopts`) and for `createDefragTmpDB` (`options := *b.bopts`). Go agrees: the freelist commit is guarded by `!db.NoFreelistSync` (`bbolt/db.go:319-334`). |

Why S-e's law holds in Go:
- `newLogWithSize` sets `applied = base`.
- `RestartNode`'s `Config.Applied` only raises `applied`.
- `appliedTo` is monotone (`max`, `raft.go:739`).
- `appliedSnap` runs `stableSnapTo(s.index)` and then `appliedTo(s.index)` in one step. When a newer snapshot is pending, `stableSnapTo` does nothing (`log_unstable.go:185-190`), so `snap` stays `some` and the implication is vacuous.

## New first-tier findings

### F1. `Raft.raftState_gen.spec` (and `raftState_crash.spec`) at the current generation: a second `nodeVacant`, hence `False`

**Location:** `SpecPlan/Spec/go_etcd_io/raft/v3/Api.lean:956-960` (`raftState_gen`), `:983-989` (`raftState_crash`).

**Principle:** Sound (no way to prove `False`); a premise stated with a ∀ must be checked against the instances it does not pin down.

**The step.**
1. Both laws quantify over every `L' : GooseLocalGS GF`, including `L' := hG.goose_localGS`.
2. `HeapGS` is a structure with exactly the fields `goose_globalGS` and `goose_localGS` (Perennial `GooseLang/Lifting.lean:707-709`). By structure eta, `⟨hG.goose_globalGS, hG.goose_localGS⟩` is definitionally `hG`.
3. So that instance of `raftState_gen` reads `raftState γ id D ∗ crashed ⊢ |={⊤}=> raftState γ id D ∗ nodeVacant γ id`, all at one heap.
4. `crashed` is persistent (`CrashToken.lean:41`). The law can therefore be applied twice, which gives two `nodeVacant γ id`. `exclusive.spec` (`Api.lean:592`) refutes two.

Lean accepts the derivation:

```lean
theorem rv_false (h : raftState_gen.spec (GF := GF)) (hx : exclusive.spec (GF := GF)) :
    ∀ γ id D, raftState (GF := GF) γ id D ∗ crashed ⊢ |={⊤}=> iprop(False)
```

**Why it matters.** Perennial's crash frame (`CrashAdequacy.lean:330-332`, `:457-459`) is `∀ L', crashed -∗ extsCrashStart hG L' -∗ … ={⊤}=∗ P L'`, and it hands `crashed` to the proof of every instance.
- A client holding any `raftState` (every member's disk does: `diskState`'s `.member` realization; `cluster_alloc` gives one per voter) can derive `False` inside the frame for the *real* `L'`, by applying `raftState_gen` at `L'' := hG.goose_localGS`.
- This proves any `P L'`, so every crash/restart result above raft (W0's adequacy, `disk_crash`, `ReqCrashRecover`) is vacuous.
- Equivalently, the law cannot be realized. The stated realization ("a ghost map keyed by `(id, generation name)`, an entry inserted once", `:902-905`) cannot insert `(id, g)` again when `L'`'s crash name is `hG`'s. The client may still hold the entry already handed out.

**Why the neighbours are fine.** 4a's `beCrash`/`beFile_crash`, 4c's `boltCrash`, `disk_crash` and `dataDirFresh_crash` are guarded by OsFs's linear `crashRest (gooseOsGS hG) (gooseOsGS L') Ps`, which only `extsCrashStart hG L'` gives for the `L'` being proved. `walRecs_crash` consumes what it returns and mints nothing. Raft's two laws are the only crossing laws that mint an exclusive token with no guard.

**Affects:** every caller of the crossing:
- 2e's `disk_crash` realization;
- `memberBoot_crash` and `memberJoin_crash` (`ApiBoot.lean:694-720`), whose realizations rest on `raftState_gen`;
- W0's restart story (top.md K6).

**Suggested fix (one of these).**
- (a) **Make the crossing consume an exclusive witness of the old generation's occupancy instead of minting.** For example: `raftState γ id D ∗ (nodeVacant γ id ∨ ∃ n, isNode n γ id ∗ nodeRunning n 1) ∗ crashed ⊢ |={⊤}=> raftState@L' γ id D ∗ nodeVacant@L' γ id` (and the same for `raftState_crash`).
  - At `L' = hG` this is harmless: it only turns a running node's whole token into a vacancy, in a generation that can no longer step.
  - The client then keeps `nodeRunning n 1` (or the vacancy) in its crash invariant. The disk's realization would hold it beside `raftState`. This falls under the recorded frame-extraction gap.
- (b) **Take a premise that `L'` is another generation**, `⌜L'.goose_crashGS.crashName ≠ hG.goose_localGS.goose_crashGS.crashName⌝`.
  - That premise suffices: a second application needs the new name's `crashed`.
  - The frame cannot establish it today. It needs a Perennial change: the crash rule hands the frame a freshness fact or token for `L'`, which is true because `crashToken_init` allocates a fresh name. Record it in `notes/perennial-changes.md`.

  With either fix, rewrite the realization text at `:902-905`.

### F2. `backend.Close.spec` cannot be proved when the file was created in this generation (a recorded gap, not an open question)

**Location:** `SpecPlan/Spec/go_etcd_io/etcd/server/v3/storage/backend/backend__Close.lean:70-80`; `Api.lean:685-688` (`beCloseUpd`'s `COMM` needs `beFile p (some I)`).

**Principle:** Sound (a reachable input with no proof). An unsound candidate is replaced by a true one, not left standing.

**The step.**
1. `beFile p (some I)` is realized as 4c's `fileHolds p D`, which needs the name durable (`fileHolds_image`: `m.named = true`, bbolt `Api.lean:581-586`).
2. A backend started from `beFile p none` gets `BoltSt.fresh` through `boltFresh_alloc` (`named = false`). This is etcd's first boot's `member/snap/db`: `bolt.Open` creates it with `O_CREATE`, and the directory is never fsynced.
3. After `DB.Close`, `boltRelease` gives `osMeta` only with `σ.named = true → m.named = true` (bbolt `Api.lean:614`). So `beCloseUpd`'s `COMM` has no source.
4. `beFile_crash` (`Durable.lean:162-171`) cannot absorb a weaker realization either. Its post allows only `o' = o ∨ o' ∈ os`, not "gone", and a crash can lose an unnamed file.

**Who is affected.**
- The file says this itself ("Not fixed (recorded)"), as do `repair3-boot.md` item 7(a) and top.md K6. It is pre-existing (the old post had it), but it is not in `open-questions.md`: C2 covers bbolt's model, not 4a's `Close`.
- 2e's `bootstrapped*.Close` and `srvClosed`: a first boot followed by a stop.
- The snippet `ReqReopen` (`examples/specreq/backend/commit.go:12-44`), whose Assumes does not exclude a fresh path.

**Suggested fix.**
- Record the gap as an open question.
- Or give `beFile` the name state: `beFile p o` realized by `fileHolds` or by the unnamed closed form. Then `beFile_crash`'s post becomes `o' = o ∨ o' ∈ os ∨ (o' = none ∧ ¬named)`, through a `named` flag or a separate `beFileFresh` predicate, the way `beCrash` already has `o = none ∧ Image.empty ∈ L`.
- Meanwhile, add to `ReqReopen`'s Assumes: "the file at `path` exists with a durable name (`beFile_of`)".

## Regressions (files changed since `41c6c3a39f`)

### raft

**`Api.lean`: the crash section, `global.spec`, `Durable.crashOk`, `raftState_gen`, `raftState_crash`.**

`global.spec` (`:935-949`):
- It is realizable. Each listed predicate (`committedLb`/`Ops`, `confAt`/`Decisions`/`Decided`, `snapsMade`, `snapValid`, `readCtxs`, `readCtx`, `readState`, `msgSent`, `msgCredit`, `freshIds`, `bootLog`) can be built from `GooseGlobalGS` alone: invariants, `AllG` ghost state, and the later credits in `InvGS_gen` (`Lifting.lean:671-684`).
- It is not vacuous. It leaves the exclusive ones exclusive at each generation.
- Combining it with `freshIds_take` at `L'` gives only fresh ids.

`crashOk` (`:925-933`) is true of the WAL's replay:
- Records are written as entries, then the state record, then one fsync, and a crash leaves a prefix. `Save` (`etcdserver/raft.go:264`) comes after `SaveSnap` (`:257`, `wal.SaveSnapshot`).
- The old record with `j` entries: `hs.commit ≤ D.commit < entsFrom`, by `BatchOk`.
- The batch record with everything written: `D.next b` at its commit.
- For a snapshot batch, the cases are nothing written (`j = 0`) or all of it. The snapshot-record-only case is `crashScopeOk`'s (2.8).
- `raftState_gen` at rest keeps `D`. `StorageHolds` lets a restart see any commit in `[wcommit, commit]` (`Model.lean:275-283`), which covers a lost commit-only state record.

Is `nodeVacant` exclusive across generations?
- At distinct crash names, yes: a crossing consumes `raftState`, which is exclusive.
- At `L' = hG`, no: that is F1.

**`ApiCore.lean`:** `coreIdle_floor` (S-e). It is true at step boundaries (above). It is unused at `appliedSnap`'s mid-step state, which the invariant does not cover.

**`ApiLog.lean`:** the `logFloor_mono` gloss only.

**`Model.lean`:** `Durable.crashed`'s docstring only.

**`raft__hasUnappliedConfChanges.lean`, `raft__hup.lean`:** N3 (above).

### backend (4a)

**`Api.lean`: `beFileN`, `beOpenUpd`, `beCloseUpd`, and `beNew` without `beHist`.**
- `beOpenUpd`'s mask `⊤ \ ↑beFileN, ∅` lets the client's crash-state invariant sit outside the backend's file invariants. A client with no invariant builds the update from the `beFile` it owns (`R γ := COMM`'s resources), and the snippets `commit.go`/`more.go` say so.
- No consumer outside 4a used `beNew`'s `beHist` (grep): the only remaining `beNew` users are `OpenBackend` and `OpenSnapshotBackend`, which pass `R γ` on.

**`New.lean` / `newBackend.lean`.** They close:
1. A ghost step before `bolt.Open` (`backend.go:233`) runs `fileHolds_alloc` or `boltFresh_alloc` on the update's `beFile` (in `beFileN`), allocates the history and its authority, and commits `beDurInv ∗ beSynced? ∗ beHist γ [o.getD empty]`.
2. 4c's `Open` takes `boltFile γ ∗ boltClosed γ` with `NoFreelistSync` on (the `emp` slot, NR2). On success it gives `isBolt ∗ boltOpened`. Its error is excluded by `dbOpenOk`; Go panics there (`:234-236`).
3. A crash before the update finds `beFile` (`beFile_crash`); a crash after it finds the open form (`beCrash`).
4. Under `UnsafeNoFsync`, `beSynced` is missing and `beCrash` does not apply. This is a stated mode, and 2e's `diskCfgOk` excludes it.

**`backend__Close.lean`.** It closes, except for F2:
1. `close(stopc)`, `<-donec`, then `db.Close()`, which gives `boltClosed γ` whatever the error (bbolt `DB__Close.lean`, `tok = true`).
2. Firing `beCloseUpd` releases the history authority's share, which makes `boltState γ 1`.
3. `boltRelease` then gives clean, durable bytes. Its premises hold: `dur = some []`, because a failed backend commit is `lg.Fatal`, and `busy = false`.
4. `fileHolds_image` gives `beFile p (some I)` only if the name is durable: F2.

**`Durable.lean`.**
- `beFile_crash`: plausible from `fileHolds` (every byte clean, the name durable) and `beFile_none`. It is guarded by `crashRest` (`p ∉ Ps`). Its revert case is the recorded OsFs rename gap (C42/C43).
- `beRevs`, the list form: unchanged since `41c6c3a39f` (`Api.lean:491-494`). The three exclusivity laws cover every pair.
- `boltOpenOptions_init`: NR2.

**`backend.Defrag` (trusted, unchanged).**
- Its "why it is true" is consistent with 4c as it is now: the reopen with `b.bopts` and the temporary database with `*b.bopts` both use the `emp` slot.
- `boltRelease` of the old file needs the whole `boltState`. The backend holds it through its own history invariant while the client keeps `beHist`. That is plausible, but the realization text should say that `beDurInv γ p` follows the current bbolt name across the swap (second tier).
- The rename and directory sync are C42/C43.

**`OpenBackend` (2d/2e, trusted).** It passes `beOpenUpd` to `New` unchanged, and the goroutine and channel hand-off is as in Go. It closes.

### bbolt (4c)

**`Open.lean`:** the header note only.
- With `NoFreelistSync` on, `Open` performs no commit: the `Begin(true)`/`Commit` block is skipped (`db.go:319-334`).
- `loadFreelist` reads, or rebuilds the freelist from `freepages()`, and writes nothing (`:448-471`).
- So the `emp` pre and post are right, and the crash invariant never leaves its closed state on a fresh file's `init` (the fork's crash-safe `init`).

### schema (4b)

No change.

## Snippets

**`raftlog/ready.go` `ReqCompactApplied`:** provable now.
1. `i = applied ≥ base` and `floor ≤ applied` give `compactFloor = applied`.
2. `CreateSnapshot` at `i`: `logStor_createSnapshot`, with the `logStored` coming from `raftLog_publish`/`logFloor_stored`.
3. `Compact(i)`: `logStor_compact`.
4. `term(i)`: the storage's dummy entry at `firstIndex - 1 = i` answers, so there is no `ErrCompacted`.

**`raftlog/reads.go` `ReqScanConfChanges`:** provable.
- The early return on a pending snapshot discharges `snap = none`.
- Assumes gives `applied ≥ base` and `floor ≤ applied`, which together are `scan.spec`'s premise.

**raftnode, raftcore:** unchanged since `41c6c3a39f`. Their earlier verdicts stand.

**Second tier (completeness).**
- No snippet covers the crash crossing, which `examples/raft/kvdurable` (crash and restart) uses. `ReqRestartDurable`'s "id is vacant (the previous node stopped)" should also allow "or crossed a crash: `raftState_gen`/`raftState_crash`" once F1 is fixed.

**`backend/commit.go` `ReqReopen`:** see F2 (its Assumes).

**`backend/more.go` `ReqOpenSnapshotFile`:** provable. The file is `beFile_of` from `fileHolds_image`, so its name is durable.

## Findings table

| id | tier | file | status |
|---|---|---|---|
| N3 | 1 | `raft__hasUnappliedConfChanges.lean` | resolved |
| S-e | 2 | `ApiCore.lean` `coreIdle_floor` | resolved |
| NR1 | 1 | `examples/specreq/raftlog/ready.go` | resolved |
| NR2 | 1 | `backend/Durable.lean` | resolved |
| **F1** | **1 (new)** | `raft/v3/Api.lean` `raftState_gen`, `raftState_crash` | **open**: provably inconsistent with `exclusive.spec` |
| **F2** | **1 (recorded gap)** | `backend/backend__Close.lean`, `Api.lean` `beCloseUpd`, `Durable.lean` `beFile_crash` | **open**: recorded in top.md K6, not in `open-questions.md` |
| s1 | 2 | `examples/specreq/raftnode/restart.go` | the crossing is not covered |
| s2 | 2 | `backend/Durable.lean` / `backend__Defrag.lean` | `beDurInv`'s realization across defrag's bbolt-name swap is not stated |

## Go code

No new bug. Neither F1 nor F2 is a Go bug: F1 is in our spec. F2's root is
`nonissues/bbolt-create-dir-not-synced.md` (C2), already filed.

## Counts

- **Recheck:** 4 findings rechecked (N3, S-e, NR1, NR2), all resolved.
- **Regressions:** 12 spec files changed in the area since `41c6c3a39f`, all re-checked. 10 close.
  - raft `Api.lean` (F1) does not close.
  - `backend__Close.lean` (F2) does not close for a fresh file.
- **Specs outside the area:** `OpenBackend`, `OpenSnapshotBackend`, `backend.Defrag` and bbolt's `Open`/`DB.Close` were checked for closure; they close.
- **Snippets:** 2 changed snippets checked (raftlog `reads.go`, `ready.go`); both are provable. 2 backend snippets were re-read: `ReqOpenSnapshotFile` is provable; `ReqReopen` needs an Assumes line (F2).
- **New findings:** 1 first-tier (F1), 1 first-tier recorded gap (F2), 2 second-tier.

## Ranked by need of revision

1. `SpecPlan/Spec/go_etcd_io/raft/v3/Api.lean`: `raftState_gen`/`raftState_crash` (F1). Their realization text and `ApiBoot.lean`'s `memberBoot_crash`/`memberJoin_crash` realizations follow.
2. `backend__Close.lean` / `beCloseUpd` / `beFile_crash` (F2): record it as an open question, or give `beFile` its name state; fix `ReqReopen`'s Assumes.
3. `examples/specreq/raftnode/restart.go`: cover the crash crossing (s1).
4. `backend/Durable.lean` header: `beDurInv` across defrag (s2).
