# F2: the sender's observation of the compaction records (2026-11-02)

The spec-first stage after #7-cmp's Freeze (`notes/image-cmp-plan.md`): discharge SNAPSHOT-SORRY
#7-cmp (`SnapSendBranch.srvBeSnapOk_cmpRecs`), the one `sorry` the compaction-mode snapshot image
rests on. Branch `image-cmp`, after the Freeze commit. Draft: `ImageCmpF2Draft.lean`.

## Scope

A snapshot of the server's backend in compaction mode, taken by `createMergedSnapshotMessage` on the
apply thread (sole KV writer at `log`, compaction resources `cmpOwn` at `crev`), must observe
`keyImageM true log r D` at `r.crev = crev`:

1. **The records**: `Meta`'s `finishedCompactRev`/`scheduledCompactRev` in `D` are the records'
   bytes, and `r.crev = crev` (Go's `compactMainRev`).
2. **The cut**: `D`'s `Key` bucket is the log's entries cut per key at a prefix of the ones
   compaction at `r.crev` deletes (`entsCutAt`).

Today: `backend.Snapshot.spec` (an axiom) gives (1) only through the flag (`fkRd`: the values at the
open, while nothing was put; `Meta` is a hook bucket, outside `vData`, and the compaction keys are
not the hook's own keys, so `hkData` does not see them) and of (2) a physical view thin of the
logical one (`viewAt`: each missing entry deletable, no shape). mvcc keeps its own record of the
compaction keys (`metaCompact`, in `compactRes`) unconnected to the backend's data, and nothing of
the job's progress.

Out of scope: the restart path's compaction-mode receipt (RESTART-RCPT); the compaction-mode
snapshot apply (56's stage C).

## Findings

- **F2-1. `srvBeSnapOk_cmpRecs` is not the lemma F2 proves.** It transforms an arbitrary
  `srvBeSnapOk` triple into one with a stronger post; Iris has no conjunction rule for triples, so
  it is not provable from any spec of `Snapshot` (true of Go, unprovable in this form). F2 replaces
  it: `srvBeSnapOk_window`'s observation gains the records (over `specF2`) and the sorry lemma goes.
  No narrower provable placeholder exists without restating the trusted `Snapshot` text, which the
  Freeze kept fixed.
- **F2-2. The server's backend has one non-hook bucket** (`KBReal.P`: every bucket but `Key` is
  the hook's), so the physical view `vData` is the `Key` bucket, written only by mvcc. (Review: the
  backend's contract changes for every writer of a non-hook bucket all the same, and mvcc's abstract
  backend contract with it; `vData` is the non-hook buckets, not the safe-range ones, which
  coincide only for `KBReal.P`.)
- **F2-3. The cut needs the job's cursor.** "Every missing entry deletable" does not give "per key a
  prefix": the job deletes in revision order from revision `0`, so the cut is kept by a cursor
  (`jobCursor c p`: every entry below `p` deletable at `c` gone). Jobs run one at a time (the FIFO
  scheduler); a compaction scheduled while one runs raises `sched` (and `r.crev`) past the running
  job's revision, which keeps the cut (`KeyDel` grows with the revision). A job stopped between
  batches leaves a partial cut, still a prefix per key.
- **F2-4. `r.crev = x.crev` needs a tie between `W` and the apply thread** (revised after review:
  not a share of `crevUB`, a logical authority already split ½ right, ¼ `s.mu`, ¼ `s.revMu`, which a
  share in the per-backend `W` would strand at a restore). A physical ghost of the scheduled record
  (`schedHalf`, a `PhysNames` field renewed by `Restore`), half in `cmpTrack`, half in the
  restorable compaction right; with `fin ≤ sched` in `cmpTrack` (the job writes only `fin`),
  `r.crev` is fixed by `sched`.

## Draft (`ImageCmpF2Draft.lean`)

- Backend: `pvHalf γ vd`, `ckHalf γ v` (placeholders for two `BNames` fields); the batch lock holds
  the other halves at the writer's contents' `vData` and `fkVals`.
- **Trusted text, restated**: `backend.backend.Snapshot.specF2` (below), `spec_of_specF2` (today's
  spec is an instance: the restatement only strengthens).
- mvcc: `physCut`, `jobCursor` (at a whole revision), `cursorDone`, `schedHalf`, `cmpTrack` (a
  conjunct of `compactRes` at the switch).
- Proved: `keyImageM_of_tracked` (the observation suffices), `windowObs_image`.
- Statement for the Prove phase: `apply.cmpObs_stmt` (the writer's observation from `cmpTrack`).

### The restated axiom

```lean
abbrev backend.backend.Snapshot.specF2 : Prop :=
  ∀ γ P W Pk b qo R (Q : VData → GMap (GoString × GoString) GoString → GMap GoString BktData →
      FkVals → Prop),
  {{ isPkgInit backend ∗ isBackend γ P W Pk b ∗ bOpen γ qo ∗ wbTok γ ∗ R ∗
      □ (∀ vd d r v, R -∗ W -∗ Pk -∗ viewAt γ vd -∗ pvHalf γ vd -∗ hkOwn γ d -∗
          rbOwn γ r -∗ ckHalf γ v -∗ ⌜Q vd d r v⌝) }}
    b.Snapshot()
  {{ sp D, RET sp; snapOpen sp D ∗ bOpen γ qo ∗ R ∗ fkRd γ P (D, ⟨∅, 0⟩) ∗
      ⌜Q (sData P D) (hkData P D) (rbData P D) (fkVals D)⌝ }}
```

Why it is true of Go: today's argument (the docstring of `backend__Snapshot.lean`'s axiom), with
the two new ghosts beside `hkOwn`/`rbOwn`: at the end of the last commit before the read
transaction began, the lock was free, so its halves of `pvHalf`/`ckHalf` were at the writer's
contents, which the commit made the committed data. Go tests (`axiomcx/f2_test.go`):
`TestSnapshotPendingWrites` (an unlocked, uncommitted put of a compaction key and delete in `Key` are
in the snapshot), `TestSnapshotWaitsForSession` (a session holding the lock during `Snapshot` is in
it whole); `imgcmp_test.go`'s `TestImageCmpMidJob` (the records and the cut, mid-job and with a
second compaction queued). All pass.

## What the Prove phase does (at the switch)

1. `BNames` gains `pv`, `ck`; the batch lock's invariant (`batchGhostAt`) holds their halves at the
   writer's contents; every write to a non-hook bucket (`UnsafePut`, `UnsafeSeqPut`, `UnsafeDelete`,
   `UnsafeDeleteBucket`) and a put of a compaction key take and update the client's half (`metaPutCap`'s triple gains `ckHalf`); `New`/`OpenBackend` give the
   client's halves at the opened data; a commit keeps them.
2. Only then (review A1) the axiom restated (`backend__Snapshot.lean`): `specF2` in place of `spec`,
   its docstring naming step 1's invariant; the `axiom` skill's check before the Freeze.
3. mvcc: `compactRes` gains `cmpTrack` (with `metaCompact`'s record as its `r`; for the real
   backend in compaction mode); `PhysNames` gains `jc`, `sch` (renewed by `Restore`), the restorable
   right (`compactRightR`) the other `schedHalf`; `updateCompactRev` (taking `1 ≤ rev`),
   `UnsafeSetFinishedCompact`, the job (`scheduleCompaction`: its cursor fragment in `compactTok`),
   `restore` (the resumed job, the opened records, `cmpTrack` in the new backend's pre-registration
   state), `store.Write`'s puts (the cut extended by present entries: `entsCutAt` of a longer log)
   keep it; the writer's pin gains a share of `γ.wv`.
4. `srvBeSnapOk_window` over `specF2` with the observation `windowObs`; `mergedCreate_window`
   uses it (`cmpObs_stmt`, `windowObs_image`); `srvBeSnapOk_cmpRecs` and its `sorry` deleted.

## Review (round 1, a fresh spec reviewer, 2026-11-02)

`specF2`: no falsifying execution found (attacks: the job's deleting `Unlock` committing inside its
session, `run`/`ForceCommit` commits, pending writes, a session during `Snapshot`); a strengthening
only. The mvcc side and `cmpObs_stmt` were not provable as drafted. First tier:

- **D1. `cmpObs_stmt` over `lateW`**: after `store.Restore` the new backend's `lateW` stays
  unregistered until a writer takes the batch lock (`writerReg`); a snapshot can come first (a
  follower restores in compaction mode, becomes leader, sends a merged snapshot before any write:
  `ForceCommit` registers nothing). The lesson of the writer's pin. Open: question 5.
- **D2. `cmpTrack`'s log is `writerRes`'s, not `kvWriter`'s** (the pin agrees on the bucket, the
  certificate only gives a prefix). Open: question 6.
- **C1. The cursor at a main revision cannot keep the prefix shape** (a batch may end between `(m,0)`
  and `(m,1)` of one revision; `M2StorageDraftIndex.lean`'s lesson). Fixed: the cursor is a `Rev`.
- **C2. A logical `crevUB` share in the per-backend `W`** (stranded by a restore; the split
  misstated). Fixed: `schedHalf`, a physical name (F2-4 revised).
- **A1. The axiom is only as true as the batch lock's invariant holding the two halves**: restate it
  only after the backend's step 1 lands, its docstring naming that invariant. Adopted (Prove phase
  order).

Second tier, adopted: A2 (`pvHalf` over the non-hook buckets, every write to one, either mode); C3
(`fin ≤ sched` in `cmpTrack`; the cursor fragment in `compactTok`, not the persistent
`compactJobPre`); C5 (`cmpTrack` gated by the instance and the mode; mvcc's abstract backend contract
(`batchTxSpecG`/`isKeyBackendG`) carries the halves); C4 open (question 7). Third tier: names
(`cmpObs_stmt`/`windowObs` in `apply`), `jcG`/`schG` `PhysNames` fields, the test names, a lemma
`KeyDel` monotone in the revision (none yet: `KeyDel_prefix` only), whether `fkOkG`'s open-values
clause stays once `ckHalf` is exact.

Collections resting on the strengthened axiom (`One spec per function`: listed): backend, authkv,
cachekv, compactkv, m2, linkv3p, k8setcd3, leasekv, linkvtxn, server, snapshot, putget, putget3,
watchkv.

## Questions (for the user; recommendations)

**Approved, all seven (the user, 2026-11-02; `notes/decisions.md`).**

1. **Restate `backend.Snapshot.spec` as `specF2`** (the trusted text above). Recommended.
2. **Two exact client halves** (`pvHalf` of the physical non-hook view, `ckHalf` of the
   compaction keys) rather than widening the hook's own keys to the compaction keys (whose client
   half the consistent index's `Pk` holds whole, so mvcc could not write them) or a "gone set"
   (equivalent, more vocabulary). Recommended.
3. **The cut kept by a job cursor in mvcc** (F2-3). Recommended.
4. **`srvBeSnapOk_cmpRecs` replaced, not proved** (F2-1). Recommended.
5. **D1: where the observation finds `cmpTrack` when no writer has registered since a restore.**
   Recommendation: `store.Restore` (which makes the new `cmpTrack` from the opened records) leaves it
   in the new backend's pre-registration state, which `lateW` then carries in both states (one
   design of `writerReg` to check in the Prove phase); the alternative, holding the client halves
   with the apply thread, fails because the job and the writers move them concurrently.
6. **D2: the writer's log in `cmpTrack`**: a share of `γ.wv` in the writer's pin (as the pin holds a
   bucket-view quarter). Recommended.
7. **C4: the source of `recsPos`** (records `≥ 1`): `updateCompactRev` takes `1 ≤ rev` from its
   caller (the server's committed compactions, `compactPropOk`, are at revisions `≥ 1`; M2's scope
   restriction Q7). Recommended.

## Open after landing: T1-B, `lateWB` at a restart (2026-11-03)

F2's second review round found that `lateWB`'s unregistered arm, narrowed to an empty `Key` bucket
with no compaction records (the fix of round 1's A1), cannot be met by a restart: the backend reopens
the stopped member's data, which is not empty, so `InvRestart.newPost` cannot hold and
`bootstrapRestartContract` (under `examples/common/Restart.lean`'s `bootPremiseR`) says `bootstrap`
always fails on a restart, false of Go. F2 landed without fixing it (the user's choice, 2026-11-03):
it is the first item of the whole-`bootOk` spec-first review. The reviewer's proposed fix: index the
boot state by the opened data, `lateWB gx γB P D := (dghostVar gx ½ none ∗ backend.pvckInit γB P D) ∨
lateWR gx`, a first boot the case of an empty `D` (a law from `bootOk`'s `HD`/`HmEmpty` to the empty
form, for `NewStore`); it changes the text of `bootOk`'s `Hnew` and `InvRestart.newPost`, and
`lateWD_boot`, `kbBoot`/`kbTieInit` (fixed at the empty log and `-1`) and `crevRightM`'s
`kbCrev (-1)` generalize with it.
