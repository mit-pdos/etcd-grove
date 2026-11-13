# Restart track: Scope for restarting it (2026-11-11, for etcd-grove-81; design only, nothing edited or built)

Read at `lean` `da225483c9` (main checkout, read-only) and branch `r2db` (tip `09316d74cc`,
off `ebcadd29bf`, notes only, never landed). Go citations are etcd at the pin `673da07c8`. Estimates
are marked (est.). Where this Scope and `notes/r2db-scope.md` (r2db, revision 4) differ, this one
holds for sequencing and sizes, and r2db holds for the texts it drafts (§4 there). The r2db texts
were written against `ebcadd29bf`, before the mvcc API merge (R6/R8), mvccfull F1, premise fixes
1-7 and the per-type stage A. Their line numbers are stale and must be re-cited (stage S0).

---

## 1. Where the track stands on `lean`, layer by layer

| Layer | State on `lean` | Files |
|---|---|---|
| **Go program and test** (R1) | Done. `restart3`: start 3, put, `HardStop` a follower, close its peer listener, `NPuts` puts, restart it on its data dir, serve its gRPC, get through it. The test counts a WAL replay, a WAL snapshot, and a snapshot sent and installed after the restart (15/15). | `examples/etcd/restart/restart3.go`, `restart3_test.go` |
| **Example layer** (R2a) | `Run.wp_proof` and `Main.wp_proof` are proved over hypotheses. `restartCheck.wp_proof` takes `startMember.specRestart`. `startMember.wp_proofRestart` takes the unproved `etcdstart.BuildServer.specRestart`, the draft `Start_builtR_spec` and the draft `http.registerClosable_spec` (HS3). No `Link.lean`, no `Results.lean`, no tcb collection: **nothing of restart is linked.** | `Proof/.../examples/etcd/restart/*.lean`; `Spec/.../examples/lib/etcdstart/BuildServer.lean:87-118`; `Proof/.../etcdstart/{Restart,StartStop,StartRes}.lean`; `Proof/net/http/ListenerClose.lean` |
| **The stop** (R2b) | Done and linked. `HardStop.spec` → `run`'s deferred shutdown → `raftNode.stop` → `Cleanup` (`mvccImage_stop.law`) → `stopCleanupImage` gives `srvDiskImage`. **Scope (load-bearing for a schedule theorem): a member can be stopped only if it never served gRPC** (`EtcdServer__HardStop.lean:8-15`: its serving stocks went to `Serve` and no `grpc.Server.Stop` spec returns them); also auth off and no mvcc compaction mode (`srvStop.scope`, `InvRestart.lean:230`). | `Spec/.../etcdserver/EtcdServer__HardStop.lean`; `Link.lean:1613,1737` |
| **The image** (R2c) | Defined. `srvDiskImage` (`InvRestart.lean:135`): `nodeVacant`, `raftState S`, `srvRLogLb A`, `imageRestAt`, mvcc's `mvccImage` (receipt inside: RESTART-RCPT settled by R6), `confAt i m`, `wal.stopImage` (sealed: `StorageHolds S σ`, `σ.b ≤ i ≤ σ.commit`, `walSnapCert`), registry auth, `srvFiles` (`walFiles … σ` **at `sized = false`** and `fileHolds … D`), `pathOwn`. | `Proof/.../etcdserver/InvRestart.lean`; `WalApi.lean:325-341`; `storage/WalRecs.lean` |
| **The restart contract** (R2c, L3) | A **premise**, not an axiom: `bootstrapRestartContract` (`InvRestart.lean:566`) → `bootOkR` (`:363`), wrapped as `etcdstart.bootPremiseR` (`Proof/.../etcdstart/Restart.lean:36`) and carried by `restart3.premises` (`Defs.lean:100-118`). `bootOkR` holds the opaque `memStorRestarted` (`:342`, no content), only `walReady` + `walOpen` of the WAL (no records, no metadata, no durability), `lateWBR := mvccW gx` (B2 is moot, below), `Hmem` (in-memory members = `restModel … L`, H10). | as left |
| **The WAL** | Names-only. `walFiles` is an `axiom` IProp (read as `True`); its meaning comes from `dataDirsAbsent` (sweep repairs R1-4a, landed). The `sized` flag exists ([r3g], `307b36dee8`): `wal.bootOk` gives `sized = true`, but `wal.bootOk_start` unsizes at once (`walRecs_unsize`), the raft loop uses `walSave_spec` (unsized; `raftNode__start.lean:627,1336`), `walClose` is at `false`, so the stop's files are unsized. **No `ReadAll` fact exists** (`walOpened`'s docstring: "deferred to the restart contract's work"). `storage.Release` takes `walBaseLb` (W2 landed); **`purgeFile` does not yet take `walPurgeRight`** (W1, `EtcdServer__purgeFile.lean:30`: "not yet here"). | `storage/WalRecs.lean:209-251`; `etcdserver/WalApi.lean`; `etcdserver/InvWal.lean` |
| **Raft's restart** | `RestartNode.spec` proved (durability stage II (u)), linked; `node.Stop` gives `nodeVacant`. raft's crash durability is proved at the raft level (`kvdurable_porcupine_safe`, durableExt). Missing for the server: the loop fact of Q31, the start tag (row 4, Q32), and the restarted storage's entry sizes (`out_size`'s [r3h] condition, `Proof/go_etcd_io/raft/v3/MsgOut.lean:198-203`). `out_size` is a tracked `sorry` that every server `_safe` result already rests on (15 collections). | `Spec/go_etcd_io/raft/v3/RestartNode.lean`; `Proof/go_etcd_io/raft/v3/{InvNode,MsgOut}.lean` |
| **The server's restart/replay** (R2d'a) | **Landed, frozen** (tag `r2dpa-frozen`): `run.spec` over `isServerRunC`, whose start is `srvRunRestartR` (a first start is its instance); the per-entry replay specs (`applyEntryNormal`'s `v3 = false`, `applyConfChange`, `apply`, `applyEntries.specBatch`, `applyAll.specSnapM/specBatch`, `stopCleanupImage`) are the restart forms. Scope `σ.b = 0` only. **Vacuous on most restarts** (STATUS "R2d'a", correction of 2026-11-07): row 3 `rnWalCommitAbove` (`InvRaftNode.lean:393`) is false at the start of almost every restart after a quiet stop; `Hwpend`/`srvWinPend` (`InvRun.lean:57-70`) is false on every restarted run in which the member later leads and snapshots a follower. No closed theorem carries them. `NewServer` builds only a first start (`newRaftNode.spec`'s post pins `γ.a0 = [] ∧ γ.t0 = 0`; `isServerBuiltC` keeps the first-start `%HEr`/`Hsnap`). | `Proof/.../etcdserver/{EtcdServer__run,AuthCompRows,InvRun,InvRaftNode,ApplyRDefs,RestReplay}.lean`; `notes/restart-plan.md` "R2d'a restart-only premises" |
| **mvcc / backend image** | **Done** (mvccfull F1, below, §2). | `Spec/.../storage/mvcc/{Api,EtcdBackend}.lean`; `Proof/.../storage/mvcc/{NewStoreR,NewStoreSess,NewWatchableAt,RWMutexWLocked,Api/ImageBridge}.lean` |
| **`NewServer` at a restart** (R2d'b) | Not started. Its Scope is revision 4 on `r2db` (FULL vs CUT, Q41 still with the user). | `git show r2db:notes/r2db-scope.md` |
| **Snapshots across windows** (R2s) | Design only (`notes/decisions.md` "R2s: snapshots across windows"; r2db §14 R2s-A). | — |
| **The cluster driver** | `examples/lib/cluster3` has partition and client steps only (`PeerCut/Mend`, `ClientBlackhole/Unblackhole/Drop`); no stop or restart step. `restart3` is a fixed script with one follower restart. | `examples/lib/cluster3/cluster3.go`; `Proof/.../examples/lib/cluster3/` |
| **The closed theorem** | None. `restart3_safe` (R2e) is a draft statement in the plan only. | `notes/restart-plan.md` "The top-level statement" |

Whole-repo prerequisites, outside the track: the per-type stage A landed (`pbEnc_ok` gone);
**the per-type stage B (grpc's handler pool, `grpc.serve`'s caller-chosen `S`/`n`;
`notes/per-type-blockers.md` (a)) is not landed** (`/shared/tmp/stageB-scope-r2-review.md`: NOT
READY). STATUS still says 59 exported results, all 17 `*_safe`, rest on the refuted grpc message-model axioms. A restart closed
theorem would inherit that until stage B lands.

## 2. What mvcc B3 and mvccfull supply, and what they retire

What mvccfull F1 landed (`notes/mvccfull-proof-plan.md`, "Freeze", "F1 landed"; `notes/decisions.md`,
"mvccfull F1's Freeze"):

- **`mvcc.api.New.spec`/`NewStore.spec` over any image** (`mvccStorageFor B Pk σ.log σ.crev u`,
  `MvccReachable σ`, nothing pending, the resumed compaction `if u`), proved: `NewStoreR.lean` (the
  session over `storeSessT`, `restore()` at `ns = false`, `RWMutexWLocked.lean`'s
  `init_RWMutex_wlocked` so a resumed compaction finds the store), `NewStoreSess(Real).lean`,
  `NewWatchableAt.lean` (`wsInitAt`), `Api/ImageBridge.lean` (`newStore_of_storage`).
- **`etcdStorage_open.law`** (`EtcdBackend.lean:169`): `mvccImage D L c u` (persistent) with
  `backend.newPostKP` over `D` gives `mvccStorageFor … L c u`. **`mvccImage_stop.law`**: a stopped
  store's image. So the store side of a restart is: `srvDiskImage`'s `mvccImage` (persistent; the
  caller keeps it across the contract, which takes it by `-∗`) plus `bootOkR`'s `Hnew` → open law
  → `New.spec`.
- **`lease.NewLessor.spec` over a lease bucket with records** (restated axiom, Freeze item 2,
  mirroring the proved `lessor.Recover`), the lessor's owner part lent to `New`.
- `mvccfull_adequate`: restarts and snapshot restores **at the storage layer**, all graceful
  (`backend.Close` → `fileHolds` → reopen). It does not model a crash, the WAL, or raft.

What that retires or shrinks in the planned stages:

| Planned item | Effect |
|---|---|
| R2d'b **B3** (`mvcc.New`/`NewStore` restoring, 1.5-2 wk) | **Retired** (done). |
| R2d'b **B2** (`lateWB`'s unregistered arm → `pvckOwn`, `lateWBR` merged, trusted) | **Retired**: `lateWBR gx _ := mvcc.api.mvccW gx` (`InvRestart.lean:351`), the first start's resource; only a deletion of the alias remains (a form change). Confirm at S0. |
| mvccfull risk R6 / R2d'b: `NewLessor` on a bucket with records | **Retired** (restated once for both clients). |
| RESTART-RCPT (the compaction-mode receipt of the image) | **Retired** (the receipt is inside `mvccImage`). Compaction mode at a restart remains out of scope for other reasons (`srvStop.scope`). |
| R2d'b batch 4 (B2-B4, 2.5-3.5 wk) | **Shrinks to HS1 alone** (B4: `NewAuthStore` over `authBoot`, 2-3 d) plus the `lateWBR` deletion. |
| R2d'b **B5** (`NewServer.specG`'s boot sum, 3-4 wk, "least certain") | **Shrinks**: the store and lessor part is one `etcdStorage_open.law` + `New.spec` call, the same shape as the first start's (`NewServer.lean` already lends `Hlown` to `New`). Est. 2.5-3.5 wk. The risk "a gap in `bootOkR` for B3's restoring `NewStore`" is gone. |
| The "certificate map's `M`" for the server's restart (mvccfull plan, "to confirm") | Still to check in B5: the restart supplies `New.spec`'s certificate map. |

Net: about 3.5-5 weeks of work leave the critical path compared with r2db §13's figures.

## 3. What remains, as stages

Ordered by dependency. "Kind" says which statements move: internal (no approval needed beyond the
Scope), frozen or exported (approval), trusted (axiom-skill attack and approval).

### S0. Re-baseline (2-3 d, est.)
Re-cite r2db's §4 texts at `lean` tip (`InvRaftNode`, `AuthCompRows`, `InvRun`, `EtcdServer__run`,
`NewServer` moved under R6/R8, pf1-7). Diff `bootOk` (`InvBoot.lean:253`) against `bootOkR`
(`InvRestart.lean:363`) for every change since R2c not mirrored: at least `%Hraft`'s
`bv.lg' ≠ null` (pf6 made `bootOk`'s `bv.lg' = cfg.Logger'`), the snapshotter's logger (pf6 D1),
`#Hsz` removal (done in both). Get Q41 decided (§4, D2).

### S1. R2d'a's vacuity: rows 2-3 and `Hwpend` (1-1.5 wk for rows 2-3; `Hwpend` see below)
- **Rows 2-3 (Q31 (a) in F1's form, decided 2026-11-07):** delete `rnWinInstallAbove` and
  `rnWalCommitAbove` from `rnRestartOk`; put the loop fact `|a0| ≤ p.Commit'` in `rnLoopTokP`
  (pinned `commit0`/`snap0` in `RNNames`), established from `RestartNode`'s `σ.hs` and kept by the
  proved `readyRest_commit_mono`; `rn_ready_recv` derives row 2 by `readyRest_snap`;
  `raftNode.stop.spec`'s post gives row 3 as `|a0| ≤ σ.commit` of the records it returns, with
  `σ.hs = v.hs` and `∃ l', isCommittedLogLb cl l' ∗ ⌜σ.b ≤ |l'| ∧ DurAgrees S l'⌝` threaded through
  `rnDur_take`, `rnStopImage`, `stopCleanupImage` into `wal.stopImage`'s sealed body (needed by S2's
  `wal.restartOk_start`). Kind: internal plus `raftNode.stop.spec`'s post (frozen, one approval).
  True of Go (review v2 confirmed the loop fact and the restated row 3).
  Files: `InvRaftNode.lean` (1047 importers: one full build), `InvWal.lean`, `WalApi.lean`,
  `Spec/.../raftNode__stop.lean`, `StopShutdown.lean`.
- **`Hwpend` (row 1).** Two options:
  - (a) Q33's redesign now (r2db §4.4-§4.5: the wand takes the apply side's exact token
    `rnApplyTok γn A` at the post-receive log, guard `|pre ++ A| < |a0|`, supply `srvWinSupply` inside
    the image, `srvWinAdd` where the stop's image becomes the restart's): narrows the false class to
    "elected at a term reached while a >1 MiB replay is still handed out". +1-1.5 wk, and all of it
    is deleted by R2s-A.
  - (b) Leave `Hwpend` as frozen, disclosed false, and remove it with R2s-A (S7), started early.
  **Recommendation: (b).** No closed theorem can carry `Hwpend` in either form (the strong-theorems
  goal), so (a) only buys an open triple that is non-vacuous on more runs for a few weeks. Choose (a)
  only if R2s-A cannot start within about 6 weeks.
- Checkpoint **C1**: R2d'a's restart triple is non-vacuous on quiet stops (row 3 true).

### S2. The WAL at a restart: `ReadAll` and the sized records (1.5-2.5 wk, est.)
- **S2a. `wal.restartOk`**, a WAL slot in `bootOkR` (trusted text): the restart's `wal.Open` +
  `ReadAll` of `walFiles (walDirOf dd "") id cid σ sized` gives `walOpened w … σ sized` with the
  metadata `walMetaIs w id cid` and `walPurgeRight`; its elimination `wal.restartOk_start` allocates
  `rnDurInv` at the view `⟨S, σ.hs, none, l₀⟩` (`l₀ := l'.take σ.b`, committed, `DurAgrees` from
  S1's stop post). `DedicatedWALDir = ""` (already the contract's). It is the first exported reader
  of `walFiles`: prerequisites **W1** (`purgeFile` takes and returns `walPurgeRight`, sweep repairs
  R1-3, **not landed**) and dataDirsAbsent (landed).
- **S2b. The sized flag end to end** (the "WAL's sized ReadAll fact", [r3g]/[r3h]): keep
  `sized = true` in `rnDurInv` from `wal.bootOk` (drop the `walRecs_unsize` in `wal.bootOk_start`);
  the raft loop's two `Save`s through `walSaveSized_spec` (`WalApi.lean:152`, with `entSizeOk` of the
  handed-out entry objects from raft's `outEntR` and `out_size`); `walClose` at `true`; `srvFiles` at
  `walFiles … σ true`; `wal.restartOk` at `sized = true` gives, with `storage.diskOk` (no `Save`
  failed; already every closed theorem's premise), the replayed entry objects with `entSizeOk`
  (`ReadAll`'s `Unmarshal` round trip, stage A's D2). `memStorRestarted` (S3) carries them into the
  restarted `MemoryStorage`, so raft's storage contract has bounded entries and **`out_size`'s [r3h]
  condition holds for restarted nodes**. Kind: internal for the loop; trusted for `wal.restartOk`
  and the `walClose` spec at `true` (axiom-skill attack: a WAL written with a failed `Save`; a
  segment purged after `Close`).
- Files: `WalApi.lean`, `WalRecs.lean`, `InvWal.lean`, `raftNode__start.lean` (proof), `InvRestart.lean`.
- **No `ReadAll` without S2b.** Without it every restarted node's result leans on `out_size`, whose
  Go argument does not cover restarts (its docstring says so).

### S3. Raft's restart path in the server (3-4 wk, est.; r2db batches 1s, 1b, 2)
- `newRaftNode.spec`'s binders `a0 t0 L₀ commit0 snap0`, post `γ.a0 = a0 ∧ γ.t0 = t0` (review 4;
  frozen); `rnRestartOk` into `isRaftNode` (`rnCfgAt := rnView`; review 5); `raftNode.start`/`stop` at
  `P` (`γn.pre = []`, tokens and `cum` at `P`: Q34 (a)).
- **B1: `memStorRestarted` defined** over raft's storage vocabulary (`ApplySnapshot` of the record at
  `σ.b` with the backend's `ConfState`, `SetHardState(σ.hs)`, `Append(σ.ents)`, `bootstrap.go:554-581,
  725-734`), giving `RestartNode`'s `restartStorage` at `a = i` and `srvFrozenTerms γs 1 P`
  (`kd_restartStorage` is the model). It is the contract's body: trusted (HS2's re-attack).
- **Q39's law**: `confAt cl k m → m = simple cfg` from `srvClusterOk` (`confAt 0` and
  `srvRuleKeeps`), so the restarted storage snapshot's `ConfState` (the backend's at `i`) is valid at
  `σ.b`. If no such law exists, the static-membership premise R-S3 enters the contract (fallback Q39 (b)).
- `bootstrappedRaft.newRaftNode.spec` and `NodeStartSpec` over the boot sum (Q35 (a)); the exported
  `server_raft_node_start` restated.
- **Row 4 (`rnSnapTermAbove`, Q32).** Recommendation: neither (a) (raft start tag, 2-3 wk,
  rebuilds 1905 raft importers) nor (c) now: row 4's only consumer is `winNoMergedSendR`'s `rt ≤ t0`
  arm, which R2s-A deletes. Keep row 4 frozen until R2s-A, then delete it. (Q37 (b), the restarted
  lease TTL row, needs the start tag; out of the closed theorem's workload, §3 S9.)
- Probe first (r2db §3 steps 1-4): `run`'s first restart batch at `b > 0`; `rn_ready_recv` with
  the loop fact; the stop at `b > 0`; `memStorRestarted`'s body to `restartStorage`. H9's rule: stop
  on a gap, freeze nothing.
- Checkpoint **C2** (probe) and **C3** (the restart boot linked below `NewServer`).

### S4. The hubs at `snap0`; `run` at `⟨snap0, A₀⟩` (1-2 wk, est.; r2db batch 3)
`isServerBuiltC`'s `%HEr` and `Hsnap` in restart form (and the four built hubs), `start` derives
rows 6-8 from row 8 in `isRaftNode` (Q38 (a)), `run.wp_proof` at `⟨snap0, A₀⟩` (about 15 sites,
`EtcdServer__run.lean`). One full build (`AuthCompRows.lean`: 744 importers).

### S5. Constructors (0.5-1 wk, est.; was batch 4)
HS1 (`auth.NewAuthStore.spec` over `authBoot`, `NewAuthStore.lean:127`; trusted, attack recorded in
`restart-plan.md` R2d Scope §5); delete `lateWBR`. B3 done.

### S6. `NewServer` over both boots (2.5-3.5 wk, est.; B5)
`NewServer.specG`'s restart branch builds `isServerBuiltC`'s restart form from `bootOkR`:
`srvRLogLb`'s threading (row 8), the WAL slot (S2), the store through `etcdStorage_open.law` +
`New.spec`, the lessor through the restated `NewLessor`, membership's in-memory members (H10:
`bootOkR`'s `Hmem`; the axiom-skill check of `cl.Recover`'s JSON round trip, a hard stop on a
refutation), Q37 (a) (no lease-TTL row after a restart). The week-8 guard of r2db §13 applies
(B5 deferred, `NewServer.specRestart` stated not linked). **Waits for pf8** (§5).

### S7. R2s-A: follow the merged snapshot; `Hwpend` removed (6-9 wk work, 5-7 on its path, est.)
r2db §14: the snapshot certificate at a consistent index `j ≥` its raft index (`srvNet`'s `img`,
`sentMsg_snapshot`, `srvSnapRO`), `applyAll`'s merged send inside a window (`winNoMergedSendR`
deleted), the receiver's `applySnapshot` of an image above the snapshot's index followed by S4's
replay window reused at the install point, `run`'s snapshot jobs over a window; `srvWinPend`,
`srvWinSupply`, `srvWinAdd` and row 4 deleted. Steps 1-2 can start after S3's probe; step 3 needs
S4. Its own Freeze (`srvNet` is exported) and an axiom re-attack of the snapshot slot.
Checkpoint **C5**: no restart-only premise left in any restart result.

### S8. etcdstart, the example's links, many restarts (1-2 wk, est.; B6 + F4)
`memberBuiltR` merged into `memberBuilt`, `Start_builtR_spec` deleted, `BuildServer` one spec,
`startMember`/`restartCheck` linked. **F4 (a member restarted any number of times)**: the image the
second stop leaves must be consumable by the next restart (`restartNames` chained, the id
incarnation keys, `memberRestartRes` re-made by `stop`). Needed by the schedule theorem (S10).
Checkpoint **C4**: `BuildServer.specRestart` proved; `restartCheck` an open triple with no
restart-only premise (after S7).

### S9. R2e: `restart3_safe` (2-3 wk, est., after S7, S8 and the per-type stage B)
`restart3`'s `Link.lean`, `Results.lean`, adequacy, collection `etc/tcb-collections/restart3.txt`.
HS3 (`registerClosable_spec`, `ListenerClose_spec`) as trust-boundary axioms with their attack;
HS2 (the contract) per D4; R-S3/R-S7 supplied by the run (static membership; `stop` waits for the
bootstrap log). Statement: as `putget3_safe`'s, with the restart premises:

```lean
theorem restart3_safe [lctx] [sem] [package_sem : …restart.Assumptions] [cache_sem] …
    (Hctx : ∀ hG, ContextReadErrs …) (Hcec : ∀ hG, ContextErrsClient …)
    (id₁ id₂ id₃ : w64) (ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (Hbf : BootFacts id₁ id₂ id₃ ps ctxs boot) (Hck : ckptEffectsOk) (Haf : authRecordsFit)
    (Hbuq : apply.backendUnderQuota) (Hrf : grpcRepliesFit) (Hdbo : storage.diskOk)
    (HNs : prometheus.namesUnclaimed restart3Program restart3Names)
    (HAs : addrsUnclaimed restart3Program restart3Addrs)
    (HDs : dataDirsAbsent restart3Program [name₁ ++ ".etcd", name₂ ++ ".etcd", name₃ ++ ".etcd"])
    (HEnv : verifyEnvOff restart3Program) (n : Nat)
    -- each member's bootstrapContract and, for members 2 and 3, bootstrapRestartContract (D4)
    (Hprem : ∀ hG, ⊢ etcd_restart.premises n id₁ id₂ id₃ ps ctxs boot)
    (σ g) (Hlctx) (Hinit : IsInit σ) (Hthreads : σ.threads = 1) (κs t2 σ2)
    (Hsteps : RealNsteps n ([restart3Program], (σ, g)) κs (t2, σ2)) (Hn : n + 2 ≤ 2 ^ 28) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧ (∀ e2 ∈ t2, RealNotStuck e2 σ2) ∧
    (∀ v, Val v ∈ t2 → v.isPanic = false)
```
Checkpoint **C6**.

### S10. The schedule theorem: kills and restarts during traffic (5-8 wk, est., after S9; part trust work)

**The Go side** (`examples/lib/cluster3`, a new example `examples/etcd/restartp`, kept apart from
linkv3p as the user chose for restart3, so `etcd_partition_safe` keeps its premises):
- new step kinds `MemberStop = 5`, `MemberStart = 6` on member A (or one `MemberRestart`), in the same
  single driver goroutine as the partition steps, so a stop never races a `CutPeer` on that server;
  the member table is a slice the driver updates; a step on a stopped member does nothing (as an
  out-of-range one does now); stopping the last running member is allowed (requests fail: Unknown);
- a stop: wait until the member's `AppliedIndex()` covers the bootstrap log (R-S7, as `restart3`'s
  `stop`), stop its gRPC server so its handlers finish (`grpc.WaitForHandlers(true)` with `Stop()`,
  or embed's `GracefulStop` with a timeout fallback), `HardStop`, close the peer listener;
- a start: `BuildServer` on the same data directory and addresses, `Start`, listen on the client
  address again, `gs.Serve`; the bridge keeps forwarding to the same client address;
- the workload is linkv3p's (`Check`, porcupine against linkvtxn's model; no mvcc `Compact`), so
  the result is `porcupine.Ok`/`Unknown` and `Illegal` panics;
- Go test with a counting logger: every run restarts at least one member, at least one restart
  replays past a WAL snapshot (`σ.b > 0`), at least one restarted member later leads, at least one
  is caught up by a snapshot (the R2s path).

**The proof side**, beyond S1-S9:
- **A `grpc.Server.Stop` spec** (with `WaitForHandlers`) that returns the handler pool's tokens and
  the serving stocks, lifting `HardStop`'s "never served" scope. Trusted; its shape depends on the
  per-type stage B's pool (tied to `threadTok`), so it comes after stage B. 1-2 wk (est.).
- **A client address listened on again**: `net.Listen` consumes `netAddrFree` for good
  (`Proof/net/InvNet.lean`) and a gRPC address's server is fixed (`grpcServes addr …`): HS3 widened to
  gRPC listeners (the listener's close gives `netAddrFree` back) and `grpcServes` per incarnation.
  Trusted. 1 wk (est.).
- The partitioner over a member table that changes: `PeerStep` on a restarted member uses the new
  server's facts; a cut held by the other member toward the restarted one survives, the restarted
  member's own cuts are gone (etcd's transport is per incarnation). 1-2 wk.
- Bounds: each incarnation leaks the goroutines `http.Serve` and gRPC leave behind with their
  thread tokens; a premise `restarts · threadsPerIncarnation + … ≤ 2^28` derived from
  `steps.length` (decidable, like `Hsteps`). `notes/bounds-plan.md`'s owner rule.
- The theorem (draft):

```lean
theorem etcd_restart_safe [lctx] [sem] [package_sem : …restartp.Assumptions] [cache_sem]
    [DialWithBalancerBody] [log.NewModel]
    (Hctx : ∀ hG, ContextReadErrs …) (Hcec : ∀ hG, ContextErrsClient …)
    (id₁ id₂ id₃ : w64) (ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (Hbf : BootFacts id₁ id₂ id₃ ps ctxs boot)
    (Hck : ckptEffectsOk) (Haf : authRecordsFit) (Hbuq : apply.backendUnderQuota)
    (Hrf : grpcRepliesFit) (Hdbo : storage.diskOk)
    (clients ops : w64) (Hc0 : 0 ≤ sint.Z clients) (Hc31 : sint.Z clients < 2 ^ 31)
    (Hops : 0 ≤ sint.Z ops) (Hmul : sint.Z clients * sint.Z ops < 2 ^ 60)
    (steps : List cluster3.Step)          -- partition, client, MemberStop and MemberStart steps
    (Hsteps : steps.length < 2 ^ 20)      -- the incarnations' thread budget (bounds, est.)
    (HNs : prometheus.namesUnclaimed (restartpProgram clients ops steps) restartpNames)
    (HAs : addrsUnclaimed (restartpProgram clients ops steps) restartpAddrs)
    (HDs : dataDirsAbsent (restartpProgram clients ops steps) [n₁ ++ ".etcd", n₂ ++ ".etcd", n₃ ++ ".etcd"])
    (HEnv : verifyEnvOff (restartpProgram clients ops steps)) (n : Nat)
    (Hprem : ∀ hG, ⊢ etcd_restartp.premises n id₁ id₂ id₃ ps ctxs boot)  -- D4
    (σ g) (Hlctx) (Hinit : IsInit σ) (Hthreads : σ.threads = 1) (κs t2 σ2)
    (Hsteps' : RealNsteps n ([restartpProgram clients ops steps], (σ, g)) κs (t2, σ2))
    (Hn : n + 2 ≤ 2 ^ 28) :
    (∀ v t2', t2 = Val v :: t2' → v = #(go!"Ok") ∨ v = #(go!"Unknown")) ∧
    (∀ e2 ∈ t2, RealNotStuck e2 σ2) ∧ (∀ v, Val v ∈ t2 → v.isPanic = false)
```

  Every hypothesis but `Hprem`'s restart contracts and `Hsteps`'s bound is `etcd_partition_safe`'s
  (`Proof/.../examples/etcd/partition/Results.lean:109-142`). "Every schedule" is the `∀ steps`.
  **What "kill" means here is decided by D1**: with graceful stops, a `MemberStop` is `HardStop`
  after the gRPC stop, not a SIGKILL.
- Checkpoint **C7**.

**Premise check against the strong-theorems goal** (no validity about real translated code, no
unsatisfiable premise):

| Premise | Status |
|---|---|
| `Hbf`, `Hck`, `Haf`, `Hbuq`, `Hrf`, `Hdbo`, `HNs`, `HAs`, `HDs`, `HEnv`, `Hctx`, `Hcec` | As in `etcd_partition_safe`; STATUS "Premise fixes 4" lists what is still open in them (`ContextReadErrs`/`ContextErrsClient`: claims about `context`'s translated globals, provable from `context.isInit` but for `descs`). Inherited, not new. |
| `bootstrapContract` (in `Hprem`) | Trust about names-only code (D13b), as today. Its `#Hmembers` is **a WP about the translated `RaftCluster.Members`, stronger than its proved spec** (STATUS "Premise fixes 4"): a validity about real translated code. Must be replaced by the proved `Members` spec plus a state fact before C7 (stage S11, D7). |
| `bootstrapRestartContract` (in `Hprem`) | New trust about names-only code; carries the same `#Hmembers` (`InvRestart.lean`, `bootOkR`); after S2/S3 its body includes `wal.restartOk` and `memStorRestarted`. Satisfiable: every conjunct is a claim about Go's `bootstrap`, testable (axiom-skill + Go test with the counting logger). D4. |
| `Hwpend`/`srvWinAdd` | **Must not appear** (false on real runs). Removed by S7 (R2s-A). |
| Rows 2-8 of R2d'a | Must not appear: S1 (2, 3), S7 (4), S4/S6 (5-8, proved from the image). |
| Scope restrictions R-S1..R-S7 (auth off, mvcc compaction off, static membership, `DedicatedWALDir = ""` and `ForceNewCluster = false`, graceful image in the same run, `dataDirsAbsent`, stop after the bootstrap log) | Decidable facts of the program's configuration and driver, true of `restartp` by construction; none is a hypothesis of the theorem (R-S3 only if Q39's law fails). |
| The request-id freshness across a member's runs | **Hidden in trusted code**: `TrustedCode/go_etcd_io/etcd/pkg/v3/idutil.lean`'s `Generator.Next` `assume`s no other generator issued the id (`nonissues/etcd-request-id-restart-reuse.md`: false if the clock goes back, or a restart within the millisecond, or more than 256 ids/ms since the previous start). Not in the theorem's text; prunes runs. Becomes load-bearing with restarts. D3. |
| `storage.diskOk`, `storage.dbOpensOk` | World assumptions about the disk (no failed `Save`; bbolt opens its file), already in the closed theorems. |

### S11. Close the restart contract's `#Hmembers` (about 1 wk, est.)
Replace `bootOk`'s and `bootOkR`'s `#Hmembers` (a WP of the translated `Members()`) by the proved
`RaftCluster.Members` spec over the in-memory members (`Hmem`/`clusterMem`) and the directory fact
(`memberDirIs`). Benefits every existing closed theorem too. Not restart-specific; can run any time
after pf8.

### S12. Crash semantics ("kill" in etcd robustness's sense): a separate track (R6), months
Robustness's `KillFailpoint` is SIGKILL, and most of its gofail failpoints (`raftBeforeSave`,
`backendBeforeWriteBackBuf`, ...) panic the process mid-write: crashes, not graceful stops. Covering
them needs R6 (`notes/restart-plan.md`, R6): file semantics with crashes under the WAL and bbolt
(the `osfs` extension of `notes/osfs-ext-plan.md`, already used by `examples/osfs/{crashlog,
bboltfs}`, or `durableExt`), the WAL proved over it or behind a crash-aware contract (torn tails,
`Repair`, segment cut/rename, preallocation), bbolt's commit order (the bbolt v2 proof is at U0b),
the backend behind the WAL after a crash (the consistent index committed in batches: R2s's
`i ≤ σ.commit` weakening, HS2), and the leader's acknowledged writes resting on followers' fsyncs.
Raft's own crash durability is already proved (`kvdurable_porcupine_safe`). Estimate: 3-6 months
(est.), not refined here. It needs new world assumptions about the disk (D1).

## 4. Sizes, checkpoints, user decisions

### Sizes (est.)

| Stage | Work | Depends on | Can start |
|---|---|---|---|
| S0 re-baseline | 2-3 d | — | now |
| S1 rows 2-3 (+ `Hwpend` (a) +1-1.5 wk if chosen) | 1-1.5 wk | S0 | now |
| S2 WAL `ReadAll` + sized | 1.5-2.5 wk | S1 (DurAgrees), W1 for the Freeze | now (S2b first) |
| S3 raft restart path (probe, B1, Q39) | 3-4 wk | S0 | now |
| S4 hubs at `snap0`, `run` | 1-2 wk | S1, S3's probe | after S1 |
| S5 HS1, `lateWBR` | 0.5-1 wk | pf8 (`NewAuthStore.lean`) | after pf8 |
| S6 `NewServer` both boots | 2.5-3.5 wk | S2, S3, S4, S5, **pf8** | after pf8 |
| S7 R2s-A | 6-9 wk (5-7 path) | S3's probe; step 3 after S4 | steps 1-2 after the probe |
| S8 etcdstart, links, F4 | 1-2 wk | S6 | — |
| S9 `restart3_safe` | 2-3 wk | S7, S8, per-type stage B | — |
| S10 schedule theorem | 5-8 wk | S9, stage B (grpc `Stop`) | Go driver and test now |
| S11 `#Hmembers` | 1 wk | pf8 | after pf8 |
| S12 crash (R6) | 3-6 months | everything above | separate Scope |

Totals to `restart3_safe` (S0-S9): about 22-33 weeks of work; with two sessions (one on S1/S3/S4/S6,
one on S2/S7) about 12-18 weeks of calendar. The schedule theorem adds 5-8 weeks, part of which (the
Go driver, its test, the grpc `Stop` design) overlaps. These are r2db §14's figures less what
mvccfull retired (about 3.5-5 weeks) and less Q32 (a) and Q33 (a), plus S2b, S10 and S11.

### Checkpoints (report at each)
C1 (S1: row 3 true, R2d'a non-vacuous on quiet stops) · C2 (S3's probe) · C3 (restart boot linked
below `NewServer`) · C4 (`BuildServer.specRestart` proved) · C5 (S7: no restart-only premise) · C6
(`restart3_safe`) · C7 (`etcd_restart_safe`). Each Freeze package goes to a fresh `spec-reviewer`; each
trusted text to the `axiom` skill before its Freeze.

### Decisions for the user (via etcd-grove-81)

- **D1. Graceful stops or kills.** The track as planned proves graceful stops (`HardStop`, Q4 (a)):
  every write is visible to the next incarnation, synced or not. That covers etcd's restart path
  (WAL replay, snapshot load, the backend image, catch-up) but **not robustness's kill failpoints**,
  which are crashes. Options: (a) graceful now, the closed theorem says "stop and restart", crashes in
  R6 later; (b) crashes first, which means new world assumptions about the disk (the device honours
  cache flushes, sector writes are atomic, no media errors, `osfs-ext-plan.md`'s list) and R6's
  months. *Recommended: (a)*, with the theorem's docstring saying it does not cover kills.
- **D2. R2d'b's shape (Q41, pending since 2026-11-07).** *Recommended:* FULL's F4 (many restarts:
  the schedule theorem needs it), without Q32 (a) (the start tag; R2s-A makes row 4 moot) and
  without Q33 (a) (deleted by R2s-A), with R2s-A started in parallel after S3's probe. Not FULL, not
  the CUT; it is the CUT's statement minus its one-restart limit, at roughly the CUT's cost.
- **D3. Request ids across restarts** (a world assumption hidden in the trusted `Generator.Next`).
  Options: (a) accept it as a listed world assumption (clock monotone across restarts, fewer than
  256 ids per ms since the previous start) and say so in the theorem's docstring; (b) a fork change
  (seed the generator above the ids in the replayed WAL) so the model needs no `assume` at restarts;
  (c) keep `restartp`'s schedules from restarting within a bound after a start (still needs the
  clock). *Recommended: (a) now, (b) as a later cleanup if cheap*; this is the user's because it is
  a fact about the world the proof cannot check.
- **D4. The restart contract: a hypothesis or an axiom.** Today `bootstrapContract` is a premise in
  `Hprem` (D13b); `bootstrapRestartContract` would join it. The tcb report does not list premises.
  *Recommended:* keep both as premises (no change of practice), attacked with the `axiom` skill and
  backed by the Go test; list them in the theorem's docstring and STATUS; Q3 (b) (translate
  `bootstrap`'s restart path, the WAL behind axioms) later.
- **D5. The gRPC server's stop** (S10): a new trust-boundary spec, `Stop` with `WaitForHandlers`,
  returning the handler pool, and the driver changed to use it; ordered after the per-type stage B.
  *Recommended: yes*, as stated.
- **D6. The closed theorem's scope** (auth off, mvcc compaction off, static membership, no
  dedicated WAL dir, no force-new-cluster, graceful image in the same run, data directories fresh at
  program start, a stop after the bootstrap log): approve as listed (all true of `restartp`).
- **D7. `#Hmembers` before the restart theorem** (S11). *Recommended: yes* (a validity about real
  translated code in every boot contract).

## 5. Overlap with premise-fixes-8

pf8's scope (`notes/decisions.md`, "Premise fixes 7", last list): `FromIncomingContext`,
`AuthInfoFromTLS`, `isReqAuth`/`isReqAuthBound` (false when `ClientCertAuthEnabled`), `Invoke`/`NewStream`'s
`ctx.Value(mdOutgoingKey)`, `FromOutgoingContext`, `watchCtx`'s clause, `streamKeyFromCtx`,
`WithCancelTodo`. Its working lists (`/shared/tmp/premise-fixes-8/aifc-files.txt`, `l2.txt`,
`rcl-auth.txt`) and its worktree (`/shared/etcd-grove-pf8`, clean but one scratch Go test) show no
Scope yet (`scope.md` absent at the time of reading).

**Shared files** (restart stage → pf8 item):

| File | Restart stage | pf8 | Conflict |
|---|---|---|---|
| `Spec/go_etcd_io/etcd/server/v3/auth/NewAuthStore.lean` (trusted) | S5 (HS1: `authBoot` disjunct, `:127`) | `isReqAuth` in its post (`:136`), likely restated with `ClientCertAuthEnabled` | **direct**, small; S5 after pf8 |
| `Proof/.../etcdserver/NewServer.lean` (2934 lines) and `Spec/.../NewServer.lean` | S6 (B5: the boot sum, most of the proof) | `isReqAuth`'s supply from `NewAuthStore`, the `ClientCertAuthEnabled` field (`Proof :1626, 2036, 2080-2085`; spec `:373`); `rcl-auth.txt` lists `etcdserver_NewServer` as a reverse caller of `AuthInfoFromTLS` | **direct, large**; S6 after pf8 |
| `Proof/.../etcdserver/InvStart.lean` (`isServerOn`: `authStore ↦□ v.auth ∗ isReqAuth v.auth E.RD`, `:111`) | S4/S6 (hubs) | `isReqAuth` | moderate; rebase |
| `Proof/.../etcdserver/AuthCompRows.lean` (`:679`, `isReqAuthBound`) | S1 (`srvRunRestartR`, the hubs), S4 (hubs at `snap0`), S7 (window texts) | `isReqAuthBound` | moderate; distant lines |
| `Proof/.../etcdserver/ServerOnDefs.lean` (`:231-238`) | S4/S6 if the built hubs' auth rows move | `isReqAuthBound` | low |
| `Proof/.../etcdserver/InvBoot.lean` (`bootCfgOk`, `bootOk`) | S0 audit, S11 (`#Hmembers`); `bootstrapRestartContract` reads `bootCfgOk` by name | in `l2.txt`, apparently for `ctxs` (a false positive); a `ClientCertAuthEnabled = false` added to `bootCfgOk` would change both contracts' meaning without a text conflict | low (watch semantic change) |
| `Proof/.../examples/lib/etcdstart/Defs.lean` (`srvTLSId`, `:539-542`), `BuildServer.lean`, `StartStop.lean` | S8 (B6) | `rcl-auth.txt` lists `etcdstart_*`, `cluster3_*` as reverse callers | moderate; S8 after pf8 |
| `Proof/.../etcdserver/Link.lean`, `Results.lean`, `api/v3rpc/Link.lean` | every linking stage | regenerated | trivial (regenerate) |
| `examples/lib/cluster3/*`, `Proof/.../examples/lib/cluster3/*` | S10 | reverse callers (`cluster3_StartCluster`, `StartMember`) | S10 is after pf8 anyway |

**Not shared** (no pf8 list names them; checked by grep for `isReqAuth`, `AuthInfoFromTLS`,
`ClientCertAuth`, `FromIncoming`, `WithCancelTodo`): `InvRaftNode.lean`, `InvWal.lean`,
`WalApi.lean`, `WalRecs.lean`, `InvRestart.lean`, `InvRun.lean`, `ApplyRDefs.lean`, `RestReplay.lean`,
`EtcdServer__run.lean`, `raftNode__start/stop`, `newRaftNode`, `NodeStart.lean`, `InvNodeStart.lean`,
`StopShutdown.lean`, raft's tree, the snapshot path's `srvNet`/`SnapRO`/`InvApplyAll`/`ApplyAllSnap*`/
`MergedImageOn`, and the Go programs.

**Recommended sequencing**:
1. **Start now, in parallel with pf8:** S0; S1 (rows 2-3; its full build is `InvRaftNode`-rooted,
   which pf8 does not edit, but schedule it outside pf8's gates per the landing rules); S2 (WAL);
   S3 (probe, then B1, Q39, `newRaftNode`); S7's steps 1-2 (the snapshot certificate at `j ≥ i`)
   after S3's probe; the Go side of S10 (driver kinds, the counting test, the `grpc.Stop` design note).
2. **After pf8's `isReqAuth`/`AuthInfoFromTLS` part lands:** S4 (if it touches `InvStart`), S5, S6,
   S8, S11. If pf8 is quick (its own estimate), S4 can simply wait; if not, S4 goes first and pf8
   rebases over `AuthCompRows`' few restart lines (pf8's change there is one lemma).
3. **After the per-type stage B:** S9's adequacy (every `_safe` result waits for it) and S10's
   `grpc.Server.Stop` spec.
4. Landing: S1 and S4 each need a full build (`InvRaftNode` 1047 importers, `AuthCompRows` 744);
   never while pf8's gates run (`notes/spec-first-plan.md`, landing lock; memory "No lean moves during gates").

## 6. Risks, including premises already on `lean`

**Known false or suspicious on `lean` today**
1. **R2d'a row 3 (`rnWalCommitAbove`, `InvRaftNode.lean:393`) is false** at the start of almost every
   restart; **`Hwpend` (`InvRun.lean:57-70`) is false** on every later-leadership run. Disclosed
   (STATUS, decisions "R2d'a's disclosure corrected"); no closed theorem carries them; the frozen
   restart triple is vacuous on those runs until S1/S7.
2. **`bootOkR`'s `#Hmembers`**: a WP of translated code (`Members()`) stronger than its proved spec,
   copied from `bootOk`. The same flaw is in every existing boot contract (STATUS "Premise fixes 4").
3. **`bootOkR` has drifted from `bootOk`**: `%Hraft` says only `bv.lg' ≠ null` where `bootOk` now
   says `bv.lg' = cfg.Logger'` (pf6). Weaker, so not unsound, but S6 will need the stronger claim;
   other drifts to be found by S0's diff.
4. **`memStorRestarted` is opaque** (`InvRestart.lean:342`): the contract's post says nothing usable
   about the restarted storage, so no restart is provable from it; defining it (S3) is a change to
   trusted text.
5. **The stop's files are unsized** (`srvFiles` at `walFiles … false`; the loop's `Save`s unsized):
   with no `ReadAll` fact, a restarted node's entry sizes are unbounded in the model, so `out_size`
   (a `sorry` under every server `_safe` result) has no Go argument for restarted nodes (its own
   docstring). S2b.
6. **The trusted `Generator.Next` assumes id freshness across a member's runs** (D3). Harmless with
   one start per member; load-bearing with restarts.
7. **`HardStop` only for a member that never served gRPC**: true but restrictive; blocks any
   schedule that restarts a serving member until D5.
8. **W1 not landed**: `purgeFile` does not take `walPurgeRight`, so `wal.restartOk` (the first
   exported reader of `walFiles`) would rest on an unenforced stop order (review gap 9). A
   prerequisite of S2's Freeze.
9. **`clusterImageOk_restModel`'s ids form** (axiom; `notes/axiom-review/clusterimage-ids.md`:
   survives, "stronger than its argument"; the S4 sweep repair added the `ClusterVersionSet` premise).
   Reached by the restart's snapshot arm; re-attack with S7.

**Risks to the plan**
- **Per-type stage B** is NOT READY (r2 review). Until it lands, every `_safe` result is
  untrustworthy, so C6/C7 cannot claim anything; S10's `grpc.Stop` spec depends on its pool design.
- **`NewServer`'s 2934-line proof over two boots** (S6) stays the least certain item; the week-8 guard
  (B5 deferred, `specRestart` stated, not linked) bounds the damage.
- **R2s-A** has no Draft or probe yet; the receive side (an image above the snapshot index, then a
  replay window at the receiver) reuses S4's window, so S4's design must not assume the window starts
  at boot.
- **Q39's law** may not exist without per-entry facts; fallback R-S3 as a contract premise.
- **Restarted members and partitions** (S10): a cut held by a running member toward a restarted one
  persists while the restarted side's is gone; the partitioner's facts about a server must survive
  its stop (a persistent fact of a stopped server's transport). Check in S10's Draft.
- **Thread budget across incarnations**: leaked goroutines keep their tokens; `steps.length`'s bound
  must be derived from per-incarnation counts (bounds plan), not chosen.
- **Crashes stay out** (D1 (a)): a reader of the theorem could take "restart" for "kill". The
  docstring and STATUS must say graceful.
- **Build and disk**: `/shared` has about 70 GB free (2026-11-11); two parallel restart worktrees plus
  pf8's need the coordinator's build moves, not copies.

## Intermediate milestones: a ladder of closed crash theorems (USER approved 2026-11-11)
Each rung validates one layer's crash spec in a real program before the next depends on it.
1. etcd_wal_safe — the WAL alone under power loss (WAL W1.5/W4; planned).
2. Raft over etcd's real WAL with crashes — a kvdurable variant whose raft storage is etcd's WAL (+ MemoryStorage as etcd uses it): raft restart from walRead, R-C1 (entries without HardState, lower commit), Ready ordering; reuses kvdurable's proof. After W4; restart S3's probe feeds it.
3. Backend + consistent-index replay under crash (server side) — mvccfull + bbolt crash images (rollback to last commit), apply skipping ≤ consistent index, backend ahead of WAL; reuses mvccfull. Can start in parallel.
4. etcd_restart1_safe (server side) — one member, txnlin's KV workload, power-loss crashes/restarts in a loop; checks linearizability across restarts and no lost acknowledged write; real bootstrap/WAL/snapshot/RestartNode/replay/backend path; no peers (avoids S7 merged-snapshot following and stopping a serving member). Reuses etcd_txnlin_safe + rungs 1-3.
5. restart3_safe and the schedule theorem (peers, snapshot catch-up incl. C-W1's path).
Open for rung 2's Scope: crash as an in-process abandoned incarnation (kvdurable style, faithful only if the image comes from the WAL/bbolt crash relations) vs. one process per member.
