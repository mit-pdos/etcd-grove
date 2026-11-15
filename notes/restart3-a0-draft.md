# restart3 A0: the R2s-A Draft and probe (2026-11-15, for etcd-grove-81; DRAFT revision 1, nothing landed)

Revision 1 applies review round 1 (`/shared/tmp/restart3-a0/review-r1.md`): M1 (A-g is graceful-only), M2 (the
backward install can panic a catching-up watcher: confirmed by an mvcc test, the nonissue rewritten), m1-m9.

Plan: `notes/restart3-scope.md` §2.3, stage A0. Route (A) and the go/no-go after A0 were decided by the user
(2026-11-15); D-R3-2/3/4/6 by etcd-grove-81 (`questions.md`). Branch `restart3`, worktree
`/shared/etcd-grove-auth3`, off `lean` `c3da59fa29`.

Inputs read: `notes/restart3-scope.md`, `notes/restart-scope.md` (R2s-A, S8-S10), `notes/decisions.md` ("R2s",
"D21" M0-M6), `notes/restart-s7-{scope,probe,p2a,freeze,handoff}.md`, branch `r2db`'s `notes/r2db-scope.md`
(§10, §12, §14), and the code: `InvApplyAll.lean` (`srvNet`), `rafthttp/Net.lean` (`NetPayload`,
`netSnapBundle`, `snapDirInv`), `InvImage.lean`/`ImageOn.lean` (`dbImage`, `srvImageM`), `ApplyRDefs.lean`
(`winNoMergedSendR`), `InvRun.lean` (`srvWinPend`), `InvRaftNode.lean` (`rnSnapTermAbove`, `rnRestartOk`,
`rnSnapMsg`), `InvRestart.lean` (`srvDiskImageAt`, `bootstrapRestartContract`, `srvRestartRows`), `WalApi.lean`
(`wal.stopImage`), `KVStoreApi.lean`/`KVStoreCore.lean` (the server's KV store invariant), `InvRequest.lean`
(the applied index), `Spec/.../EtcdServer__applyAll.lean` (`specBatch`, `specSnapM`) and its proof's merge
branch, `EtcdServer__run.lean` (`applyResR`, `run_job_snapC`). Go: etcd at the fork pin `2eaeb872bc`
(`server/etcdserver/server.go`, `snapshot_merge.go`).

Abbreviations as in the Scope: `E/` = `Proof/go_etcd_io/etcd/server/v3/etcdserver/`, `SE/` = its `Spec/`
twin. Estimates are marked (est.).

---

## 0. Result in one paragraph

**R2s-A as recorded hits a blocker.** Following the merged snapshot in the ghost (`decisions.md`, "R2s")
needs the receiver to install an image that is *older* than its current backend: a member whose backend
is ahead of its raft commit (after an install from a restarted leader still inside its replay window)
can then accept another leader's snapshot at an index between its commit and its backend's consistent
index, and Go moves the backend backward and re-applies (the Q16-3 review's F1 run, `decisions.md`
"R2s"). The R2s decision planned "the KV ghost reset at an install". But the server's KV store invariant,
restated over mvcc's API on 2026-11-06 (strict M1, after the R2s decision), keeps the store's log as the
authority of a **monotone list** whose fragments (`kvLogLb`) are persistent floors held by readers,
watchers and the writer itself, and its restore builder restores only **to an extension**
(`KVStoreApi.lean:114-120, 176-180`). A backward restore cannot re-establish it (probe P1, checked).
Making it possible means re-founding every floor client of the store (reads, watches, the applied
index's `appliedMonoMap`): est. +6-10 wk on top of the Scope's 5-8, with no design yet. **So A1 as
recorded is a no-go by D-R3-2's rule.** Two variants of route (A) avoid the backward install, both by a
change to the goose fork of etcd. The small one, **A-g**, defers a merged snapshot while the leader is
inside its own replay window (`ep.appliedi < ConsistentIndex()`), reporting the snapshot failed so that
raft retries it after the window. With A-g every merged image is at its own raft index, no backend is
ever ahead of its raft commit, and R2s-A's other pieces disappear: no certificate change, no receiver
window, no change to the stop's WAL slot or the restart contract, no new raft law, no trusted text
touched. The rows (`winNoMergedSendR`, `srvWinPend`, row 4, `srvRestartRows`) are deleted, because the
guard refutes the in-window merge that they excluded (probe P2, checked; Go: a smoke test, 6/6, in which the
guard never fired). **A-g is graceful-only** (review M1): after a crash the backend's consistent index can
be above the WAL's commit, so a backward install is reachable with no window sender; restart3 covers
graceful stops only (N2), and the crash case stays with a crash-model theorem (A-r covers both causes).
**A finding on the way** (review M2, confirmed): Go itself can panic on a backward install, when a watch is
catching up at that member (`nonissues/etcd-backward-snapshot-install-panics-watcher.md`, an mvcc test that
panics; not yet reached through etcd's own paths). **Recommended:
go on route (A) with A-g** (A1 est. 2-3 wk, the route 5.5-8 wk of work), which needs the user's approval
of the fork change. B0 stays the fallback if the user rejects any fork change.

## 1. What is on `lean` (corrections to the plan's inputs)

- **More `Hwpend` hubs** (review m1): `srvBuiltG` (`E/ServerOn.lean:186`), `isServerBuiltOn` (`E/StartOn.lean:95`),
  used by the auth examples; `E/LeaseRun.lean:14` names `srvWinPend` in its header.
- **`srvWinSupply` and `srvWinAdd` do not exist in Lean.** They are r2db's proposed Q33 redesign (`r2db
  §4.4-§4.5`), never built (CUT's R-2 discussion). Their "deletion" is a notes-only item: strike them from
  `notes/restart-scope.md` (R2s-A, S1) and `notes/restart3-scope.md` §2.3. What exists: `srvWinPend`
  (`E/InvRun.lean:62`, the hubs' `Hwpend`: `E/AuthCompRows.lean:229, 391`, `E/InvStart.lean:287`,
  `E/InvBuild.lean:335`), `winNoMergedSendR` (`E/ApplyRDefs.lean:108`, `SE/EtcdServer__applyAll.lean:100`),
  row 4 `rnSnapTermAbove` (`E/InvRaftNode.lean:464`, inside `rnRestartOk:494-498`), `rnSnapMsg`'s `t0`
  bound (`E/InvRaftNode.lean:203-208`), and `srvRestartRows` (`E/InvRestart.lean:714`, a premise of
  `NewServer.specR` and, through `□ ∀ A σ`, of etcdstart's `newServerMode/newServer/BuildServer.specRestart`).
- **"The raft API law, a snapshot's index above the receiver's commit" already exists**: `readyRest_snap`
  (`Proof/go_etcd_io/raft/v3/InvNode.lean:969`, `hardState.Commit' < snapIdx`), used by
  `rnRestartOk_winAbove` (`E/InvRaftNode.lean:542`). R2s-A would need it against Go's applied index (`ai ≤
  commit < snapIdx`), derivable with the loop's commit fact (`rnLoopTokP`); no raft interface diff.
- **The only consumer of row 4** is `winNoMergedSendR`'s `rt ≤ t0` arm (`E/EtcdServer__applyAll.lean:410-414`,
  through `rnSnapMsg`'s bound); row 1's only consumer is `winNoMergedSendR`'s right disjunct, supplied by
  `run` from `Hwpend`. So whatever discharges the in-window merge deletes all four.

## 2. R2s-A as recorded (the Draft the brief asked for)

### 2.1 The certificate at a consistent index `j ≥ i` (step 1)

`srvNet`'s image certificate (`E/InvApplyAll.lean:94`, `img := fun i D => srvImageM γ.authOn γ i D`) becomes
```lean
def srvImageGe (on : Bool) (γ : SrvRaft) (i : w64) (D : backend.Data) : IProp GF :=
  iprop(∃ j : w64, ⌜uint.Z i ≤ uint.Z j⌝ ∗ srvImageM on γ j D)
-- srvNet γ := { …, img := fun i D => srvImageGe γ.authOn γ i D, … }
```
`srvImageM on γ j D` already says `D`'s consistent index is `j` and `D` is the image of a committed prefix
of length `j` (`dbImage`'s `srvRLogLb γ A`, `uint.Z j = |A|`), so the certificate needs nothing else.
Probe P3 (checked): the definition is a valid `NetPayload.img` and today's certificate gives it at `j = i`
(`probe_P3_ofEq`). Every place the certificate is named changes with it: `srvNet` (exported: its `Freeze`),
`srvDiskImageAt`'s snapshot directory (`snapDirInv … (srvImageM γ.authOn γ)`, `E/InvRestart.lean:188`, the
restart contract's image), `srvSnapRO`'s directory (`E/SnapRO.lean:442`), the receiver's
`snapRecv_image`/`snapRecv_imageOn` (`SnapRecvFacts.lean`, `SnapRecvOn.lean:477`). The trust-boundary texts
that carry it (`Snapshotter.SaveDBFrom`, `Transport.Start`/`SendSnapshot` through `netSnapBundle`,
`OpenSnapshotBackend`) are generic in `img`: their text does not change, the instance's meaning does, hence
the re-attack (§2.5).

**The sender** (step 2). `applyAll`'s merged-send branch at a pending window: Go merges at `snapi =
ep.appliedi` (`ai`, inside the window `ai < ai₀ + |A₀|`) a backend whose consistent index is the window's
`ciEff ≥ ai₀ + |A₀|` (`kvBatchR`), so the image is `srvImageM … (ai₀ + |ghostOf rp A|) D` (the ghost log is
the backend's log, committed: `srvRLogLb γr.raft rp.A₀`), and the certificate `srvImageGe … ai D` at `j =
|ghostOf|`. What `mergedCreate_window` (`SnapSendBranch.lean`) proves at `hciE : ciEff = ai'` must be
redone at `ciEff = ai₀ + |ghostOf rp A|`, with the rest buckets at the replay arm (`srvRestRp … A₀ r`):
the image's rest buckets are the backend's, `bkRestAtL` of `pre ++ A₀`, while the in-memory members are
`restReplay`'s; `imageRestAt` reads only the backend. `winNoMergedSendR` and its `T`, `srvSnapBagN` leave
`specBatch`.

### 2.2 The receiver: an image above the snapshot index, then the replay window (step 3)

Go (`server.go:1021-1180` at `2eaeb872bc`): `applySnapshot` panics unless `Index > ep.appliedi`, opens the
snapshot's `.snap.db` (consistent index `j ≥ Index`), sets `ep.appliedi = Index`, and the entries
`(Index, j]` are then replayed v2-only by the consistent-index guard (`shouldApplyV3`). That is a restart
point at the install: `rp' = ⟨b := Index - ai₀, A₀ := A_j⟩` (`RestReplay.lean:56`), Go's log `A'` of length
`Index`, the ghost log `ghostOf rp' A' = A_j`. Draft of `applyAll.specSnapM`'s change
(`SE/EtcdServer__applyAll.lean:198-305`):

- premises: drop `uint.Z g < uint.Z sv.Index` (A8) in favour of `uint.Z ai < uint.Z sv.Index` (Go's guard,
  from `readyRest_snap` and the loop's commit fact); the payload's certificate `srvImageGe`;
- post: `epAppliedI ↦ sv.Index` (unchanged), the ghost applied index `g' = j`, `kvAppliedM … A_j`,
  `srvRestR E' γr rp' A'`, `kvBatchR`-style facts at `rp'` (`ai₀ + |A_j| ≤ ciEff' = j`), `srvSnapOwn … g'`;
  `run`'s loop invariant `applyResR K C rp A` with `rp` existential (`E/EtcdServer__run.lean:130`);
  `run_job_snapC`'s `hwin` premise dropped.
- `applySnapshot.specSnapM` (`SE/EtcdServer__applySnapshot.lean`): the image at `j`, its post's `A'` the
  image's log `A_j` (today: of length `Index`).

**The blocker: `j` can be below the receiver's ghost index.** With window senders, a receiver's backend
can be ahead of its raft commit (`j > Index`), and then a second snapshot from a member without a window,
at an index in `(commit, j)`, is accepted by raft (`raft.go:1877`) and by Go (`Index > ep.appliedi`), and
Go restores the older image (F1: backend 100 → 70, then 71..100 re-applied v3). Go is correct (linearizable
reads cannot see it: a read's index is at least the leader's commit, which covers 100 once a read saw it;
watchers are protected by `watchableStore.Restore`'s `restore` flag), but the proof cannot follow:

- the server's store invariant `kvStoreInv` (`KVStoreApi.lean:114-120`) holds `monoListAuthOwn γs.slog 1
  σ.log`, its floors `kvLogLb γs L = monoListLbOwn γs.slog L` are persistent, the writer mints one at every
  state (`kvAus.law`'s last clause), and the restore builder is "a restore to an extension" (`log <+:
  log'`, `KVStoreApi.lean:176-180`; `restoreArgs.law`'s `A <+: A'`). Probe P1 (checked,
  `Scratch/R3A0ProbeKV.lean`): `probe_P1_floor` (the authority extends every floor),
  `probe_P1_noBackward` (a log not extending a floor is refuted), `probe_P1_writerFloor` (the floor at the
  writer's log exists before any restore). The notified log `γs.nlog` (watchers' `histLb`) is a monotone
  list too.
- the applied index's invariant (`srvAppliedBody`, `InvRequest.lean:2340-2350`) keeps `appliedMonoMap M`
  and `srvApi.kvLogLb E.γs L` of the applied log: the ghost applied index and its logs cannot go backward
  (`applied_jump` only raises), which the R2s decision's "monotone applied index at Go's index" re-keys,
  but its logs are still the store's floors.

Nor can the ghost stay ahead of the store (review m6): `mvccState γ σ` is the physical store, tied to `γs.slog`
exactly (`KVStoreApi.lean:115-116`), and the floor read law (`:182`) is false of Go under a backward install
(two serializable reads see the revision decrease). So A-u is not a re-proof but a weaker read guarantee.
And Go itself can panic there (review M2): `watchableStore.Restore` marks only the synced watchers `restore`,
so an unsynced watcher above the restored revision trips `chooseAll`'s panic (confirmed by
`TestZZBackwardRestoreUnsyncedWatcher`, the nonissue's test). So R2s-A needs either a store invariant whose floors survive a truncating restore (every floor client:
the read path's `kvReadAt`, the watch path's `histLb`, the applied logs, the cache's and k8s's watch
results that rest on them), or an argument that the backward install never happens, which is false of Go.
Recorded as `nonissues/etcd-backward-snapshot-install-panics-watcher.md` (behavior etcd does not
guarantee against; blocks this design, not the property).

### 2.3 Deletions (step 4)

`winNoMergedSendR` (+ `winNoMergedSendR_nil`, its `T` and `srvSnapBagN` in `specBatch`), `srvWinPend` (+
`srvWinPend_first`, the hubs' `Hwpend`), row 4 `rnSnapTermAbove` (out of `rnRestartOk`; `NodeStartSpecR`'s
installer, `newRaftNode.lean`), `rnSnapMsg`'s `t0` bound (`processMessages`), `srvRestartRows` (+
`RestartRowsSingle.lean`), the `□ ∀ A σ, srvRestartRows` premise of `newServerMode/newServer/BuildServer.specRestart`
and of restart1's/restart3's drafts. `srvWinSupply`/`srvWinAdd`: notes only (§1).

### 2.4 Frozen or exported statements R2s-A changes

| Statement | Change |
|---|---|
| `srvNet` (`E/InvApplyAll.lean:94`, exported through `isServerApplyAll`, the transport axioms' instance) | `img` → `srvImageGe` |
| `EtcdServer.applyAll.specBatch` (`SE/EtcdServer__applyAll.lean:54`, frozen) | `winNoMergedSendR … ∗ T ∗ srvSnapBagN` deleted; `T` binder deleted |
| `EtcdServer.applyAll.specSnapM` (same file, frozen) | §2.2: A8 → Go's guard, post at `rp'` |
| `EtcdServer.applySnapshot.specSnapM` (`SE/EtcdServer__applySnapshot.lean`, frozen) | the image at `j`; post's log `A_j` |
| `EtcdServer.run` spec (`SE/EtcdServer__run.lean`), `isServerRunC`/`isServerBuiltC` (`E/AuthCompRows.lean`, hubs: requests to 82) | `Hwpend` deleted |
| `rnRestartOk`, `isRaftNode` (`E/InvRaftNode.lean`, 1047 importers), `NodeStartSpecR`, `newRaftNode.spec`, `bootstrappedRaft.newRaftNode.spec` | row 4 deleted; R2s-A: `\|a0\| ≤ commit0` weakened (a stop after an install from a window sender has `i > σ.commit`) |
| `NewServer.specR` (`SE/NewServerR.lean:107`), etcdstart `newServerMode/newServer/BuildServer.specRestart` | `Hrows` deleted |
| `wal.stopImage` (sealed) and `bootstrapRestartContract` (trusted) | §2.5 |
| `srvDiskImageAt`/`srvDiskImage` (`E/InvRestart.lean:150-200`) | the directory's certificate `srvImageGe`; `wal.stopImage`'s new form |
| `etcd_restart1_safe` | its rows are discharged inside, but its premise `bootstrapRestartContract` changes (§2.5, item 2: weaker) |

### 2.5 Trusted texts R2s-A touches (each a hard stop)

1. **The snapshot slot re-attack**: the axioms generic in `img` (`snap.Snapshotter.SaveDBFrom`, the
   transport's `Start`/`SendSnapshot`, `storage.OpenSnapshotBackend`) at the new instance, and
   `membership.clusterImageOk_restModel` (reached by the receiver's snapshot arm at `A_j`): an `axiom`-skill
   attack, no text change expected.
2. **The stop's WAL slot inside `bootstrapRestartContract`**: `wal.stopImage`'s `σ.b ≤ i ≤ σ.commit` →
   `σ.b ≤ i ∧ ∃ p, σ.b ≤ p ≤ σ.commit ∧ confAt cl p m` (the R2s decision's finding 2; `etcd` itself expects
   `consistent_index > Commit` after such an install, `bootstrap.go:613-621`); the contract's
   `⌜σ.b ≤ uint.nat i ∧ uint.nat i ≤ σ.commit ∧ …⌝` (`E/InvRestart.lean:661`) the same, and `rnRestartOk`'s
   `|a0| ≤ commit0` with `rnRestartOk_winAbove` re-derived from the configuration point. The contract is a
   premise of `etcd_restart1_safe`: its text changes (a weaker premise).
3. **The raft API law**: none new (§1, `readyRest_snap`).

### 2.6 Estimate of R2s-A as recorded

The Scope's 5-8 wk did not include the store invariant. Variant **A-u** (keep upstream's behavior, re-found
the floors): +6-10 wk (est.; no design: each floor client must tolerate a truncation to a committed
prefix, the watch path's proof of `watchableStore.Restore`'s `restore` flag included), so **A1 11-18 wk:
no-go**. Variant **A-r** (a fork change on the receiver: when the snapshot's index is at or below the
consistent index, keep the backend, which is a committed prefix extending the snapshot, release the
`.snap.db`, and set `ep.appliedi = Index`): no backward install, the rest of R2s-A as drafted above, A1 5-8
wk plus the receiver's change (est.).

## 3. Variant A-g: no merged snapshot inside the sender's window (recommended)

### 3.1 The Go change (the goose fork, `server/etcdserver/server.go:1013`, the merge's select)

```go
if m.GetTerm() == apply.raftTerm && m.GetSnapshot().GetMetadata().GetIndex() <= ep.appliedi {
    if ep.appliedi < s.consistIndex.ConsistentIndex() {
        // inside the replay window the backend is ahead of the applied index: a merged snapshot
        // would carry an image newer than its index; let raft retry it after the window
        s.ReportSnapshot(m.GetTo(), raft.SnapshotFailure)
    } else {
        merged := s.createMergedSnapshotMessage(m, ep.appliedt, ep.appliedi, ep.confState)
        s.sendMergedSnap(merged)
    }
}
```
(the probe's copy: `/shared/tmp/restart3-a0/ag-guard.patch`, with a log line). The fork already carries two guards at
this select: the index guard is for the proof; the term guard fixes a real bug
(`issues/etcd-merged-snapshot-stale-term.md`). A-g would be a second change made for the proof. Liveness: without `ReportSnapshot`, raft's progress
would stay in `StateSnapshot` (paused) until a leadership change; with it, the progress goes to
`StateProbe` and raft resends a snapshot at a later heartbeat response, by then past the window (the
window ends once the replay is applied). Upstream behavior is correct (§2.2); the change is for the proof
only, so it is the user's to approve (D-A0-1).

**Considered and rejected (A-c, review m6):** stamp the merged snapshot at the consistent index instead of
`ep.appliedi`: no deferral, but the snapshot's term and `ConfState` at `ci` are not known to the sender (the
replayed entries are v2-only, its raft log may not hold them at a stamped index past its applied one, and
raft's `isMessage_snap_recontent` needs `index ≤ ai`).

**Go evidence, a smoke test only** (`/shared/tmp/restart3-a0/ag2-run-*.txt`): restart3probe setting A against the patched server
(`go test -modfile` with a local replace of `server/v3`), 6 runs in separate processes, 32G cap,
`GOWORK=off`: 6/6 pass the exact check (155 pairs, version 1, revision 156), a merged snapshot sent to and
installed at the restarted member in every run, the guard never fired (no leader inside its window in
this program). A forced in-window leader (r2db §12's run 8 harness) would show the guard firing and the
retry; that is A1's first step (§3.4).

### 3.2 The proof change

At the merge (`E/EtcdServer__applyAll.lean:466-480`), the guard's read is `wp_ci_get` (`E/InvServer.lean:187`,
`applyThread γ st''` and `applyBackend`, both in context, `st''.pending = false` from `loopOk`), returning
`ciEff γ st''.k`. When the guard is false, the window is over: probe P2 (checked,
`Scratch/R3A0ProbeGuard.lean`) `probe_P2_guard` (`ai₀ + |A₀| ≤ ciEff st ≤ ciEff st''` and `¬ ai' < ciEff st''`
give `|A₀| ≤ |A ++ un|`, which is `hW`), `probe_P2_ghost` (then `ghostOf_past`), and `probe_P2_guard_in` (inside
the window the guard holds: it defers exactly the in-window merges). From `hW` on, the existing branch is
unchanged (`hgai`, `hciE`, `mergedCreate_window`). The guard's true branch calls `EtcdServer.ReportSnapshot`
(`SE/EtcdServer__ReportSnapshot.lean`, needs `srvProcOk γn s id γd`, persistent, which `NewServer` makes for
the transport; it must reach `isServerApplyAll`: a hub row, a request to 82) or, if D-A0-2 chooses the
silent drop, nothing. The message `m` (owned, `rnSnapMsg`) is dropped either way, as at the term guard. With `srvSnapBagN` gone
from `specBatch`, the merge receives through `isServerApplyAll`'s bag at its existential `γm` (`γm.node =
γr.raft.raft`, `E/InvApplyAll.lean:131`; destructured as `-` today at `E/EtcdServer__applyAll.lean:107`), and
`srv_sentSnap_pos` takes `γm.id` (review m3; not yet checked in Lean).

Then the deletions of §2.3, all of them. Nothing of §2.1, §2.2, §2.5 is needed:
- every merged image is at its own index (`ciEff = ai'` at the merge, as today), so `srvNet`, the snapshot
  directory, `specSnapM` and the receive path are unchanged;
- **at a graceful stop and restart,** no backend is ever ahead of its raft commit (an install sets it to the snapshot's index, which raft
  committed; a restart's window has `|a0| ≤ commit0`), so `wal.stopImage`, `bootstrapRestartContract` and
  `rnRestartOk`'s `|a0| ≤ commit0` stay true as written;
- no backward install exists on graceful runs (a snapshot is above the receiver's commit, hence above its
  backend). After a crash it does (review M1): out of restart3's scope (N2).

### 3.3 Statements A-g changes, and trusted texts

| Statement | Change |
|---|---|
| `EtcdServer.applyAll.specBatch` (frozen) | `winNoMergedSendR … ∗ T ∗ srvSnapBagN` deleted, binder `T` deleted (weaker precondition, same post minus `T`) |
| `EtcdServer.run`'s spec, `isServerRunC`/`isServerBuiltC` (hubs, 82) | `Hwpend` deleted; `isServerApplyAll` gains `srvProcOk` (if D-A0-2 (a)) |
| `rnRestartOk`/`isRaftNode`, `rnSnapMsg`, `NodeStartSpecR`, `newRaftNode.spec`, `bootstrappedRaft.newRaftNode.spec` | row 4 and the `t0` bound deleted |
| `NewServer.specR`, etcdstart `newServerMode/newServer/BuildServer.specRestart` (linked) | `Hrows` / `□ ∀ A σ, srvRestartRows` deleted |
| `createMergedSnapshotMessage`'s spec | only its docstring (`rnSnapMsg`'s) |
| the Goose translation of `server.go` | regenerated from the fork's new commit (`etc/goose.py --project etcd`) |
| the hubs `srvBuiltG` (`ServerOn.lean:186`), `isServerBuiltOn` (`StartOn.lean:95`) (82) | `Hwpend` deleted |
| `applyAll.wp_proofBatch`'s callee specs, the server's `Link.lean` and the proof's interface | gains `consistentIndex.ConsistentIndex.spec`, `raftpb.Message.GetTo.spec`, `EtcdServer.ReportSnapshot.spec` |
| `applyAll_model` (`E/Results.lean:200-217`, exported) | restates `applyAll.spec`: text follows `specBatch`; docstring |
| SpecPlan's `EtcdServer__applyAll.lean:25-30` (the guard "is the code's") | the window test added; a `notes/specs-only/ledger.md` entry first |
| `examples/go.mod`'s replace of etcd (`etc/goose.py --check`) | bumped with the fork pin |
| `etcd_restart1_safe`, every other closed theorem | unchanged |

Trusted texts: none touched. Trust base: unchanged (no axiom, `sorry` or opaque). Interfaces to regenerate:
the server's and etcdstart's (rows gone).

### 3.4 A1 under A-g (est.)

| Step | Work | Est. |
|---|---|---|
| g0 | the fork commit (guard + `ReportSnapshot`), its Go tests (restart3probe A, etcd's `server/etcdserver` unit tests, a forced in-window-leader run showing the guard and the retry), the pin bump and translation (`etc/goose.py`); the user pushes the fork | 2-3 d |
| g1 | the merge branch over the guard (`wp_ci_get`, P2), `ReportSnapshot` (hub row `srvProcOk` in `isServerApplyAll`, via 82), the bag through `isServerApplyAll` (m3), the three new callees in `Link.lean` | 4-5 d |
| g2 | the deletions (§2.3) through the five hubs, `run`, `NodeStartSpecR`, `newRaftNode`, `NewServer.specR`, etcdstart, restart1/restart3 drafts; two full builds (`InvRaftNode`: 1047 importers) | 3-5 d |
| g3 | SpecPlan ledger entry and text; Freeze package (§3.3's table), interfaces, gates, tcb `--check` unchanged | 2-3 d |
| | **A1-g total** | **2-3 wk** (+1-2 d for m1-m3) |

### 3.5 The whole route under A-g (est.)

A1-g 2-3 wk + C1 (restart3's Go, workload of §4 of the Scope, counting test, translation) 3-4 d + C2
(example proofs) 1.5-2 wk + C3 (handler swap, D-R3-4) 0.5-1 wk + C4 (link, Freeze of the theorem) 1 wk =
**5.5-8 wk of work**, about 4.5-6.5 wk of calendar (C1-C3 in parallel with g1-g3: restart3's `startMember`
needs only the rows' deletion, g2). Against the Scope's route (A) 10-14 wk and B0 8.5-12.5 wk.

The theorem in plain words is the Scope's §2.1, of the fork with the guard: leaders compact, the stopped
member is caught up by a snapshot, it replays its WAL past a snapshot record; what the fork adds is that a
leader still replaying its own WAL defers a snapshot until it is past the replay.

## 4. Composition with the auth-on-leases restatement (`/shared/etcd-grove-rs56`, branch `auth-lease`)

That agent restates `EtcdServer.applySnapshot.specSnapM` (its `LogNoLease` premise `hnl` replaced at auth on by
"every leased key's lease is in the image's table", `auth-lease-s3a-draft.md` §5) and the auth-on snapshot
path (`SnapRecvOn`, `MergedImageOn`, `ImageOn`, `ApplyAllSnap`, `SnapApplyWalk/Post/KV`).

- **Under A-g** the receive path, the images and `specSnapM` are untouched by restart3. Conflict points:
  `SE/EtcdServer__applyAll.lean` (both edit `specBatch`'s precondition: they `logShapeM true → logShapeOn
  E.lm`, A1 deletes the window rows: different lines, a textual merge), `E/EtcdServer__applyAll.lean` (A1
  edits the merge branch, 380-480; they edit the snapshot branch and `logShapeOn` sites), `E/AuthCompRows.lean`
  (hubs: A1 deletes `Hwpend`, they may add lease rows; both via 82), `E/InvApplyAll.lean` (A1 adds
  `srvProcOk` to `isServerApplyAll` if D-A0-2 (a)). `E/SnapSendBranch.lean` is not touched by A1 (review m4). A1 sequenced after their landing, rebased: est. 0.5-1 d of merge work.
- **Under R2s-A/A-r** (for the record): both restate `specSnapM` and the image predicates. Compose by stating
  R2s-A's receiver over "the image's log" `A_j` (whatever its length) so that their `hnl` at `A'` reads at
  `A_j` unchanged; conflict points: `SE/EtcdServer__applySnapshot.lean` (premises and post), `SE/EtcdServer__applyAll.lean`'s
  `specSnapM`, `SnapRecvOn.lean` (`snapRecv_imageOn` at `j`), `MergedImageOn.lean` (the window sender's image),
  `ImageOn.lean` (unchanged shape, used at `j`), `SnapApplyPost.lean` (`srvSnapApplied_of_walk`'s indices),
  `ApplyAllSnap.lean` (`applyAll.wp_proofSnapM`), `InvApplyAll.lean` (`srvNet`). Every one a real conflict.

## 5. Go/no-go (D-R3-2's rule: no-go if A1 > 9 wk or a blocker)

- **R2s-A as recorded: no-go** (blocker §2.2; A-u 11-18 wk).
- **Route (A) with A-g: go** (A1 2-3 wk), **if the user approves the fork change** (D-A0-1).
- A-r: go by the rule (A1 5-8 wk + the receiver's change). Larger than A-g and it changes two trusted texts,
  but it also covers the crash cause of the backward install (review M1); A-g suffices for restart3's
  graceful scope, and A-r (or a crash-time variant) belongs with a crash-model restart theorem.
- If the user rejects any fork change: B0 (8.5-12.5 wk; reverses D2 (b), adds the no-downgrade text), the
  recorded fallback.

## 6. Decisions needed

- **D-A0-1 (user).** Route (A) via A-g: the goose fork's merge defers a merged snapshot while
  `ep.appliedi < ConsistentIndex()` (the leader's replay window). *Recommended.* Alternatives: A-r (receiver
  change), A-u (no fork change, no-go by the rule), B0.
- **D-A0-2.** On a deferred snapshot: (a) `ReportSnapshot(to, SnapshotFailure)` (liveness kept: raft
  retries; needs `srvProcOk` in `isServerApplyAll`, a hub row) or (b) drop silently as the term guard does
  (follower stuck in `StateSnapshot` until a leadership change; no hub change). *Recommended: (a).*
- **D-A0-3.** The finding `nonissues/etcd-backward-snapshot-install-panics-watcher.md` (a backward install
  panics a catching-up watcher; mvcc test fails, not yet reached through etcd's paths; `blocks-proof: no`).
  Write the integration test that would move it to `issues/` (a forced in-window leader and a lagging
  second leader, or a crash between apply and the HardState save; est. 2-4 d), or leave it a nonissue.
  *Recommended: leave it for now, revisit with the crash-model work.*
- **D-A0-4.** Strike `srvWinSupply`/`srvWinAdd` from the restart notes (never built). *Recommended* (notes only).
- **D-A0-5.** Supersede the R2s decision's receiver design (`decisions.md`, "R2s": "the KV ghost reset at an
  install") by this note's §2.2 finding, whatever D-A0-1 decides. *Recommended.*

## 7. After the checkpoint (2026-11-15): decisions, the integration test (D-A0-3)

Decisions (`questions.md`): D-A0-1 approved by the user (route (A) via A-g); D-A0-2 `ReportSnapshot` (the
`srvProcOk` hub row in the A1 Freeze package); D-A0-3 the integration test now (the user); D-A0-4/5 yes.

**The test** (`nonissues/etcd-backward-snapshot-install-panics-watcher/inwindow_merge_test.go`, run in a copy of
etcd at `2eaeb872bc` built with `gofail enable`, `/shared/tmp/restart3-a0/etcd`; logs `it-run{1..5}.log`):
- **Reached, graceful**: a restarted leader merges a snapshot inside its replay window; the follower installs it
  at raft index 217 with its backend at consistent index 467, re-applies 218..467 v2-only and serves all 455
  keys (run 5, PASS). This is the harness for A-g's guard-firing run (step 2).
- **Not reached**: the backward install and the watcher panic (the nonissue's "Why not an issue" gives the
  reason: the second, older sender must pass the fork's term guard with a stale commit, which needs an electorate
  without the first leader's term entries; est. 2-4 d more with about seven members and a delayed leader send).
  The finding stays in `nonissues/`. The crash path reaches the receiver state more directly; not tried.
- **Timing lessons**: ticks share the raft loop with `Ready` processing, so `raftBeforeSave` sleeps slow elections
  as much as handouts (run 3: ElectionTicks 50 made the election come after the whole handout); a leader merges
  only at the end of a batch handed out at its term, so the follower must be connected once the leader applies
  past its commit at election (run 2 connected it earlier, and no merged snapshot was ever sent).

**Observation (to confirm in step 2): the fork's term guard can wedge a follower.** In run 2 the leader's
`MsgSnap` reached the apply loop at a batch handed out before its election; the term guard dropped it silently,
raft's progress for the follower stayed in `StateSnapshot`, and the follower got no snapshot for the rest of the
run (about 30 s, while the same leader led). Upstream has no such guard (the proposed upstream fix in
`issues/etcd-merged-snapshot-stale-term.md` drops only a message older than the applied term, after raft has
left it). Liveness only (`blocks-proof: no`). Proposed with the A-g commit: `ReportSnapshot(to, SnapshotFailure)`
on every drop at this select (the term and index guards too), so raft probes again (D-A0-6).

**No existing closed theorem has premises under which a backward install is reachable** (written confirmation
for etcd-grove-81). A backward install needs a receiver whose backend is ahead of its raft commit. On graceful
runs that state arises only from a merged snapshot made inside the sender's replay window, which needs a sender
that restarted. Every closed theorem other than `etcd_restart1_safe` starts each member once and never restarts
one (no replay window: `RestartPt.first`, the merge at `ciEff = ai'`), and none models a crash. `etcd_restart1_safe`
restarts its single member, but a single voter sends no `MsgSnap` at all (the P2-a law `snapTo`: a `MsgSnap`'s
destination is a committed voter other than the sender), so it has no merge and no install. In the proof, the
only install is `applyAll.specSnapM`, whose premise `uint.Z g < uint.Z sv.Index` (A8, derived from
`rnRestartOk_winAbove`) is a forward install.

## 8. Step 2: the A-g guard-firing run, and the fork commit (2026-11-15)

D-A0-6 (etcd-grove-81): `ReportSnapshot(SnapshotFailure)` on every drop at the merge select.

**The fork commit**: `6e8f0c004` on branch `restart3-ag` of a clone of `upamanyus/etcd`
(`/shared/tmp/restart3-a0/etcd-fork`), on `goose-lean` `2eaeb872b`, not pushed: inside the window
(`ep.appliedi < s.consistIndex.ConsistentIndex()`) the merge is replaced by `s.ReportSnapshot(m.GetTo(),
raft.SnapshotFailure)`; a message dropped by the term or index guard is reported failed too. etcd's
`server/etcdserver` unit tests pass on it (`go test ./etcdserver/`, 9.9 s).

**Runs** (the harness of §7, etcd at `2eaeb872bc` with the same change plus log lines, `gofail enable`d;
logs `/shared/tmp/restart3-a0/s2-*.log`):

| Setting | Runs | Result |
|---|---|---|
| `ZZ_EXPECT_DEFER=1` (connect the follower once the leader applies its term's batches, inside its window) | 3 | PASS 3/3: the guard fired 19-25 times per run (deferred inside the window), the follower installed a snapshot at its own index (487 = 487, 467 = 467, 487 = 487), then served all 455 keys linearizably |
| `ZZ_MEND_EARLY=1` (connect it before: the term guard drops the first `MsgSnap`s) | 3 | PASS 3/3: 1-7 term-guard drops and 11-24 deferrals per run, each reported; the follower recovered, installed at 467 = 467 and served all 455 keys |
| `ZZ_MEND_EARLY=1`, `ZZ_NO_REPORT=1` (the drops not reported, as before the commit) | 2 | FAIL 2/2: after one unreported drop the follower got no snapshot for 60 s (the leader's window ended after about 20 s): the stuck follower of §7, confirmed |

So: the guard fires and the run stays correct; every merged image installed is at its own index; reporting the
drops is what lets the follower recover.

Next: the user pushes `6e8f0c004` to `goose-lean` (fast-forward from `2eaeb872b`); then A1's g0 (pin bump in
`etc/goose.py` and `examples/go.mod`, translation, `etc/goose.py --check`).
