# Review r1: notes/restart3-a0-draft.md (restart3 A0: R2s-A blocker, variant A-g)

Reviewer: independent, read-only. Worktree /shared/etcd-grove-auth3 (branch restart3, HEAD 36364c25ea).
Go: etcd fork 2eaeb872bc (server.go, snapshot_merge.go, raft.go, mvcc), raft 565c2bd.
No builds were run. Every Lean claim below comes from reading the code; where I could not check something I say so.

## Summary of checks

1. **The blocker holds, and it is reachable in Go.** `applySnapshot` checks only `Index > ep.appliedi`
   (server.go:1046) and then opens the snapshot's db unconditionally (server.go:1068, `SetBackend` at :1080).
   Raft accepts a snapshot if its index is above `raftLog.committed` (raft.go:1877). The merged image is
   `s.be.Snapshot()` stamped with `ep.appliedi` (snapshot_merge.go:34-50). So in the window-merge scenario
   the backend does move backward. The KV store invariant cannot follow a backward restore:
   - `monoListAuthOwn γs.slog 1 σ.log` (KVStoreApi.lean:116);
   - the restore builder requires `log <+: log'` (:176-180);
   - anyone's read from a floor gives `L₀ <+: σ.log` (:182, `kvReadAt` :132-135).
   The applied index only moves forward (`applied_jump`, InvRequest.lean:2477-2481; `appliedMonoMap`, :2343-2350).
2. **A-g is sound in the proof's model, and probe P2 is the right lemma.** Its hypotheses are available at the
   merge, and the value `wp_ci_get` returns is the same `ciEff` (details under "What is good").
3. **The deletion tables are incomplete.** See m1 and m2.
4. **The liveness claim about ReportSnapshot is right, and the spec is usable from the apply thread.** See m8.
5. **The nonissue's watcher claim is wrong.** See M2.
6. **Overstatements:** "no backend is ever ahead of its raft commit" and "no backward install exists" hold
   only for graceful restarts (M1). "A-r is dominated by A-g" ignores this.

## What is good

- **Section 1's corrections hold.**
  - `srvWinSupply`/`srvWinAdd` appear in no `.lean` file.
  - Row 1 (`srvWinPend`) and row 4 (`rnSnapTermAbove`) are exactly `srvRestartRows`
    (InvRestart.lean:714-719).
  - Row 4 is consumed only through `rnSnapTermOk`:
    `rnRestartOk_snapTerm` (InvRaftNode.lean:500-530) → `rnRawMsgs` (:381) → `rnMsgOk_of_api` (:997-1000)
    → `rnSnapMsg`'s `t0 < Term` (:203-208) → the `rt ≤ t0` arm of the merge (EtcdServer__applyAll.lean:410-416).
  - `readyRest_snap` exists (raft InvNode.lean:969).
- **The blocker's Go trace is right.**
  - server.go:1013-1015 merges at `ep.appliedi` with the whole backend.
  - server.go:1046 is the receiver's only index check.
  - The `matchTerm` fast-forward (raft.go:1925-1931) does not intercept the scenario: after the first install
    the receiver's log holds no entries above the first snapshot until appends arrive.
- **Probe P2's hypotheses are all available at the merge point:**
  - `hk`: `kvBatchR … (ciEff γ st.k)` gives `ai0 + |A₀| ≤ ciEff st.k` (ApplyRDefs.lean:89;
    SE/EtcdServer__applyAll.lean:98).
  - `hmono`, first step: `applyEntries`' post gives `ciEff st' = ciEff st ∨ ciEff st' = max(ciEff st, ai')`
    (SE/EtcdServer__applyEntries.lean:110-111).
  - `hmono`, second step: `snapshotIfNeededAndCompactRaftLog` keeps it, `ciEff st''.k = ciEff st'.k`
    (its spec's post, `⌜loopOk γ st' ai ∧ ciEff γ st'.k = ciEff γ st.k⌝`; used at EtcdServer__applyAll.lean:479).
  - `wp_ci_get` returns exactly `#(ciEff γ st''.k)` (InvServer.lean:205). Its premise `st''.pending = false`
    comes from `loopOk` (InvApplier.lean:107-108).
  - Loading changes only `k`, not `ciEff` (`stLoaded_facts_snap`, EtcdServer__snapshot.lean:63-64), so
    `Hfin`'s `ciEff γ stF.k = ciEff γ st'.k` still holds.
  - When the guard is false the window is over (P2). Past the window the existing proof already derives
    `ciEff st'' = ai'` (`hciE`, EtcdServer__applyAll.lean:477-487). So the guard is exactly the window
    condition, and the true branch is never taken outside a window.
- **The R2s decision's reasoning is superseded on the right ground.** The 2026-11-06 R2s entry
  (decisions.md:33166ff) predates the strict-M1 store invariant and planned "the KV ghost reset at an install".
- **Section 4 sequences A1 after auth-lease.** That is sensible.

## Findings

### BLOCKER

None. A-g, as a design for the graceful-restart scope, survives this review.

### MAJOR

**M1. A-g does not remove the backward install. It removes only its window-merge cause. A crash restart reaches the same install, with no window sender involved.**

- **Principle:** state the scope a claim holds in; a claim the project's own plan contradicts is overstated.
- **Evidence.** The raft loop hands a batch to apply (raft.go:240) before it saves the batch's HardState
  (:264), so after a machine crash bbolt's consistent index can be above the WAL's commit:
  - `notes/restart-vs-crash.md:174-182` ("already reachable under machine crashes");
  - rnRestartOk's own docstring: "`|a0| ≤ commit0` is **graceful-only** (after a power loss the backend's
    consistent index can be above the WAL's synced commit: crash-design §2.3)" (InvRaftNode.lean:483-490);
  - `wal.stopImage`'s docstring: "the order holds at a graceful stop, not at every instant"
    (WalApi.lean:360-366).

  Such a member, with restored commit `c0 < ci`, accepts a snapshot at an index in `(c0, ci)` (raft.go:1877;
  server.go:1046) and restores the older image. That is the same KV-floor problem as §2.2, with no merge
  inside any window.
- **Affects:**
  - §0 and §3.2's "no backend is ever ahead of its raft commit" and "no backward install exists";
  - §5's "A-r … dominated by A-g". A-r (the receiver keeps a backend that already extends the snapshot)
    handles both the window-merge cause and the crash cause. A-g handles only the former;
  - the nonissue's "Cause" and its `blocks-proof: no`. These are fine for the graceful scope but not for
    the crash restarts the project plans ("plan for crashes now", 2026-11-11).
- **Fix:**
  - Qualify §0, §3.2 and the nonissue: "at a graceful stop, `wal.stopImage`'s `i ≤ σ.commit`".
  - Add a paragraph to §5 and D-A0-1: a crash-restart theorem will meet the backward install whatever A1
    chooses, so it will need A-r's receiver change or A-u's re-founding then. Compare A-g + (later A-r)
    with A-r now: A-r now changes two trusted texts, per §2.5, but solves both causes.
  - This does not change "go" for A1-g in the graceful scope, but the user should decide D-A0-1 knowing it.

**M2. The nonissue's watcher claim ("A watcher is not affected") is wrong, and there is a candidate reachable panic.**

- **Principle:** a nonissue's impact must be checked against the code; a panic reachable this way belongs
  in `issues/` with a test.
- **Evidence.** `watchableStore.Restore` sets `restore = true` only on **synced** watchers
  (watchable_store.go:215-218).
  - **Unsynced watchers can panic.** An unsynced watcher can carry `minRev` above the restored
    `currentRev` without the flag:
    - a watch created with a past start revision 90 at current revision 100, not yet synced (resync every
      100 ms; at most `maxWatchersPerSync` per round);
    - or one left unsynced with `minRev = eb.moreRev` (watchable_store.go:398-410);
    - or a victim moved to unsynced (`minRev <= curRev`, :333-334) before the restore.

    After a restore down to revision 80, `chooseAll` meets `w.minRev > curRev` with `!w.restore` and
    panics, `"watcher minimum revision %d should not exceed current revision %d"`
    (watcher_group.go:244-250). That panic is in `syncWatchersLoop`'s goroutine, so the process dies.
  - **The flag does not cover a backward restore.** The flag's comment (watcher_group.go:245-247) is about
    a *future-revision* watcher (`math.MaxInt64 - 2`), not a backward restore. So "etcd's own watch code
    anticipates a restore below a watcher's revision" (the nonissue's "Why not an issue") reads more into
    it than it says.
  - **Progress notifications go backward.** A synced watcher that has received events up to revision 100
    can get a progress notification at the restored, lower revision: `progressIfSync` checks `rev <
    w.startRev`, not `minRev` (watchable_store.go:533-551). So a watch stream sees its revision go back.
    That matters to the cache package and to k8s, which advance on progress revisions
    (cf. `issues/cache-stale-progress-compacts-newest-watch.md`).
  - Not found in `issues/` or `nonissues/` (searched for `chooseAll`, `should not exceed current revision`
    and `restore`).
- **Uncertain:** I found this by code reading and did not run it. The race window for the unsynced case is
  narrow, at most about one resync period.
- **Fix:**
  - Write a Go test: an mvcc unit test of `watchableStore.Restore` to an older backend with an unsynced
    watcher at `minRev` between the two revisions. It needs no cluster, and the panic should be immediate.
  - If it fails, file `issues/etcd-mvcc-watch-panic-after-backward-restore` with the crash-restart
    reproduction path (M1), which upstream also reaches.
  - Either way, rewrite the nonissue's Impact paragraph and §2.2's "watchers are protected by the restore
    flag".
  - The linearizable-read claim does hold. A ReadIndex needs the leader to have committed in its term, so
    its read index is at least 100, and the member waits for `appliedi ≥` that (raft ReadOnlySafe;
    server's `applyWait`).

### MINOR

**m1. Two more hubs carry `Hwpend`, and section 1 and the tables do not list them.**
- `srvBuiltG` (ServerOn.lean:186) and `isServerBuiltOn` (StartOn.lean:95). The auth examples use them
  (`examples/etcd/auth/startServer.lean`, `auth3/startMember.lean`).
- LeaseRun.lean:14 names `srvWinPend` in its header.
- **Fix:** add them to §1, §3.3 (hub rows: requests to 82) and g2's work.

**m2. §3.3 misses several statement and interface changes.**
- **New callees.** `applyAll.wp_proofBatch`'s callee list (EtcdServer__applyAll.lean:55-81) gains
  `consistentIndex.ConsistentIndex.spec`, `raftpb.Message.GetTo.spec` and `EtcdServer.ReportSnapshot.spec`.
  The current list has none of them. So `Link.lean` (gen-link) and the proof file's interface change.
- **Exported result.** `applyAll_model` (Results.lean:200-217) restates `applyAll.spec` and its docstring
  names `winNoMergedSendR`/`srvSnapBagN`/`T`.
- **SpecPlan and the ledger.**
  - SpecPlan's `EtcdServer__applyAll.lean:25-30` says the merged snapshot's guard "is the code's
    (`m.term = raftTerm`, `index ≤ appliedi`)". With the fork change, the code's guard gains the window
    test.
  - SpecPlan also says "a merged snapshot at any applied index is valid". The Draft's §2.2 shows that hides
    the backward install.
  - CLAUDE.md requires a `notes/specs-only/ledger.md` entry before the spec edit.
- **Goose pins.** The fork bump also moves `examples/go.mod`'s replace of etcd (`etc/goose.py --check`).
- **Fix:** add these rows and the g0 item.

**m3. Deleting `srvSnapBagN` from `specBatch` removes the bag the merge branch currently receives through.**
- The merge branch receives through `srvSnapBagN` (`iunfold srvSnapBagN at Hbagn`,
  EtcdServer__applyAll.lean:383-386). After the deletion it must use `isServerApplyAll`'s bag at the
  existential `γm`, with `γm.node = γr.raft.raft` (InvApplyAll.lean:131). That bag is already destructured
  as `-` at EtcdServer__applyAll.lean:107.
- `srv_sentSnap_pos` then takes `γm.id`.
- This looks feasible (uncertain: not checked), but §3.2 should say it.

**m4. §4 overstates one conflict point.** It lists `E/SnapSendBranch.lean` as "A1 only drops the t0-bound
uses". The file has no uses of `t0`; `rnSnapMsg` appears only in its docstring (lines 6, 13). A1 need not
touch it.

**m5. §3.1 mislabels the term guard.** It says the fork "already carries two proof guards at this select".
Only the index guard is for the proof (server.go:1006-1012). The term guard is the fix recorded as
`issues/etcd-merged-snapshot-stale-term.md`. This matters to how the user weighs a third fork change.
Reword.

**m6. The blocker argument can be stronger, and it answers "is there a cheaper way".**
- **The ghost cannot stay ahead.** Keeping the KV ghost at the backend's old log while mvcc's physical
  state goes back is impossible, because `mvccState γ σ` is the physical store, tied to `γs.slog` exactly
  (KVStoreApi.lean:115-116). Worse, the floor read law (`□ ∀ L₀, kvLogLb γs L₀ -∗ auRead γ (kvReadAt …
  L₀)`, :182) is *false of Go* under a backward install: the nonissue itself says two serializable reads
  see the revision go back. A-u is therefore not "re-founding the proof" but weakening the store's read
  guarantee. Say so.
- **A-c.** A sender-side alternative is worth a line: stamp the merged snapshot at the consistent index
  instead of `ep.appliedi`. That avoids deferral and liveness questions, but needs the term and the
  `ConfState` at `ci`, and replayed conf changes are v2-only. Recording why it was rejected would close
  the question.

**m7. The Go evidence is a smoke test.**
- The 6/6 runs (`ag2-run-*.txt`) show only that the patched server, used via `alt.mod`'s replace to
  `/shared/tmp/restart3-a0/server`, does not break the normal path. The guard never fired and no line
  says `A0PROBE`.
- The Draft says this. But §0's "Go probe 6/6" reads as evidence for the guard; qualify it there too.

**m8. Liveness: right, with two caveats.**
- **Why it works.**
  - `MsgSnapStatus` with `Reject` sets `PendingSnapshot = 0` and calls `BecomeProbe` (`Next = Match+1`),
    then `MsgAppFlowPaused = true` (raft.go:1626-1645; progress.go:130-142).
  - The next `MsgHeartbeatResp` clears the pause and calls `sendAppend` (raft.go:1594-1613), which goes
    back to `maybeSendSnapshot` (:666-689).
  - The raftNode hands a `toApply` to the apply loop on every Ready, so the select at server.go:1001-1018
  runs often.
  - Without the report, a `StateSnapshot` progress is always paused (progress.go:262-270) until an
    `MsgAppResp`, an `MsgSnapStatus` or a term change, as the Draft says.
- **Caveat 1:** `processMessages` drops a `MsgSnap` silently when `msgSnapC` (capacity 16) is full
  (etcd raft.go:395-398). Upstream already has this stuck case.
- **Caveat 2:** calling `ReportSnapshot` synchronously from the apply thread is new. `node.ReportSnapshot`
  blocks on the unbuffered `recvc` (node.go:315, 592-598), but `node.run` always serves `recvc`
  (node.go:394), so there is no deadlock.
- **The spec is usable from the apply thread.** `EtcdServer.ReportSnapshot.spec` needs only the
  persistent `srvProcOk γn s id γd` (Spec/.../EtcdServer__ReportSnapshot.lean:29-34), and its proof calls
  only raft's `ReportSnapshot` through `rnStepIfc` (Proof/.../EtcdServer__ReportSnapshot.lean). NewServer
  builds `srvProcOk` (NewServer.lean:1222; NewServerR.lean:1155), but no apply hub carries it. D-A0-2 (a)'s
  hub row is real work. Add a sentence on why the post `True` is enough: liveness is not proved.

**m9. Estimates.** A1-g's 2-3 wk looks plausible. m1-m3 add about 1-2 d to g1/g2 (two more hubs, three new
callees, the bag switch). The route's 5.5-8 wk depends on C2, which I could not check. The R2s-A/A-u
figures (+6-10 wk, "no design") are unverifiable as stated; given m6, A-u is a guarantee change and likely
no-go on meaning, not only on cost.

## Ranking (need of revision)

1. **The nonissue** (M2, plus M1's cause and scope). Its impact claims are wrong as written, and a reachable
   panic needs a test before it can stay a nonissue.
2. **Draft §0, §3.2, §5 and D-A0-1** (M1). The graceful-only qualification is missing, and so is the A-r
   comparison under crashes.
3. **Draft §1, §3.3 and §3.4** (m1-m3, m9). Incomplete deletion and statement lists.
4. **Draft §3.1, §4 and §2.2's justification** (m4-m8). Wording, and a stronger blocker argument.

## Verdict

**Go for A1 with A-g in the graceful-restart scope, after revision.** The blocker is real, and stronger than
stated: the floor read law is false of Go under a backward install. A-g's guard is exactly the window
condition in the proof's model. Probe P2's hypotheses are all available at the merge point, and its value
is the same `ciEff`. Every restart-only row (`srvWinPend`, `winNoMergedSendR`, row 4, `rnSnapMsg`'s `t0`
bound, `srvRestartRows`) does become deletable.

Before the user decides D-A0-1, the Draft must say:
- A-g removes the backward install only for graceful stops. Crash restarts (bbolt ahead of the WAL) reach
  it anyway, which weighs toward A-r.
- The nonissue's watcher claims must be rewritten and the possible `chooseAll` panic tested.
