# restart3: handoff (2026-11-15)

Worktree `/shared/etcd-grove-auth3`, branch `restart3` (off `lean` `c3da59fa29`, `restart3-scope` merged).
Plan: `notes/restart3-scope.md` (route (A), decided by the user 2026-11-15). Decisions: `questions.md`.

## Done
- **A0 (stopped at the go/no-go checkpoint)**: `notes/restart3-a0-draft.md`. R2s-A as recorded is blocked
  (a backward install the KV store invariant cannot follow, §2.2); variant A-g (a fork guard deferring a
  merged snapshot in the sender's replay window) recommended (§3).
- Probes (unlinked; checked with `lake env lean`; copies in `notes/restart3-a0/`, working copies in
  `Scratch/`, untracked): `R3A0ProbeKV.lean` (P1), `R3A0ProbeGuard.lean` (P2, P3).
- Go probe of A-g: `notes/restart3-a0/ag-guard.patch` against the fork's `server/v3` (module cache copy at
  `/shared/tmp/restart3-a0/server`), restart3probe setting A, 6/6 (`/shared/tmp/restart3-a0/ag2-run-*.txt`).
- `nonissues/etcd-backward-snapshot-install-panics-watcher.md` (index regenerated).

## Next, in order (after etcd-grove-81's answer)
1. If A-g: g0 the fork commit (guard + `ReportSnapshot`), Go tests, pin bump, `etc/goose.py --project etcd`
   (GOWORK unset); g1 the merge branch (`wp_ci_get`, `probe_P2_guard`); g2 the deletions (Draft §2.3);
   g3 Freeze package (Draft §3.3). Sequenced after auth-lease's `specSnapM` restatement lands.
2. C1-C4 of the Scope (restart3's Go and proofs), the handler swap (D-R3-4).

## Pitfalls
- The probes import server modules: build `EtcdServer__run`/`EtcdServer__applyAll` first (targeted build,
  64G cap); `lake env --packages=/shared/tmp/manifest-ddc.json lean Scratch/<file>`.
- Go probe against a patched fork: `go test -modfile=/shared/tmp/restart3-a0/alt.mod` (a copy of
  `examples/go.mod` with `server/v3` replaced by the local copy), `GOWORK=off`, 32G cap; one run per process.
- `notes/status-history.md` is append-only (check `wc -l` against lean before a commit).

## 2026-11-15 after the checkpoint
- Decisions D-A0-1..5 recorded (`questions.md`). Step 1 (integration test) done: in-window merge reached on a
  graceful path, backward install not reached (Draft §7, the nonissue). Harness: `/shared/tmp/restart3-a0/etcd`
  (etcd at `2eaeb872bc`, `gofail enable`d, the test in `tests/integration/zz_backward_install_test.go`), run with
  `cd tests && GOWORK=off GOPROXY=off GOFLAGS=-mod=mod go test ./integration/ -run TestZZBackwardInstall -v`
  under the 32G cap; `ZZ_EXPECT_DEFER=1` for the A-g run (step 2).
- The fork clone for A1: `/shared/tmp/restart3-a0/etcd-fork` (branch `restart3-ag` off `goose-lean` `2eaeb872b`),
  the A-g change applied, not committed (after step 2).

## A1 in progress (2026-11-15; uncommitted work is described here until committed)
Decisions: D-A0-6 yes (ReportSnapshot on every drop); fork commit `6e8f0c004` (clone
`/shared/tmp/restart3-a0/etcd-fork`, branch `restart3-ag`), NOT pushed (the user is offline); etcd-grove-81:
proceed with A1 on `--src`, bump the pins on this branch, `goose --check` after the push.

Done on the branch (A1 g0-g1, partly):
- `etc/goose.py` etcd rev `6e8f0c004…`, `examples/go.mod`, `examples/k8s/{compactor,etcd3}/go.mod` replaces
  `v3.0.0-20261115042120-6e8f0c004c15` (go.sum not updated: needs the pushed commit).
- Translation regenerated with `etc/goose.py --project etcd --src etcd=/shared/tmp/restart3-a0/etcd-fork`
  (only `Code/go_etcd_io/etcd/server/v3/etcdserver.lean` changed: the merge select).
- `EtcdServer.ReportSnapshot.spec` precondition: the wrapper's node and `rnStepIfc` (was `srvProcOk`);
  proof and `NetBridge` adapted.
- `isServerApplyAll`'s bag row and `srvApplyAllBuilt` (InvStart) gain `rnNodeAddr ↦□ rnNodeIface γm ∗
  rnStepIfc γm …` (the "srvProcOk hub row", reduced; Freeze item); `NewServer`/`NewServerR` supply it
  (`HNodeC`, `HstepI`).
- `applyAll.specBatch`: `winNoMergedSendR`, `T`, `srvSnapBagN` deleted. Proof: new callees `hCI`, `hGTo`,
  `hRSn`; the merge receives through `isServerApplyAll`'s bag (`γm`); the window guard via `wp_ci_get` and
  `stLoaded_ciEff`/`stLoaded_pending` (new, `InvServer.lean`); drop branches call `ReportSnapshot`.
- `ApplyAllSnap.lean` (`wp_proofSnapM`, both modes): the guard read (refuted: `ciEff = Index`), drop branches
  report.
- `run_job_body`: no window rows; keeps a framed `T` (the run passes `token γwp` until `srvWinPend` goes).

Next, in order: get `EtcdServer__applyAll` building (build log `/shared/tmp/restart3-a0/build-a1-2.log`);
`Link.lean` (gen-link: applyAll's three new callees); then g2 deletions: `srvWinPend` (+ `token γwp`
threading in `EtcdServer__run`), hubs `AuthCompRows` (2), `InvStart`, `InvBuild`, `ServerOn`, `StartOn`,
`BuiltRestart`, `NewServer(R)`; row 4 (`rnRestartOk`, `NodeStartSpecR`, `newRaftNode`, `processMessages`),
`rnSnapMsg`'s `t0` bound; `srvRestartRows` (`InvRestart`, `NewServerR` spec, etcdstart `BuildServer/newServer/
newServerMode.specRestart`, restart1 `startMember`, `RestartRowsSingle.lean` deleted, restart3 drafts);
`winNoMergedSendR`/`srvSnapBagN` defs (`ApplyRDefs`); Results docstring; SpecPlan ledger + text; interfaces;
then the Freeze package (hard stop).

### A1 status at the context stop (2026-11-15)
- Committed: `a7664b099b` (pins, translation, specs/hubs), `3e2cf89fec` (applyAll's merge and ApplyAllSnap over
  the guard: both pass `etc/lean-check.py -a`), `8f3676d5d6` (server `Link.lean`: applyAll's three new callees,
  `etc/link-lean-first-server.txt`).
- `run_job_body` no longer passes window rows (keeps a framed `T`; the run still passes `token γwp`): not yet
  checked (`EtcdServer__run.lean` and everything importing `InvApplyAll`/`InvStart`/`InvServer` need a build).
- New internal lemmas: `stLoaded_ciEff`, `stLoaded_pending`, `stLoaded_p` (`InvServer.lean`).
- Pattern for the guard read: `wp_apply_core (wp_ci_get hCI γ ci b st hp) $$ [Hst Hbe] [-]`, then
  `iintro ⟨Hst, Hbe⟩`; `generalize stLoaded γ st = st4 at … ⊢`; the value returned is `ciEff γ st.k` (old st).
- Next (g2): delete `srvWinPend` and its hub rows (positional `icases`/`iframe` at: `AuthCompRows.lean`
  229/391/671/678/687/694, `InvBuild.lean` 335, `InvStart.lean` 290, `ServerOn.lean` 186, `StartOn.lean` 95/208/214,
  `ModeSpecs.lean` 584/593, `BuildGap.lean` 272/278, `EtcdServer__start.lean` 635/640, `NewServer.lean`
  2062/2248, `NewServerR.lean` 1144/2024, `EtcdServer__run.lean` 905/906 and the `token γwp` threading
  1210-1452 → `T := iprop(True)`); then row 4, `rnSnapMsg`'s bound, `srvRestartRows` (list above); then a full
  build (flock, 64G), interfaces (server, etcdstart, raft untouched), SpecPlan ledger entry, tcb `--check`
  (unchanged expected), the Freeze package (hard stop).

### A1 g2 (2026-11-15, second agent)
Committed `374df0d887` (edits), then the etcdstart interfaces; full build passes (`/shared/tmp/restart3-a1/build-g2-2.log`);
`etc/tcb-report.py --check` unchanged (870 axioms, 4 sorries), restart1 collection unchanged (508, 0); interfaces:
only etcdstart's changed (absdisk, backend, bbolt, mvcc, raft clean). Freeze package: Draft §9 (HARD STOP; waiting for
etcd-grove-81). Next after review: goose --check and go.sum once the fork is pushed; then the C-stages.
Edits:
- `srvWinPend` (`InvRun.lean`) and `srvWinPend_first` deleted; the `Hwpend` row out of `isServerRunC`,
  `isServerBuiltC` (`AuthCompRows`), `srvApplyAllBuilt`/`InvStart`, `InvBuild`, `srvBuiltG` (`ServerOn`),
  `isServerBuiltOn` (`StartOn`); the positional patterns in `AuthCompRows`, `BuildGap`, `StartOn`, `ModeSpecs`,
  `EtcdServer__start`, `NewServer`, `NewServerR`.
- `EtcdServer__run`: no `token γwp` (the saved props are `applyResR ∗ nodeRunning`); `run_job_body` lost its
  `T` binder (internal); `Hbagn` replaced by `HmidN0 : srvMemberIDAddr s ↦□ γn.id` (for the stop's cleanup).
- `winNoMergedSendR`, `winNoMergedSendR_nil`, `srvSnapBagN` deleted (`ApplyRDefs`).
- Row 4: `rnSnapTermAbove`, `rnSnapTermOk(_cons)`, `rnRestartOk_snapTerm` deleted (`InvRaftNode`);
  `rnRestartOk`'s restart disjunct loses it; `rnRawMsgs` loses `⌜rnSnapTermOk γ ms⌝`; `rnMsgOk_of_api` loses the
  premise; `rnSnapMsg`'s pure is `⌜Type' = MsgSnap⌝` (the `t0 < Term'` bound gone); `NodeStartSpecR`'s installer
  loses `rnSnapTermAbove γw`. `RNNames.t0` kept (read only by `rnRestartOk`'s first disjunct `t0 = 0`).
- `srvRestartRows` (`InvRestart`) deleted, `RestartRowsSingle.lean` deleted (git rm); `NewServer.specR`'s
  `Hrows`; etcdstart `newServer/newServerMode/BuildServer.specRestart`'s `□ ∀ A σ, srvRestartRows`; restart
  (3-member draft) `startMember/restartCheck` specs and `Run.wp_proof`'s `hRows`; restart1's proof.
- Not touched: `Proof/go_etcd_io/raft/v3/InvNodeRule.lean:455`'s docstring still names `srvRestartRows_single`
  (raft untouched, so as not to rebuild raft's importers).
- SpecPlan: ledger entry 2026-11-15 (`applyAll.spec` sketch), `SpecPlan/.../EtcdServer__applyAll.lean` sketch text.
Build log: `/shared/tmp/restart3-a1/build-g2-*.log`.

### lean merged into `restart3` (2026-11-15, lean `b7e3cf342a`, auth-lease S3a)
Conflicts: `EtcdServer__applyAll.lean` (A1's `T`-less step end and `st4` kept, at S3a's `srvRestRM C.isOn` /
`srvRestRM_past`; S3a's `srvRestM` mode switches around `mergedCreate_window` auto-merged), STATUS "Last updated"
(union of both sides' ten, newest ten kept; http-boundary moved to status-history, S7.4 already there),
status-history (A1's S7.4 line kept). Full build green (flock, 64G; `/shared/tmp/restart3-merge/build-1.log`);
`etc/gates.sh`: build, links, tcb (870/4), collections (57 match), gen-init, bounds 351, mode 417, api, interfaces,
import-all ok; goose and the Go gates (pbschema, entsize, featuregate, premisefix, k8s) fail on go.sum only (the
unpushed fork `6e8f0c004`), as expected (`/shared/tmp/restart3-merge/gates-1.log`).
