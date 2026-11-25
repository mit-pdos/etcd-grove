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

## C-stages (2026-11-15; branch `restart3-c` off `1e218a9004`, so A1 (`restart3`) lands alone)

The A1 Freeze package is approved by etcd-grove-81 (all 19 rows); A1 lands once the user pushes `6e8f0c004`
(then goose --check, go.sum, merge lean, hard stop before land.sh). The worktree is on `restart3-c`; check out
`restart3` to land A1.

### C1 done (`98b2f8f7af`)
- `examples/etcd/restart/restart3.go` rewritten in place (project `restart3` of `etc/goose.py`, package `restart`):
  `build` x3 (BuildServer at SnapCount = SnapCatchUp = 1), `newMember` (listen, serve a `raftSwap` holding the
  built incarnation's `RaftHandler()`, `Start`), N1 = 5 in-process `Put`s through member 1, the follower stopped
  (member 3, or member 2 if 3 leads; `stop`: wait `AppliedIndex() >= NBoot`, `HardStop`), N2 = 20 `Put`s,
  `restartMember` (build on the data directory, `sw.set(RaftHandler())`, `Start`), `check` (wait `Leader() != 0`,
  linearizable `Range` of ["k","l"), exactly N1+N2 pairs at version 1, revision 1+N1+N2). No gRPC served; the
  address is never closed or re-listened (D-R3-4). Each incarnation is built before its handler is served or
  swapped, so `raftSwap.h` is never unset (no `http.NotFoundHandler` needed).
- `restart3_test.go`: `TestMemberIDs`, `TestRun` (restart1's counting core, plus merged snapshots sent/installed and
  compactions). 20/20 under the 32G cap, each in its own process, a merged snapshot sent and installed after the
  restart in every run (`/shared/tmp/restart3-c/v2/run-*.txt`).
- Go runs need the unpushed fork: `go test -modfile=/shared/tmp/restart3-c/alt.mod` (examples/go.mod at
  `2eaeb872b` with `server/v3` replaced by `/shared/tmp/restart3-a0/etcd-fork/server`, at `6e8f0c004`), `GOWORK=off
  GOFLAGS=-mod=mod`.
- Translation: `etc/goose.py --project restart3 --src etcd=/shared/tmp/restart3-a0/etcd-fork`, with examples/go.mod
  and go.sum TEMPORARILY replaced by `alt.mod`/`alt.sum` (goose's package loader cannot resolve `6e8f0c004` without
  sums; GOFLAGS=-modfile breaks goose's own build in workspace mode), then restored from
  `/shared/tmp/restart3-c/go.{mod,sum}.keep`. Redo with the real go.mod once the fork is pushed.
- **The Lean drafts under `{Spec,Proof}/github_com/mit_pdos/etcd_grove/examples/etcd/restart/` still state the old
  gRPC workload and no longer match the translation: they do not build. C2 replaces them.**

### C2 plan (next): the example proofs, restart1's generalized
- Specs (`Spec/.../examples/etcd/restart/`): `build.spec` (= `etcdstart.BuildServer.spec`/`specRestart` at the
  token `restart3`), `newMember.spec` (Listen + Serve of a `raftSwap` + `Start`, from the old `startMember.wp_proof`
  lines 79-130), `restartMember.spec`, `put.spec`, `stop.spec`, `check.spec`, `Run.spec`, `Main.spec`; delete
  `serveClient`, `restartCheck`.
- Proofs: restart1's `KV.lean` (`r1Inv`, the counter, `r1ReadAu`), `Requests.lean` (`putRequestIs_alloc`,
  `rangeRequestIs_alloc`, `bgCtx_facts`), `put.lean`, `check.lean`, `stop.lean` carry over with the cluster's
  `kvInv` (shared through `restartNames`) and N = N1 + N2 = 25 keys; `Run.lean` from putget3's three-member start
  (`etcdstart.alloc3`-style ghost setup) plus restart1's stop/restart steps (`memberUp_splitStop`,
  `memberBoot_restartFacts`, `memberFreshRes_verify`); the old draft `restart/Run.lean` has the three-member
  restart's resource plumbing (`Hrfs₂/₃`, `Hvoff`).
- Read path: the `Range` at the restarted member goes through the read index (`MsgReadIndex` to the leader), the
  multi-voter path already proved (Scope §4).

### C3 plan: the swap handler, no trusted text
`raftSwap.ServeHTTP.spec` must give `http.handlerOk (raftHttpNet (netRh γn)) a Rs_sw sw` for ONE `Rs_sw` across
incarnations, while each incarnation's `RaftHandler()` is `handlerOk … (srvServeRes γn τ) h` at its own names.
Sketch: the mutex's invariant holds the current incarnation `k`, `sw.h ↦ h_k`, `handlerOk … (srvServeRes γn_k τ_k)
h_k` (persistent), and a pool of the current incarnation's `srvServeRes` copies; `Rs_sw` is a slot token
(`httpProcSlots` of them, allocated by `newMember`). `ServeHTTP`: lock, read `h`, trade the slot token for one copy
of the current pool, unlock, call `h`, then return the copy to its incarnation's pool (an old incarnation's pool
after a swap is garbage) and get the token back. Invariant: size(pool_cur) = httpProcSlots − inflight_cur ≥ free
tokens. `set` (at the restart) installs the new incarnation with the `httpProcSlots` fresh copies that
`BuildServer.specRestart`'s serve bundle gives (`HServeR`). Old invocations in flight keep the stopped
incarnation's copy (Scope §2.2 (i)-(ii)): check that `HardStop`'s post leaves `srvServeRes` copies usable by an
in-flight handler run (`EtcdServer__HardStop.lean:24-27`), and that the transport tolerates the wasted delivery.
Est. 0.5-1 wk.

### Then C4 (hard stop before linking): the statement of `etcd_restart3_safe` and its premises in plain words.

### C2/C3 in progress (2026-11-15, third agent; branch `restart3-c`)
Committed `25dc487833` (wip; the branch does not build yet, as decided). Done:
- `Proof/.../restart/Swap.lean` (checked with `etc/lean-check.py -a`, 0 errors): the swap's ghost state, no
  trusted text. `SwNames` = slot map `g`, current incarnation `cur`, slot count `n` (a FIELD: see pitfall);
  per-incarnation invariant `swIncInv γn n c b τ` (slot j: copy ∗ `swTokB b j`, or `swTokA c j`); global
  `swGInv` (cur half, slot authority, per slot `swObl c j (m !! j)`: `A_j` unless busy with `c`); moves
  `sw_alloc` (newMember), `sw_enter` (needs £1), `sw_exit` (no £: works under ▷ with timeless tokens),
  `sw_install` (set). No freshness of incarnation names needed.
- `Defs.lean`: listener-close parts gone; `swLock`, `swapOk` (with ⌜γS.n = httpProcSlots⌝), `memberRec`.
- `KV.lean`: `r3Inv`/`r3PutAu`/`r3ReadAu`/`r3Ok_get` at 25 puts over restart1's pure lemmas.
- Specs: `build` (`spec`/`specRestart`), `newMember` (`newMember.spec`, `restartMember.spec`), `raftSwap`
  (`ServeHTTP.spec` in `http.handlerOk`'s invocation form, `set.spec`); `put`/`check`/`stop` copied from
  restart1 (stop generalized over `name`, NBoot 3; check's constants 11 → 25), not yet checked.
- Proofs: `build.lean` written (not checked); `raftSwap.lean` being written.
- Old drafts `serveClient`, `restartCheck`, `startMember` (spec+proof) deleted; `Init.lean` regenerated.
Next: raftSwap proofs; newMember/restartMember proofs (template: etcdstart `NewMember.lean`, old draft
`startMember.lean` in git history `1e218a9004`); put/stop/check checks; Run (three members: putget3 `Main.lean`
for alloc3/StartMember plumbing, `dir3_ok`/`dir3_host`/`dir3_dirsOk` to copy for restart's addresses; the old
draft Run.lean has `leadInv_memberID_of_req`; the stopped member chosen at run time: `wp_bind` the `If` and
prove it with a post naming the chosen member, to keep one copy of the tail); Main; then C4 hard stop.
Pitfall (2026-11-15): a lemma instantiated at a NUMERAL slot count whose statement has
`[∗list] j ∈ List.range n` made the IPM materialize the list (15 GB RSS in `imod`, killed). Keep `List.range`
over a variable (`γS.n`); only `List.replicate httpProcSlots` reaches concrete proofs (as in etcdstart).
Run lean-check under `systemd-run --scope -q -p MemoryMax=…` to be safe.

### C2/C3 done (2026-11-15, third agent): at the C4 hard stop
Commits `25dc487833`..`4939e4892a` (+ this note). Targeted `lake build` of every module of the example
(`Main Run newMember raftSwap build put stop check Init`, 64G cap) passes (`/shared/tmp/restart3-c/build-c2.log`);
no `sorry`, no axiom, no trusted text added. Proved: `raftSwap.ServeHTTP`/`set` (C3, over `Swap.lean`),
`newMember` (Listen, register, the swap's ghost state from the `httpProcSlots` serving copies, `init_Mutex`,
`go http.Serve(pl, sw)` with `swap_handlerOk`, Start), `restartMember` (`build.specRestart`, `set`, Start),
`build` (both), `put`/`stop`/`check` (restart1's, 25 puts, NBoot 3), `Run` (alloc3, 3 builds, 3 newMembers,
N1 puts, the `if` via `wp_bind (If _ _ _)` + `wp_wand` with post `stopCand`, stop, N2 puts, restartMember,
check), `Main`.
Checks (i)/(ii) of Scope §2.2: discharged by the proof itself: a stopped incarnation's in-flight handler run
keeps its own copy of `srvServeRes` (`sw_exit` drops it after the run; `HardStop.spec` takes nothing of it),
and the handler's WP is `RaftHandler`'s proved contract, so a message delivered to the dead incarnation needs
no world assumption.
Next (C4, after etcd-grove-81's answer on the statement): `PkgTable.lean`/`Init` wiring as restart1's
(`etc/gen-init.py` PkgTable entry for `restart`), `MainLinked.lean`, `Adequacy.lean` (`restart3Program`,
`restart3GF`, `restart3Names`, `restart3Addrs` = the three peer addresses), `Results.lean` with
`etcd_restart3_safe`, a tcb collection `etc/tcb-collections/restart3.txt`, `etc/link-*` lists if needed,
then a full build (flock, 64G), tcb `--check`, interfaces.

### C4 done (2026-11-15): at the hard stop before landing
Review fixes (etcd-grove-81): Results docstring (fork `6e8f0c004`, D-A0-1; conditional claim; "if Main returns
it returns unit"; "member 3, or member 2 if member 3 sees itself as leader"); stale spec headers (stop/check/put);
`srvLevels` and `N + 7 + bootWB ≤ wbInit` are discharged in `Adequacy.lean` (`srvLevels_of_max HT`; `unfold bootWB
backend.wbInit; omega` from `Hn`), as restart1's: no new premise. Added: `PkgTable.lean` (gen-init `PROGRAMS`),
`MainLinked.lean`, `Adequacy.lean`, `Results.lean` (`etcd_restart3_safe`), `etc/tcb-collections/restart3.txt`
(530 axioms, 0 sorries; a subset of putget3's 640; restart1's 508 plus the 22 HTTP/net boundary axioms putget3
already has). Full build (flock, 64G) passes (`/shared/tmp/restart3-c/build-c4.log`); `tcb-report.py --check`:
unchanged (870 axioms, 4 sorries); restart1 and putget3 collections unchanged; interfaces clean.
Left before landing: the user's approval of the statement; the fork push, then goose with the real go.mod
(`goose --check`, go.sum), A1 lands first; STATUS.md entry at landing.

### lean merged into `restart3` (2026-11-15, lean `b7e3cf342a`, auth-lease S3a)
Conflicts: `EtcdServer__applyAll.lean` (A1's `T`-less step end and `st4` kept, at S3a's `srvRestRM C.isOn` /
`srvRestRM_past`; S3a's `srvRestM` mode switches around `mergedCreate_window` auto-merged), STATUS "Last updated"
(union of both sides' ten, newest ten kept; http-boundary moved to status-history, S7.4 already there),
status-history (A1's S7.4 line kept). Full build green (flock, 64G; `/shared/tmp/restart3-merge/build-1.log`);
`etc/gates.sh`: build, links, tcb (870/4), collections (57 match), gen-init, bounds 351, mode 417, api, interfaces,
import-all ok; goose and the Go gates (pbschema, entsize, featuregate, premisefix, k8s) fail on go.sum only (the
unpushed fork `6e8f0c004`), as expected (`/shared/tmp/restart3-merge/gates-1.log`).

### `restart3` (with lean `b7e3cf342a`) merged into `restart3-c` (2026-11-15)
Only conflict: this handoff (both sides' sections kept). One fix: `restart/put.lean` destructs `wp_Put`'s post at
S3a's `∃ lt, ⌜…⌝ ∗ Q` (as lean's `restart1/put.lean`). Full build green (`/shared/tmp/restart3-merge/build-c2.log`);
`etc/gates.sh` (`/shared/tmp/restart3-merge/gates-c2.log`): tcb 870/4, collections 58 match (restart3 530/0 =
restart1's 508 plus 22 HTTP/net axioms, a subset of putget3's 640), links, gen-init, mode 417, api, interfaces ok;
goose and the Go gates fail on go.sum only (unpushed fork). **bounds FAILS: 356 vs 351**, `stock` 5 in
`examples/etcd/restart` (`Swap.lean` 250/280/282/491, `Spec/.../raftSwap.lean` 63: the swap's pool of `srvServeRes`
copies and slot tokens), from C3, not the merge; needs an allow entry (the swap owns the pool) or a rework, decided
by etcd-grove-81, before landing.
Decided by etcd-grove-81 (2026-11-15): an owner entry in `etc/bounds-allow.txt` (the swap owns its `srvServeRes`/
slot-token pool, like the reader pools); `etc/bounds-check.py --check`: ok (351, baseline 351).
Left before landing: the fork push, goose with the real go.mod and go.sum, `restart3` (A1) lands first.

### Landing A1 (2026-11-15)
Merged lean `17d12658f5` (auth-lease S3a2) and origin/lean `e3b1f66570` (kvraft, proof-cleanup skill): conflicts only in
STATUS "Last updated" (one copy of each entry, ten newest kept) and status-history (append-only). go.sum of `examples`,
`examples/k8s/{compactor,etcd3}` at the pushed fork `6e8f0c004` (hashes from `go mod download`); `etc/featuregate-allow.txt`
paths at the new pseudo-version; `etc/goose.py --check` passes (`/shared/tmp/restart3-land/goose-check.log`). Full build
green (`/shared/tmp/restart3-land/build-a1.log`). STATUS entry for A1 added. Then `etc/land.sh`.

### Landing `restart3-c` (2026-11-15)
Merged lean `bf5cefbcaf` (A1 landed; only conflict this handoff). The statement of `etcd_restart3_safe` approved by
the user, 2026-11-15, via etcd-grove-81 (Results' module docstring says so). Full build green
(`/shared/tmp/restart3-land/build-c.log`); `etc/tcb-report.py --check` 870/4; restart3 collection 530/0. STATUS entry
added. Then `etc/land.sh`.
