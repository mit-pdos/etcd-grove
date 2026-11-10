# premise-fixes-4: handoff

Branch `premise-fixes-4` (worktree `/shared/etcd-grove-pf4`, off lean `d33293fe11`), session agent
of etcd-grove-81. Brief: fix the round-2 premise attack's findings on `etcd_partition_safe`
(`/shared/tmp/coord-81/round2/findings.json`). Scratch: `/shared/tmp/premise-fixes-4/`.

Build: `flock /shared/tmp/etcd-grove-build.lock systemd-run --scope -q -p MemoryMax=64G lake build
--packages=/shared/tmp/manifest-ddc.json`. Go tests: `cd examples; GOWORK=off go test ./premisefix/...`
(under `systemd-run --scope -q -p MemoryMax=32G`).

## Done

1. **rnSetLoggerOk** (critical; decided by etcd-grove-81: prove it). Raft's `isInitialized`
   (`Proof/go_etcd_io/raft/v3/Base.lean`) gains `"#HloggerMu" ∷ sync.isMutex (globalAddr raftLoggerMu)
   (∃ l, globalAddr raftLogger ↦ l)`; raft's `Init.lean` (hand-written: raft is `RAFT_INIT`, external
   to `etc/gen-init.py`) makes the mutex from the two allocations it used to drop. `SetLogger.spec`
   (`{{ isPkgInit raft }} SetLogger l {{ True }}`) proved (`Proof/go_etcd_io/raft/v3/SetLogger.lean`),
   in `etc/api/raft.txt` and raft's Link; `newRaftNode.wp_proof` takes it as a callee (server Link).
   `rnSetLoggerOk` deleted; dropped from `newRaftNode`/`bootstrappedRaft.newRaftNode`/`NewServer`'s
   specs, `NodeStart`, `etcdstart.commonPremises`, `OneMember`, putget3/auth/leaseexpiry's bags and
   every `icases Hprem` pattern.
   Full build green (d168bb2f5e), interfaces regenerated (raft `Base`, `SetLogger`; etcdstart
   `Defs`/`OneMember`), tcb baseline and every collection unchanged.
2. Sweep (fix 2): no other conjunct has the pattern; open items for the coordinator: `mvcc.keySized`
   (`#Hsz` in `bootstrapContract`'s post, mvccrand's `Hks`: possibly refutable, nothing bounds
   `rtHeld`'s bucket), `ContextReadErrs`/`ContextErrsClient` (provable but for `descs`: `errDesc`
   opaque), `#Hmembers` (stronger than `Members.spec`), bboltfs `Hinit_wp`. Checkpoint (a) report.
3. Go tests for fixes 3-5 (`examples/premisefix/{httpmux,httppath,fmtarg}`), passing at go1.27.3.

## State at df64187851 (+ this handoff commit)

- Fix 1: done (checkpoint (a) accepted).
- Fixes 3, 4: done, rafthttp callers discharged.
- Fix 5: `fmt.argOk` restated (approved); `fmt.methodSet_none` + tactic `fmt_method_none`
  (`Spec/fmt/Errorf.lean`) prove the method facts from `go.MethodSetIs`; `fmt_args_ok` uses it.
  Fixed callers: Duration, types.ID, semver, syscall.Errno, bbolt `fmtErrorOk_argOk`, cache's
  `ErrUnsupportedRequest` (`cacheInit` + `etc/gen-init.py` SPECIAL). The last full build
  (`/shared/tmp/premise-fixes-4/build4.log`) fails in exactly three modules, all fix-5 callers:
  `rafthttp/snapshotHandler__ServeHTTP` (`http.errStrOk`), `cache/Cache__getWatchLoop` (cache's
  `errStrOk`), `cache/conditionalProgressRequestor__run` (`isEtcdProgressNotifier`, from the
  client's `RequestProgress` `statusErrOk`). Their dependents were not built.
- Fix 6: docstrings done (partition Results/Adequacy/AdequacyWatch/Main: CM-1..4; H1 in
  `ContextReadErrs.descs` via `etc/gen-init.py`, read/Init.lean is generated; rnClusterOk);
  STATUS section "Premise fixes 4" (CM-1, CM-5 caveats) and decisions entry written.

## Next, in order (option A approved by etcd-grove-81, 2026-11-10)

1. Go test FIRST: move/extend `/shared/tmp/premise-fixes-4/noformat/noformat_test.go` into
   `examples/premisefix/fmtarg` (the examples module has grpc and etcd): check that none of these
   implements `fmt.Formatter`: the 13 std errors already there, grpc's `*status.Error` from
   `status.Error(codes.X, "m")` and from `status.FromContextError(ctx.Err())` (`.Err()`),
   `rpctypes.EtcdError` (e.g. `rpctypes.ErrGRPCNoLeader`'s client form `rpctypes.Error(...)`),
   `context.DeadlineExceeded`. If any does, STOP and report.
2. Add `⌜methodSet ei.ty !! go!"Format" = none⌝` (trust text, approved) to: `http.errStrOk`
   (`Proof/net/http/Boundary.lean:341`, inside the `∃ ei` clause), cache's `errStrOk`
   (`Proof/go_etcd_io/etcd/cache/v3/Base.lean:686`), `statusErrOk` (same file, :338) and
   `isEtcdProgressNotifier`'s error clause (`cache/v3/InvEtcd.lean:1154`).
3. Repair producers: about 10 that unfold `statusErrOk` (`grep -rln "unfold.*statusErrOk\|iunfold
   statusErrOk" Proof`: rpctypes `Error.lean`, client `ErrorsNewOk`, `watcher__Close`, k8s etcd3
   `Base`/stores, apply `Base`, cache `Base`), `http.errStrOk`'s (`Codec.errorString_errStrOk`,
   `ReaderRun.wp_Is_errStrOk`, `errStrOk_nil`), cache `errStrOk_of_statusErrOk`, `errStrOk_of_ctx`
   (`Cache__watchEvents.lean:289`). Use `fmt_method_none` for concrete types. Then the three
   consumers: `argOk_of_errStrOk` (snapshotHandler), getWatchLoop line ~96, the requestor ~173.
4. `etc/errdesc-check.py`: its REVIEWED entries must still describe the restated
   `statusErrOk`/`errStrOk`; update them if the gate flags them.
5. Merge lean (f4e98c54f9 or later: premise-fixes-2, raft-entsize); STATUS "Last updated" entry
   (ten newest; move the oldest to `notes/status-history.md`, append-only, check `wc -l`).
6. Full build; regenerate interfaces (all `etc/api/*.txt`, `LAKE_OPTS=--packages=...`);
   `etc/gen-init.py --check`; `etc/gates.sh`; `etc/tcb-report.py --check` (expect no axiom change)
   and every collection `--check` (`--reuse`); checkpoint (c) report; stop before `etc/land.sh`.

Closed statements changed (fix 1, permitted): every etcd closed theorem lost `rnSetLoggerOk` from its
premises (via `etcdstart.commonPremises`, `etcdstart.premises`, `cluster3.premises`, putget3/auth/
leaseexpiry's bags); specs `newRaftNode`, `bootstrappedRaft.newRaftNode`, `NewServer` lost it too.

## Pitfalls

- `isInitialized` changed: the whole repository rebuilds.
- `notes/status-history.md` is append-only.
- `read/Init.lean` and cache's `Init.lean` are generated: edit `etc/gen-init.py`, run it, `--check`.
- `lake build` auto-backgrounds after 180 s in this harness: run full builds with `run_in_background`.
