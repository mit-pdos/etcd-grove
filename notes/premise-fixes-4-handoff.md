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

## State at 104cecf56e (second agent, 2026-11-10)

- Step 1 done: `examples/premisefix/fmtarg` `TestNoFormatter` (873b4d403d, 62b071df72): none of the 13
  std errors, grpc `*status.Error` (`status.Error`, `FromContextError(...).Err()`), `rpctypes.EtcdError`,
  the context errors, bcrypt's `ErrPasswordTooLong`/`InvalidCostError` implements `fmt.Formatter`.
- Step 2 done: the four predicates carry `⌜methodSet _.ty !! go!"Format" = none⌝`.
- Step 3 (producers), done except the STOP items below: `errLeaf` (5th conjunct), `ErrorStringLeaf.noFormat`,
  `errorString_errLeaf`, `rpctypesEtcdErrorTy` + `RpctypesEtcdErrorMethods.noFormat` (gen-init),
  `authErrVar`, `leaseErrVar`, `ctxDeadlineLeaf`, `context.errStringOk` (proved from `isCtxErr`),
  cache `wp_New_errStrOk`/`wp_Errorf_errStrOk` (step into Perennial's model; faithful for basic args),
  `errStrOk_ok` takes `hF`, `errStrOk_noFormat`, `statusErrOk_of_leafMsg`/`applyErrIs_valLeaf`/
  `clientErr_statusErrOk_of_leaf` take `hF`.
- `EtcdGrove.ContextReadErrs` (a closed theorems' premise) is stated over `errVarLeafW`/`ctxDeadlineLeafW`,
  the old bodies under new names, so its unfolded statement is unchanged; `ContextReadErrs.errs_strong`
  derives the Format facts from Perennial's `context.isInit` (`HCanceledCell`, `HDeadlineExceededTy`).
- Step 4 done: errdesc-check REVIEWED entries mention the Format fact.
- Formerly blocked, now approved (trust text, etcd-grove-81 2026-11-10): `WatchResponse__Err` needs Format of rpctypes'
  `ErrCompacted`/`ErrFutureRev` (axioms `ErrCompacted_init`, `ErrFutureRev_init` in rpctypes `Init.lean`,
  via `etc/gen-init.py` custom posts, and `rpctypesInit`'s two conjuncts); `EtcdServer__UserAdd` needs it
  of bcrypt's errors (axiom spec `Spec/golang_org/x/crypto/bcrypt/GenerateFromPassword.lean`). Draft:
  add `∗ ⌜methodSet e.ty !! go!"Format" = none⌝` (rpctypes posts), `∧ methodSet ei.ty !! go!"Format" = none`
  (bcrypt's error clause). See the full build log `/shared/tmp/premise-fixes-4/build6.log`.

## State at checkpoint (c) (third agent, 2026-11-10)

- Next 1 done (5b31cdc2c7): `rpctypes.ErrCompacted_init`/`ErrFutureRev_init` (gen-init custom posts,
  pat `%F@`), `rpctypesInit`'s two conjuncts, `bcrypt.GenerateFromPassword.spec`'s error clause carry
  the Format fact; `WatchResponse__Err`, `UserAdd` use it; decisions entry extended.
- Lean merged (f4e98c54f9, 55b49f0b24); STATUS "Last updated" entry added (the S1 + S2 entry moved to
  `status-history.md`, appended: 19128 lines, lean 19127).
- The full build then failed only in k8s `compactor__getCompactRev` (`fmt_args_ok` needs the Format
  fact: taken from `statusErrOk`); fixed; full build green (`/shared/tmp/premise-fixes-4/build8.log`).
- Interfaces: all five API lists regenerate to no change; `gen-init --check` ok; gates
  (`/shared/tmp/premise-fixes-4/gates.log`): build, links, tcb (845 axioms, 4 sorries, = baseline),
  53 collections match, goose, gen-init, model-param, pbschema, issues, errdesc, bounds, mode, api,
  import-all, premisefix ok; errorf-wrap failed on cache `Base.lean` (`wp_Errorf_errStrOk`), reviewed
  and added to REVIEWED (rerun alone: ok). A full gates rerun is left to `etc/land.sh`.

## Next, in order

1. Wait for etcd-grove-81's go after the checkpoint (c) report; merge lean again if it moved
   (raft-entsize touches rafthttp), rebuild, gates; then `etc/land.sh` (with
   `LAKE_PACKAGES=/shared/tmp/manifest-ddc.json`).

Closed statements changed (fix 1, permitted): every etcd closed theorem lost `rnSetLoggerOk` from its
premises (via `etcdstart.commonPremises`, `etcdstart.premises`, `cluster3.premises`, putget3/auth/
leaseexpiry's bags); specs `newRaftNode`, `bootstrappedRaft.newRaftNode`, `NewServer` lost it too.

## Pitfalls

- `isInitialized` changed: the whole repository rebuilds.
- `notes/status-history.md` is append-only.
- `read/Init.lean` and cache's `Init.lean` are generated: edit `etc/gen-init.py`, run it, `--check`.
- `lake build` auto-backgrounds after 180 s in this harness: run full builds with `run_in_background`.
