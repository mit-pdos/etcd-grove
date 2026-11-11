# premise-fixes-8c handoff (client half: C1, C2, C3)

Scope: `/shared/tmp/premise-fixes-8/scope.md` (approved, "## Decisions"). Coordinator: etcd-grove-81.
Worktree `/shared/etcd-grove-pf8c`, branch `premise-fixes-8c` (cut from lean `da225483c9`). The
server half (S1/S2) is in `/shared/etcd-grove-pf8`; don't touch its files.
Decisions and forms: `questions.md` (worktree root, untracked).

## C1 contents

- C1 (trust change, approved):
  - `Proof/context/LibKeysChain.lean`: `metadata.outgoingCtxOkC` (Perennial's `ctxValue` at
    `mdOutgoingKey{}`) and its laws `_background`, `_todo`, `_from`, `_valueCtx`, `_ownKey`, `_raw`,
    `_todoFrom`, `_bgFrom`, `outgoingCtxOk_of_C`, `context.keyEqOk_of_ty_ne`.
  - Stronger posts: `WithCancelTodo` (+ `ctxValueFrom todoCtxVal ctx'`), `WithTimeoutBackgroundMd`,
    `WithRequireLeader` (inner triple), `AppendToOutgoingContext` (+ `outgoingCtxOkC`).
  - `wait.channelContext.Deadline` spec + proof (translated; for C3's `chanCtx_ok`; not linked yet).
  - Go tests `examples/premisefix/ctxvalue/clientctx_test.go`: `TestClientCallCtxPanics` (the
    scratch file's four contexts, Invoke and NewStream, plus a `withVersion` copy) and
    `TestClientContexts`. Pass.

## C1: LANDED

lean `f808e61706` (2026-11-11; gates all passed, `/shared/tmp/premise-fixes-8c/land-c1.log`). The
four trusted texts and the three forms were approved by etcd-grove-81 (`questions.md`).

## C2 (the cascade; no trust change): LANDED

lean `23e7eedd58` (2026-11-11; gates all passed, `/shared/tmp/premise-fixes-8c/land-c2.log`),
accepted by etcd-grove-81 with the forms in `questions.md`. C3 waits for a fresh brief.

Commits `00aff9fc2c`..`c6fac95dc1`, lean merged (`ef76c3ad9e`, with S1). Done:
- The 11 contracts take `metadata.outgoingCtxOkC ctx`; the real client's proofs; the cache
  (`Cache.get`, `serverRevision`, `Get`, `conditionalProgressRequestor.run`, `isCacheFields`).
- `WithTimeoutBackground.spec`'s post + `ctxValueFrom backgroundCtxVal ctx'` (decided by
  etcd-grove-81), `client.wp_WithTimeout_bg`'s + `outgoingCtxOkC ctx'`; examples' users;
  `partition/MainWatch`.
- concurrency: `isEtcdMutexClient`, `isEtcdSTMClient`, `stmEnv`, `stmOptionsOwn`, `isSession`
  (octx and ctx) carry it; specs `NewSession` (pctx), `Mutex.{Lock,TryLock,Unlock,tryAcquire}`,
  `Election.{Campaign,Proclaim,Resign,Leader,Observe,observe}`, `NewSTM{ReadCommitted,Repeatable,
  Serializable}`, `mkSTM`, `WithAbortContext`, `waitDelete(s)`, `lockerMutex.{Lock,Unlock}` take it;
  `Session.Ctx`'s post gives it.
- recipes: `WaitEvents`/`WaitPrefixEvents` (WithCancel(Background()) by `_bgFrom`).
- leasing: `isLeasingClient`, `isLeasingKV`, `isLeasingEtcdClient`, `ownTxnLeasing` carry it; 17 specs
  take it (`Get`, `Put`, `Delete`, `Do`, `Txn`, `get`, `put`, `delete`, `deleteRange`,
  `deleteRangeRPC`, `acquire`, `revoke`, `revokeRange`, `revokeLeaseKvs`, `rescind`, `tryModifyOp`,
  `waitRescind`, `monitorLease`, `guard`, `guardRanges`, `revokeFallback`).
- v3lock/v3election handler specs (`lockServer.Lock`, `electionServer.{session,Campaign,Proclaim,
  Resign,Leader}`) take it (exported: their linked results).
- Producers: `isNewClient`'s ctx clause carries it (`newClient`, law `isNewClient_ctxC`);
  `chanCtx_outgoingCtxOkC`. Nothing consumes them yet.
- Every affected leaf (119, `etc/importers.py --leaves --git f808e61706`) built before the merge.

Checks (after merging lean `e5afedb770`, S2 and restart S1 included; HEAD `1a2514e0b5`): full build
clean (`/shared/tmp/premise-fixes-8c/full.sh`, 14018 jobs), `etc/tcb-report.py --check` matches
(865 axioms, 5 sorries), every collection matches, the five `etc/api` interfaces unchanged,
`gen-init --check` clean. STATUS entry written. Ready to land on etcd-grove-81's go: merge lean
again, then `etc/land.sh`.

Tools: `/shared/tmp/premise-fixes-8c/lb.sh FILE...` (a targeted `lake build` of files, errors only,
under the 64G cap; full log `/shared/tmp/premise-fixes-8c/lb.log`). Do not run several
`etc/lean-check.py` files at once on a cold import tree: parallel `lake setup-file`s raced and lost
`.olean`s (`BaseApply.olean` missing); `lb.sh` is reliable.

## C3 (the flip): implementation in progress (handed off at context limit)

Stop 1 approved by etcd-grove-81 (`questions.md`; texts in `/shared/tmp/premise-fixes-8c/c3-trusted.md`).
Decisions entry written ("Premise fixes 8, part C3", with the correction to D4). Commits `78fe100e76`
(Go case), `81dfaef76c` (the restatement and most of the cascade), then the commit with this note.

Done (all built in targeted builds unless noted):
- InvGrpc: `ctxDeadline`, `ctxWithCancelOk`, `ctxQuiet`/`ctxErrs`/`ctxOk` restated; laws
  `ctxOk_of_isContext`/`_errs`/`_quiet` (take `outgoingCtxOkC`), `ctxOk_outgoingC`.
- `FromOutgoingContext.spec` (+ `outgoingCtxOk`), `watchCtx` (+ `"#HOut"`, `watchCtx_of_isContext` takes
  it, `watchCtx_outgoingC`), `WithCancelValCtx.spec` post (+ `outgoingCtxOkC ctx'`), `streamKeyFromCtx`
  docstring, `kaCtxOk` (+ `outgoingCtxOk`).
- Producers: `ctxQuiet_todo`/`_background`, `todo_ctx`/`background_ctx`, `quiet_ctx`,
  `ctxErrClient_quiet`, `chanCtx_ok` (now takes `channelContext.Deadline`/`Value` specs and
  `wait.Assumptions`; `go_type_set` proves no AfterFunc), `chanCtx_watch` (+ `wp_Value`), the k8s
  compactor proofs (two new hypotheses; `etc/link-lean-first-k8s-etcd3.txt` and the regenerated k8s
  etcd3 `Link.lean`).
- Forms (to list at the checkpoint, "form decided by the agent"): `isWGS`'s second conjunct becomes
  `((∃ vs, …) ∗ outgoingCtxOkC G.ctx)`; `lessorAt`/`lessorAtS`'s stop-context slot becomes
  `(isContext sc scd ∗ outgoingCtxOkC sc)`; `openWatchClient.spec`, `lessor.KeepAlive.spec`,
  `watcher.RequestProgress.spec` take `outgoingCtxOkC ctx` (callers in the branch discharge it); new law
  `metadata.outgoingCtxOk_of_valueWand` (LibKeysChain); the newClient join carries `outgoingCtxOkC cx`.
- Full build (after `81dfaef76c`): the only failures were the `watchCtx_of_isContext` callers. Fixed
  since: `KMWatch`, `auth/Work` (built). **Not yet rebuilt:** `examples/etcd/{watch/Main,
  compactwatch/checkCompactRev, compactwatch/Main, auth/Main}`: their `wp_WithCancel_Background` post
  is `⟨cancel, isContext, isCancelCtxCtx ∗ ctxValueFrom⟩`; the pattern is now `⟨…, -, #xFrom⟩` with
  `ihave #xO := metadata.outgoingCtxOkC_bgFrom x $$ xFrom` (the `isplitl [] <;> iassumption` at the
  `watchCtx_of_isContext` call then finds `xO`). Earlier cascade errors in those files (watch/Main
  454/510, auth/Main 614/631) should be consequences; check.

Next, in order:
1. `lb.sh` the four example files; fix.
2. Full build (`/shared/tmp/premise-fixes-8c/full.sh`, under the lock and 64G cap).
3. `etc/tcb-report.py --check` (865 axioms, 5 sorries; LAKE_OPTS=--packages=/shared/tmp/manifest-ddc.json),
   every collection, `etc/gen-interface.py etc/api/<pkg>.txt --check` (client/v3, concurrency, cache,
   raft, ...: regenerate the changed ones and list the changed exported statements), `etc/gen-init.py --check`.
4. STATUS entry (oldest to status-history, append-only, check `wc -l`), handoff, then STOP before
   land.sh with the changed exported statements. Stage B waits on C3.

## Pitfalls

- Adding a conjunct to a stored predicate shifts positional `icases` patterns: nest the new fact inside an
  existing slot (as done for `isWGS`, `lessorAt`) rather than append.
- `gen-link.py` prints to stdout: redirect into the `Link.lean`.

- Adding a conjunct to an axiom's post breaks `icases` patterns of its users: grep for the
  `wp_apply ... as` lines (`newClient`, `TimeoutCtx.wp_WithTimeout_bgMd`, auth `reqCtx`/`Work`).
- `ctxValue` needs `[context.Assumptions]`; `outgoingCtxOkC_ownKey` needs
  `[google_golang_org.grpc.metadata.Assumptions]` (struct key equality).

## Build

`flock /shared/tmp/etcd-grove-build.lock systemd-run --scope -q -p MemoryMax=64G lake build --packages=/shared/tmp/manifest-ddc.json`
(TMPDIR=/shared/tmp). Single files: `LAKE_OPTS=--packages=/shared/tmp/manifest-ddc.json etc/lean-check.py FILE`.
