# Premise fixes 5: handoff

Branch `premise-fixes-5`, worktree `/shared/etcd-grove-pf5`, off lean `f4e98c54f9` (its `.lake/build` a
full build at that commit, moved in from premise-fixes-2's worktree). Scratch: `/shared/tmp/premise-fixes-5/`.
Coordinator: etcd-grove-81.

Two findings:
- **A. ctxOk's Done gap** (7e-1's axiom attack, `/shared/tmp/k8s7e1/attack-wrb/`): `ctxQuiet` and
  `ctxErrs` (`Proof/google_golang_org/grpc/InvGrpc.lean`) say nothing of `Done()`, so the axioms taking
  `ctxOk` that select on `ctx.Done()` (`waitRetryBackoff`, grpc's `Invoke` through `grpcInvokerOk`,
  `NewStream`) are false of a context whose `Done()` panics, or is closed while `Err()` is `nil`.
- **B. keySized**: `mvcc.keySized` (`storage/mvcc/BackendBridge.lean`) assumed by `bootOk`'s `#Hsz`
  (`InvBoot.lean`), the restart contract's (`InvRestart.lean`) and mvccrand's `Hks`; to become one counted
  bbolt axiom `backend.rtxSnap_size` and a proved `keySized_all`.

## State

- Checkpoint (a), the design, reported to etcd-grove-81 (2026-11-10); waiting for approval. No Lean
  changed yet.

## Next, in order (after approval)

1. A: `ctxDoneCh`/`ctxDone`/`ctxErrsErr` in `InvGrpc.lean`, `ctxQuiet` + Done, `ctxErrs := ctxDone ∗
   ctxErrsErr`; `ctxErrClient_eq_errs` to `ctxErrsErr`; re-prove `ctxQuiet_todo`/`_background`,
   `chanCtx_ok` (Done of `channelContext` returns `stopCh`), `ctxErrClient_quiet`,
   `Client__unaryClientInterceptor` (split the conjunction), `Client__getToken`.
2. A: Go test `examples/premisefix/ctxdone` (the contract of TODO/Background/WithCancel/ContextForChannel,
   the two panics of waitRetryBackoff's copy); wired by gates step 9 automatically.
3. A: `notes/axiom-review/ctxok-done.md` and a `notes/audit.md` row.
4. B: `axiom rtxSnap_size` in `backend/InvBbolt.lean`; `rtHeld_keyBound` (backend), `keySized_all`
   (BackendBridge); drop `#Hsz`, `Hks`; docstrings (`etcdserver/Results.lean` ~883, mvccrand Adequacy:34).
5. Merge lean (premise-fixes-4 touches context error facts), full build, gates, tcb `--check --update`,
   collections, interfaces. Stop before land.sh.

## Build command

```
export TMPDIR=/shared/tmp LAKE_OPTS=--packages=/shared/tmp/manifest-ddc.json
flock /shared/tmp/etcd-grove-build.lock systemd-run --scope -q -p MemoryMax=64G lake --packages=/shared/tmp/manifest-ddc.json build
```
