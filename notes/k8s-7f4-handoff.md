# k8s 7f-4 handoff (2026-11-12; branch `k8s-7f4`, worktree `/shared/etcd-grove-k8s7f`)

**Read first:** `notes/k8s-7f4-draft.md` (the plan), `notes/k8s-7f4-rebaseline.md` (what changed;
§4 is the order; approved by etcd-grove-81, Q-RB1..4), `notes/k8s-7f4-freeze.md` (steps 1-2),
the worktree's untracked `questions.md` (decisions), `/shared/tmp/coord-81/common-rules.md`.

## Done
- 7f-1 on lean (`3a08c2abee`), 7f-2 on lean (`6803e4e0fd`).
- The re-baseline, approved (`ba7622a0ea`); lean `802c4824aa` merged (questions.md untracked again:
  never re-add a tracked `questions.md`; `notes/walfs-questions.md` is lean's, leave it).
- Step 1 (enumerate): `notes/k8s-7f4-freeze.md` §1.
- Step 2 (the trusted package): **as text only**, `notes/k8s-7f4-freeze.md` §2 (T-a..T-f).

- Step 2 in Lean (2026-11-12, this branch): T-a, T-b, T-c, T-e, T-f as `notes/k8s-7f4-freeze.md` §2
  states them now (with file:line references and the review points); T-d deferred to 7f-3 (81).
  Go evidence: `examples/premisefix/streamctx` (passes; run with GOWORK=off). New modules:
  `Proof/.../api/v3rpc/SrvCtxWeak.lean` (`srvCtxWeak`, `noLeaderErr`, `srvCtxWeak_of_isContext`),
  `Proof/go_etcd_io/etcd/pkg/v3/traceutil/StartLaws.lean` (`Tracer.Start.spec_txn`, the old triple;
  the nine request-path callers use it).

## Next, in order
1. **STOP: the Freeze package for 81's independent review** (freeze §2, the commit, the interface
   diffs: none; tcb baseline unchanged, the new axiom `metadata.incomingOf_of_value` is not yet
   reached, it enters at step 3). Hard stop (trusted text). Commit `783fd4c8c8`.
2. After the review: steps 3-6 of the re-baseline's §4 (laws: `libCtxOkC`/`spanCtxOkC` from
   `ctxValueFrom`, back to the WP forms; R-4's lemma; interceptor branch and monitor, `sKey` first;
   Watch, with the mvcc API checkpoint; LeaseKeepAlive with LeaseRenew and the local `WithTimeout`
   lemma over `srvCtxWeak`; strengthen `isReqAuth_ctxM`/`isReqAuthBound_ctx` to drop `txnCtx`;
   the deletion of `runsNoRequireLeader`, hard stop).

## Pitfalls
- `context.wp_WithCancel_any`/`wp_WithTimeout` need `isContext parent`: the interceptor's input must
  stay strong (R-3); `LeaseRenew`'s `WithTimeout(ctx1)` over a weak `ctx1` needs the local lemma.
- grpc's run context's WP facts (`grpcRunCtx`) do not cross `WithCancel` (`LibKeysChain.lean`'s
  header): use T-a's chain forms for the wrapper.
- The handler's error must be `srvErrOk`: context errors via `applyErrIs_srvErrOk`
  (`watchServer__Watch.lean:392`), `ErrGRPCNoLeader` via `SeNL` (`newStreamInterceptor.lean`).

## Build
Every lake command with `--packages=/shared/tmp/manifest-ddc.json` (scripts: `LAKE_OPTS=...`), under
`systemd-run --scope -q -p MemoryMax=64G`; full builds also under
`flock /shared/tmp/etcd-grove-build.lock`. The worktree's `.lake/build` is stale (from 2026-11-08):
check `df -h /shared` (90G free on 2026-11-12) and ask 81 before seeding; the 7f-2 worktree
(`/shared/etcd-grove-k8s7f2`, landed) has a fresh full build of lean `6803e4e0fd` that 81 can `mv`
here. A full build was killed once at the cap on 2026-11-12 and passed on the retry.
