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

## State at this handoff (2026-11-12, end of the first 7f-4 agent's context)

- `783fd4c8c8`: the trusted package v0 (T-a, T-b, T-c, T-e, T-f), built and gated. **Reviewed by 81:
  NOT READY** (findings: `/root/.claude-csail/projects/-shared-etcd-grove/c04a65b0-a272-4ae4-94c7-91aa4a20ea30/subagents/workflows/wf_842ada2f-10d/journal.jsonl`;
  read the `findings` of the two `result` entries).
- The handoff commit (this one) also carries, **NOT BUILT**:
  - T-e' draft (decided by 81): `Proof/go_etcd_io/etcd/server/v3/auth/CtxDone.lean` (`auth.ctxDoneAny`,
    `_of_isContext`; lean-checked), `auth.ctxDoneAny_of_srvCtxWeak` in `SrvCtxWeak.lean` (lean-checked),
    `auth.ctxDoneAny_of_txnCtx` in `InvRequest.lean`; `isReqAuth`/`isReqAuthBound` take
    `libCtxOk ctx ∗ auth.ctxDoneAny ctx (∗ RD)`; repairs in `AuthReqDerive.lean`,
    `EtcdServer__AuthInfoFromCtx.lean` (unchecked).
  - B1: the axiom `metadata.incomingOf_of_value` dropped (`Incoming.lean` back to lean's text).
    Nothing used it.
  - freeze §2's "T-e'" section (marked draft).

## Next, in order (81's decisions on the review, 2026-11-12)

1. **B1, without a new axiom.** Index the handler side by the stored metadata value `v` (the
   transport MD), not by `incomingOf ctx` (the spec lens's fix): an opaque
   `metadata.incomingOfVal : GoInterface → Option …`; `FromIncomingContext.spec` quantifies `v` and
   takes `⌜incomingRes v⌝ ∗ valueAt ctx mdIncomingKeyAny (· = v)`, its post speaks of
   `incomingOfVal v` (sound: the call returns only after `Value` returned `v`); the handlers' `Spec`
   (grpcAccepted, `srvStreamInterceptorOk`, `_Watch_Watch_Handler`, the unary arm too if it is the same
   index) takes `incomingOfVal v` of grpc's run value; the wrapper's `valueAt (· = v)` is proved from
   its code (promotion to the `WithCancel` child, `ctxValueFrom`, T-a's chain form). Enumerate every use
   of `incomingOf` first (`etc/importers.py --uses incomingOf Proof/google_golang_org/grpc/metadata/Incoming.lean --files`:
   `FromIncomingContext`, `WithValue.spec`, `Tracer.Start`, `EnsureTrace`, `auth/InvAuth`'s
   `ctxTokenOf`, `Outgoing.lean`'s delivery). If that cannot work, per-constructor preservation (as
   `WithValue.spec`'s post) instead. Either way: show in the package, explicitly, that a context
   whose `Value` loops (`valueAt` for every `v`) cannot equate two contexts' metadata (the review's
   `loopCtx` program). This is a trusted-text change: if it grows past the stream path, report to 81
   before writing it all.
2. **T-e'**: build it; correct `isReqAuth`'s docstring (auth off: only `Value`; auth on, simple token:
   the token check selects on `Done()`); keep the full `libCtxOk` and record why (review m1: e.g. the
   stream path carries it anyway, and a narrower premise would differ from `checkLeaseRenew`'s).
3. **Tracer.Start (M2):** add `trace.spanCtxOk ctx` to its pre (callers: `grpcRunCtx`/`libCtxOk` on the
   request path, T-a's `spanCtxOkC` (via the step-3 law) on the stream path; `spec_txn` gains it);
   then delete the spec's Open note and update the audit row (`notes/audit.md`).
4. **libCtxOkC (spec M1):** add `ctxValue ctx trace.spanKeyVal trace.spanRes`, the full chain form
   of `libCtxOk`'s four parts. **Spec m3:** a law deriving `grpcRunCtx`'s WP parts (`spanCtxOk`,
   `libCtxOk`) from the chain forms (`context.valueAt_of_ctxValue`, needs `isPkgInit context`), or keep
   only `grpcRunCtx`'s etcd-key part on the stream arm.
5. Minors: (a) a sentence in `srvRawStreamIs`/`grpcRunCtx`: the configuration adds no stream
   interceptors or stats handlers through `GRPCAdditionalServerOptions`; (b) rerun
   `examples/premisefix/streamctx` at go1.27.3 (`GOTOOLCHAIN=go1.27.3`) and record it; optionally an
   already-cancelled `RenewHTTP` case; (c) the `Tracer.Start` disjunction as a known departure in
   `notes/decisions.md` (and make the docstring's "not widened" precise: `srvCtxWeak` admits new
   program contexts, but `isContext` already admitted the same refuting ones); (d) list the
   collections whose roots reach `acceptRun` or the prometheus axiom (`etc/tcb-report.py --roots
   'acceptRun|StreamServerInterceptor'`) in §2.
6. Build (targeted: `etc/importers.py --leaves` on the changed files, then full), tcb `--check` (with
   T-b gone the baseline should still match; list any diff), the 55 collections, axiom-tok (+selftest),
   model-param, errdesc, gen-interface on the six lists; commit; freeze §2 gets a "Revision 1" section
   (what changed per finding). **STOP for 81's re-review.**
7. After that: steps 3-6 of the re-baseline's §4 as before.

## Pitfalls
- `context.wp_WithCancel_any`/`wp_WithTimeout` need `isContext parent`: the interceptor's input must
  stay strong (R-3); `LeaseRenew`'s `WithTimeout(ctx1)` over a weak `ctx1` needs the local lemma.
- grpc's run context's WP facts (`grpcRunCtx`) do not cross `WithCancel` (`LibKeysChain.lean`'s
  header): use T-a's chain forms for the wrapper.
- The handler's error must be `srvErrOk`: context errors via `applyErrIs_srvErrOk`
  (`watchServer__Watch.lean:392`), `ErrGRPCNoLeader` via `SeNL` (`newStreamInterceptor.lean`).

## Build
Full builds from a stale tree were OOM-killed at the 64G cap twice (aggregate parallelism); a
targeted build of the changed modules first, then `etc/timed-build.py` for the full build, passed.

Every lake command with `--packages=/shared/tmp/manifest-ddc.json` (scripts: `LAKE_OPTS=...`), under
`systemd-run --scope -q -p MemoryMax=64G`; full builds also under
`flock /shared/tmp/etcd-grove-build.lock`. The worktree's `.lake/build` is stale (from 2026-11-08):
check `df -h /shared` (90G free on 2026-11-12) and ask 81 before seeding; the 7f-2 worktree
(`/shared/etcd-grove-k8s7f2`, landed) has a fresh full build of lean `6803e4e0fd` that 81 can `mv`
here. A full build was killed once at the cap on 2026-11-12 and passed on the retry.
