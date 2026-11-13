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

## Ninth agent (2026-11-13): Addendum T-j written and built; STOPPED for 81's axiom review

`43357ed9bc` (+ the notes commit after it): `context.madeCancelCtx` (opaque, `Proof/context/MadeCancelCtx.lean`)
and the trusted law `madeCancelCtx_of_isCancelCtx`; `v3rpc.ctxDoneErr`/`ctxChildErr` and laws
(`SrvCtxWeak.lean`); the local axiom `v3rpc.wp_WithTimeout_weak` (`v3rpc/WithTimeoutWeak.lean`);
`waitLeader`/`RenewHTTP` on `ctxDoneErr` (RenewHTTP keeps `netCtxOk`). **Finding T-j0**: T-h2's
`ctxDoneErr` without `#HParentCC` makes `RenewHTTP` panic via `propagateCancel`'s afterFuncer arm
(`TestRenewHTTPAfterFuncPanics`); `ctxDoneErr` keeps `#HParentCC` over `madeCancelCtx`. Checks: Addendum
T-j "Checks run, T-j" (tcb: one NEW axiom line, not updated). **Next, after the review:** tcb/collection
`--update`; `LeaseRenew` on `wp_WithTimeout_weak` (premise `srvCtxWeak ∗ levelTok`, T-h4: the default arm
becomes reachable), `LeaseKeepAlive`/`leaseKeepAlive` over the weak stream end (drop `srvStreamIsStrong`),
axiom-tok entry for `wp_WithTimeout_weak`; stop before step 6.

## Handoff point (2026-11-13, end of the eighth agent's context): T-i landed; LeaseKeepAlive next

Landed: lean `7b414c87f3` (T-i with the review's m1-m7: `etc/bgcancel-check.py` in `etc/gates.sh`;
`issues/etcd-timeout-transport-rw-timeouts-unused.md`; baselines without
`context.WithCancelBackground.wp_proof`, 866 axiom lines). Nothing unlanded on the branch.

**Next, in order** (81: "LeaseKeepAlive with T-h5's option (A); its trusted texts stop for my review"):
1. Trusted texts, as a new Addendum (T-j) in `notes/k8s-7f4-freeze.md`, written in Lean, built, then
   **STOP for 81's review** before any proof relies on them (T-h2 and T-h5 of the freeze note give the
   design):
   - `context.madeCancelCtx c` (new opaque, trusted: "allocated by `context`'s constructors, fields
     written only by `context`'s code") and the trusted law `madeCancelCtx_of_isCancelCtx`
     (Perennial's `isCancelCtx` holds only of the constructors' contexts);
   - `v3rpc.ctxDoneErr c s` (`SrvCtxWeak.lean`): `srvCtxWeak` without `#HParentCC`, `#HValue` at
     `&cancelCtxKey` returning nil, another dynamic type, or a `*cancelCtx` with `madeCancelCtx`
     (option (A); NOT T-h2's `#HValueAny`, refuted by `TestRenewHTTPNilCancelCtxPanics`);
     `v3rpc.ctxChildErr` (no token, `Err` nil or `isCtxErr ∨ noLeaderErr`); laws
     `ctxDoneErr_of_srvCtxWeak` (needs `madeCancelCtx_of_isCancelCtx`), `ctxDoneErr_of_child`;
   - the marked local axiom `v3rpc.wp_WithTimeout_weak` (new `v3rpc/WithTimeoutWeak.lean`, header
     "TRUST BOUNDARY, local, delete when notes/perennial-changes.md's 'context model over an error
     predicate' lands"): T-h2's statement, its post also `madeCancelCtx` of the child's embedded
     `*cancelCtx` via `ctxChildErr`; no netCtxOk wand needed (`ctxValueFrom parent ctx'` carries the
     chain form, T-h as written);
   - `waitLeader.spec`/`RenewHTTP.spec` move to `ctxDoneErr` (weaker premises); Go evidence: the
     existing `TestWithTimeoutWeak`, `TestNoLeaderTyped`, `TestRenewHTTPNilCancelCtxPanics` in
     `examples/premisefix/streamctx`, plus a test that a `madeCancelCtx`-shaped value (a real child)
     is fine.
   Gates for the review: build, `tcb-report --check` (report, no `--update`), collections, axiom-tok
   (entries for the new axiom's level token, as T-f'), model-param, gen-interface `--check`.
2. After the review: `LeaseKeepAlive`/`leaseKeepAlive` re-proved over the weak stream end (drop the
   temporary `srvStreamIsStrong`), `LeaseRenew` on `wp_WithTimeout_weak`; stop before step 6 (a hard
   stop; report the closed theorems it reaches).

Build: targeted `lake build --packages=/shared/tmp/manifest-ddc.json <modules>` under
`systemd-run --scope -q -p MemoryMax=64G`, then the full one with `etc/timed-build.py` under
`flock /shared/tmp/etcd-grove-build.lock`; land only via `etc/land.sh` (GOWORK unset), after 81's go.

## Eighth agent (2026-11-13): T-h0 + T-h6 landed; T-i written; STOPPED for 81's axiom review

Landed: lean `9c583ebbcf` (T-h0 + T-h6 with the T-h review's minors m1-m4, `ee11f69d91`; merged with
ctx-sweep fixes). **T-i** (`47ef0d7df0`, Addendum T-i of `notes/k8s-7f4-freeze.md`,
`notes/roundtripper-ctx-refuted.md`, audit row, Go tests `examples/premisefix/rtctx`): `http.WithContext_ok`
with rafthttp's round trippers refuted; fix: `WithContext_spec`'s post `http.reqCtx r' ctx` (opaque,
persistent), `roundTripperOk`'s `RoundTrip` takes `http.reqCtxBg r` (`context.bgCancelChild`,
`Proof/context/BgCancel.lean`: a `*cancelCtx` whose parent field is `Background()`), `netErr`'s
docstring names `context.Canceled`; `context.WithCancelBackground.spec`'s post gains `bgCancelChild` and
its axiom is now a proof (trust base: one axiom fewer); `srFixed` carries `bgCancelChild`.
**Next, after 81's review of T-i:** tcb/collection baselines (`--check --update`, axiom removed),
land; then T-h5 (`ctxDoneErr`, `ctxChildErr`, `wp_WithTimeout_weak` with option (A)) with
LeaseKeepAlive.

## Seventh agent (2026-11-13): T-h0's fix written; T-h5 soundness finding; STOPPED for 81

Done (each lean-checked `-a`, 0 errors): `da77c070e5` T-h0's fix (handoff steps 1, 2, 4's `RenewHTTP`
part, 6, 7: `Proof/net/http/NetCtx.lean`; `srvRawStreamIs`/`srvRawStreamIsW`/`srvStreamIsStrong` gain
`http.netCtxOkC ci`; `v3rpc.wrapperNetCtx`; `RenewHTTP.spec` takes `http.netCtxOk`; `Tracer.Start.spec`'s
post a **chain-form** wand; `LeaseRenew.spec`, `raftLeaseRenew` take `http.netCtxOkC`), `00ce547d39`
(`TestRunCtxChain` checks the keys). `etc/goose.py --check` passes. **T-h5** (freeze note): T-h2's
`ctxDoneErr` `#HValueAny` would make `RenewHTTP` false (typed-nil `*cancelCtx`,
`TestRenewHTTPNilCancelCtxPanics`); `ctxDoneErr`/`ctxChildErr`/`wp_WithTimeout_weak`/`waitLeader` NOT
written. Recommended: land T-h0's fix alone; the rest with option (A) at LeaseKeepAlive.
Build of T-h0 (`00ce547d39`): full build green (20261113-011402). Then 81 added the sweep's two
findings: (1) **done**, `9212d8cdea` T-h6 (`leaseTimeToLive` takes `http.netCtxOk`; `grpcRunCtx` gains
it, `netCtxOk_of_runCtx`; LeaseTimeToLive's specs/contract carry it; `examples/etcd/lease/ctxsweep_test.go`;
`notes/leasetimetolive-value-refuted.md`; audit row). (2) **NEXT, not started**: `http.WithContext_ok`
with `rafthttp.NewRoundTripper`/`newStreamRoundTripper` (`roundTripperOk`): record the request's context
(`reqCtx` in `reqOwn` or a persistent `reqCtxIs`), `WithContext_spec` takes `isContext ∗ http.netCtxOk`
(or a Background chain: every caller passes `WithCancel(Background())`; `http.netCtxOkC` of a child of
Background: `ctxValue_background` + `http.netCtxOkC_from`), `roundTripperOk`'s `RoundTrip` uses it; widen
`netErr`/`errStrOk` if the done-context error comes back. Findings: 81's workflow journal
`/root/.claude-csail/projects/-shared-etcd-grove/c04a65b0-a272-4ae4-94c7-91aa4a20ea30/subagents/workflows/wf_91727eee-383/journal.jsonl`
(search `WithContext_ok`). Record it in `notes/` (as `leasetimetolive-value-refuted.md`), Addendum T-h
(a T-h7 section), audit row. Then build, tcb --check (report, no --update; collections only after
81's review), axiom-tok, model-param, gen-interface --check, goose --check; STOP for 81's axiom review.
Gates script: `/shared/tmp/k8s7f4/gates/run.sh` (outputs in its directory).
Checks on `6d7f05f9aa` (T-h0 + T-h6): full build green (20261113-012612, 17567 jobs); `tcb-report --check`
matches the baseline (867 axioms, 4 sorries: no axiom added or removed, only restated); every collection
matches; axiom-tok ok (813 walked, 779 pass, 34 by an entry) and selftest; model-param, errdesc ok;
gen-interface --check on every API list: no diff; goose --check ok; Go tests pass
(`examples/premisefix/streamctx`, `examples/etcd/lease` T-h6 test).
Pitfall: inside `local macro` tactic quotations (`renew_forward`), `ihave #X := lemma $$ [...]` names do
not resolve later (hygiene); use the `ihave #X : P $$ []` form and `$Name` is an antiquotation there.

## Handoff point (2026-11-13, end of the sixth agent's context): T-h decided; Lean texts next

81 decided T-h (questions.md, 2026-11-13): T-h0 a refutation of the landed `RenewHTTP.spec`, fix
`http.netCtxOk ctx` (the three keys hold nil) with T-a's chain form extended to the three keys; T-h1/T-h2
accepted (`ctxDoneErr` for `waitLeader`/`RenewHTTP`, `ctxChildErr` for the child, the marked axiom
`v3rpc.wp_WithTimeout_weak`); `isTypedErr` NOT added. Wider context-key sweep: 81's own task, not here.
T-h lands on its own after 81's axiom review, before LeaseKeepAlive's proofs.

Done since: `3c58faced3` translates `net/http/httptrace` and `internal/nettrace` types only
(`etc/goose.py` project etcd, lean-root `internal/nettrace=`; `Code/net/http/httptrace.lean`
`net.http.httptrace.clientEventContextKey`, `Code/internal/nettrace.lean` `nettrace.TraceKey`,
`nettrace.LookupIPAltResolverKey`, namespaces under `Perennial`; check the exact names); `6988f81872`
`notes/renewhttp-value-refuted.md` and the audit row. Go tests in `36088aebf6`.

**Next, in order (Lean texts of T-h; nothing written yet):**
1. Keys and `http.netCtxOk` (new `Proof/net/http/NetCtx.lean` or beside `Proof/context/LibKeys.lean`):
   `httptrace.clientEventKeyAny := interface.mkOk clientEventContextKey.ty #(zero_val ..)` (as
   `metadata.mdIncomingKeyAny`), likewise the two nettrace keys; `http.netCtxOk ctx :=
   valueAt ctx k₁ (· = nil) ∗ valueAt ctx k₂ (· = nil) ∗ valueAt ctx k₃ (· = nil)`; the chain form
   `http.netCtxOkC ctx` (`ctxValue ctx kᵢ (· = nil)`), law `netCtxOk_of_netCtxOkC` (as
   `context.libCtxOk_of_libCtxOkC`, `context.valueAt_of_ctxValue`), `netCtxOkC_from` over
   `ctxValueFrom` (the keys are not `*int`: `notIntPtrKey`).
2. grpc's raw stream end (trusted, `InvGrpcStream.lean:435`): `srvRawStreamIs` gains `http.netCtxOkC ci`
   beside `context.libCtxOkC ci` (docstring: grpc's chain holds only grpc's, otel's and the transport's
   keys, `TestRunCtxChain`); `srvRawStreamIsW` its weak copy likewise (non-trusted, law
   `srvRawStreamIsW_of_raw`), the wrapper's carry as `v3rpc.wrapperLibCtx` (`WithCancel` child by
   `ctxValueFrom`, the promoted `Value`).
3. `v3rpc.ctxDoneErr`, `v3rpc.ctxChildErr` (in `v3rpc/SrvCtxWeak.lean`; text in the freeze note, T-h2),
   laws `ctxDoneErr_of_srvCtxWeak`, `ctxDoneErr_of_child`, and `srvCtxWeak_of_isContext` already gives
   the first from `isContext`.
4. `waitLeader.spec`, `RenewHTTP.spec` on `ctxDoneErr ctx cd`; `RenewHTTP.spec` also `http.netCtxOk ctx`.
5. The axiom (new `Proof/.../v3rpc/WithTimeoutWeak.lean`, header "TRUST BOUNDARY, local, delete when
   notes/perennial-changes.md's 'context model over an error predicate' lands"): T-h2's statement, and
   in the post also `□ (http.netCtxOk parent -∗ http.netCtxOk ctx')` (Go: `timerCtx.Value` at another key
   walks to `parent.Value`), so that `LeaseRenew` keeps the WP form through it.
6. `Tracer.Start.spec`'s post gains `□ (http.netCtxOk ctx -∗ http.netCtxOk ctx')` (a `WithValue` at the
   span key; stronger post of an axiom: list it in T-h).
7. Callers in this landing (LeaseRenew stays on `isContext` until LeaseKeepAlive): `LeaseRenew.spec`
   gains `http.netCtxOk ctx` (internal; its callers: `raftLeaseRenew` contract
   (`InvLeaseKeepAlive.lean:140`) gains it, `raftLeaseRenew_of_server` (`ServerLeaseRead.lean`)
   threads it); its proof: `WithTimeout` stays Perennial's (`isContext ctx1`), `netCtxOk cctx` needs
   Perennial's `wp_WithTimeout`'s `ctxValueFrom` plus the chain form: simplest is to take
   `http.netCtxOkC ctx` in `LeaseRenew.spec` instead and carry it through `Tracer.Start`
   (`ctxValue` across a `WithValue` at another key: `context.ctxValue_valueCtx`/`ctxValue_other`, if
   Tracer.Start's post gives the link; otherwise the WP wand of step 6 with a WP-form premise and
   step 5's wand once LeaseRenew uses the weak axiom). Decide by what Tracer.Start's post exposes.
   `RenewHTTP`'s and `waitLeader`'s proofs-of-use: `ctxDoneErr_of_srvCtxWeak (srvCtxWeak_of_isContext ..)`.
8. Build (targeted, then full), `etc/tcb-report.py --check` (expect: the new axiom
   `v3rpc.wp_WithTimeout_weak` in the baseline diff only if a root reaches it; it is not used yet, so
   likely NEW only in the repository axiom list), axiom-tok (new entries for the changed axioms'
   level-token binders if it asks), gen-interface (`etc/api/*.txt`), goose --check, the Go tests.
   Report the tcb diff WITHOUT `--update`. **STOP for 81's axiom review.** Then land T-h alone.
9. After that: LeaseKeepAlive (`LeaseRenew` over `srvCtxWeak ∗ levelTok 4` with the axiom and the
   reachable default arm: `errors.IsStatusErr.spec` for `ErrGRPCNoLeader` vs `Canceled`/
   `DeadlineExceeded`, the zap warn, `ErrCanceled`), `raftLeaseRenew`, `leaseKeepAlive`/`LeaseKeepAlive`
   over the weak end (the forked loop lends level 4 from its own thread token, `threadTok_lend4`),
   drop `srvStreamIsStrong`; stop before step 6.

## Sixth agent, continued (2026-11-13): landed; Addendum T-h written; STOPPED for 81's axiom review

**Landed: lean `bc86a6f6aa`** (`etc/land.sh`, all gates, after 81 accepted the bounds-allow entries).
81 decided option (c) for `WithTimeout` (questions.md). Writing it found (freeze note, Addendum T-h):
T-h0, a **refutation of the landed `leasehttp.RenewHTTP.spec`** (a context whose `Value` at net/http's
`httptrace` key panics meets `isContext`/`srvCtxWeak`; `TestRenewHTTPValuePanics`); T-h1, the child
of a weak parent cannot be `srvCtxWeak` (its `#HValue`/`#HParentCC` would claim Perennial's cancelCtx
invariant of a `*cancelCtx` storing `ErrGRPCNoLeader`); T-h2 the proposed texts (`ctxDoneErr`,
`ctxChildErr`, the axiom `v3rpc.wp_WithTimeout_weak`, `waitLeader`/`RenewHTTP` premises,
`isTypedErr` recommended not added); T-h3 Go tests (`TestWithTimeoutWeak`, `TestNoLeaderTyped`);
T-h4 `LeaseRenew`'s default arm reachable. `notes/perennial-changes.md`: "The context model over an
error predicate". **No Lean written for T-h.** Next after 81's review: the Lean texts, then
`LeaseRenew` (over `srvCtxWeak ∗ levelTok 4`, the axiom, the default arm's log), `raftLeaseRenew`,
`leaseKeepAlive`/`LeaseKeepAlive` over the weak end (the forked loop lends level 4 from its own
thread token, `threadTok_lend4`, as Watch's recvLoop), drop `srvStreamIsStrong`; stop before step 6.

## Sixth agent (2026-11-12): the T-g review applied, landing; LeaseKeepAlive's `WithTimeout` blocked

81's decisions on the T-g review (READY WITH CHANGES; questions.md): done in `7e10aa6b66` (M1: the
`RenewHTTP` axiom-tok reason restated, the freeze T-f text and the docstring corrected,
`TestRenewHTTPErrTiming`'s pre-cancelled case: `Err()` called twice, a `*url.Error`; m1:
`TestRawStreamKey` over prometheus x otelgrpc x Serve/ServeHTTP, the xDS line in `srvRawStreamIs`;
m3: `Tracer.Start`'s entry; m2 noted in the freeze note for a later cleanup). Merged lean
(`4b4eabaf38`, then notes-only lean again), full build green (build 20261112-230131), the trust-base
baselines updated for the four reached axioms (`a4ef7d7c82`: tcb 867 axioms/4 sorries, 16 collections),
gen-interface --check and axiom-tok ok. `etc/land.sh` FAILED at one gate, bounds (`spec-thread`: the new
`threadBound` premises of `newCancellableContext`, `newStreamInterceptor`, `Server`, `Serve`,
`serveClient`, `sendLoop`'s `5 ≤`); every other gate passed. `e272c4f217` adds `etc/bounds-allow.txt`
entries on the etcd3/Watch precedent (baseline 331 -> 330), NOT landed: for 81. Next: rerun
`etc/land.sh` once 81 accepts (GOWORK unset, LAKE_PACKAGES, PERENNIAL_CHECKOUT).

**LeaseKeepAlive, found before writing Lean** (reported to 81): `LeaseRenew`'s
`context.WithTimeout(ctx1)` over a weak `ctx1` cannot be a small local lemma. go1.27.3
`propagateCancel` (`context.go:476-528`), on a parent already done, calls
`child.cancel(false, parent.Err(), Cause(parent))`: the child `*timerCtx` stores the parent's
`Err()`, which for etcd's wrapper is `ErrGRPCNoLeader` once the monitor cancelled it. Perennial's
`*cancelCtx` model fixes the stored error to `isTypedErr ∧ isCtxErr` (`cancelCtxInv`'s `Herr`,
`childCancelSpec`, `cancelCtx.cancel.spec`, `timerCtx.cancel.spec`; about 45 uses in 12 files of
`Perennial/Proof/context`), and `srvCtxWeak`'s `#HErrDone` gives no `isTypedErr`. So the child
`cctx` is not an `isContext`, and a `srvCtxWeak cctx` needs a cancelCtx model over a general error
predicate (the "natural form" of `notes/perennial-changes.md`, P-RL2). `LeaseRenew`'s switch
default (log "Unexpected lease renew context error", `ErrCanceled`) becomes reachable too.
Options in the report; nothing written for them.

## Fifth agent, continued (2026-11-12): T-g decided; item 7 and the Watch chain done (lean-checked)

81 decided Q1/Q2/Q3 (questions.md). Done since (each lean-checked `-a`, 0 errors):
- Addendum T-g in Lean and in `notes/k8s-7f4-freeze.md`: `rawStreamKey si` (a pointer value);
  `SpanFromContext.spec` and mvcc's `WatchStream.Watch.contract` take `⌜todo⌝ ∨ spanCtxOk`; Go tests
  `TestRawStreamKey` (data word) and `TestSpanFromContextValueOnly` pass.
- `newStreamInterceptor` proved against `srvStreamInterceptorWOk` with its require-leader branch
  (`v3rpc.wrapper_rawW`, `v3rpc.streamKeysOk_insert/_delete`; smap's pointer persisted inside the WP);
  spec pre gains `⌜threadBound GF ≤ 2^30⌝`; linked (5 new callees).
- `Server.spec` takes `threadBound GF ≤ 2^30 →` and gives `srvStreamInterceptorWOk is True`;
  `Serve.spec`'s pure premise gains `threadBound GF ≤ 2^28` (the ten Mains pass `Htb`).
- Watch chain: `Watch.spec` takes/returns `levelTok v3rpc.ctxErrLvl`, `5 ≤ threadBound`; the recv
  goroutine and `sendLoop` lend level 4 from their thread token (`threadTok_lend4`,
  `SrvCtxWeakLaws.lean`); `ErrGRPCNoLeader` after `Done` through `errors.IsStatusErr.spec`
  (`v3rpc.statusErrOk_of_noLeaderErr`); recvLoop uses `Tracer.Start`'s weak arm; `AuthInfoFromCtx.spec`
  takes `txnCtx ∨ srvCtxWeak`, `isReqAuth_ctxM` takes `auth.ctxDoneAny`.
- Lease keep-alive specs temporarily on `srvStreamIsStrong` (old text, nothing produces it) until
  LeaseKeepAlive is re-proved (after the checkpoint).
- Results (`etcd_watchMethodOk`, `etcd_watch_served(_chain/_etcd_chain)`, `srvStreamBundle_watchSlot`)
  over `ics ++ [icW]` and level 4 in the handler's share.

Full build green (`etc/timed-build.py`, build 20261112-210835). Gates: axiom-tok ok (T-f' entries
added) and its selftest ok; model-param ok; errdesc ok; gen-interface regenerated (mvcc's
`WatchStream.Watch.contract`, etcdstart's `grpcUp*`/`Serve.spec`); tcb-report and 16 collections differ
only by axioms now reached (B1's two `incomingOf` axioms everywhere, `errors.IsStatusErr` in v3rpc,
`metadata.FromIncomingContext` in watch): baselines NOT updated, for 81. CHECKPOINT reported.
Next (after 81): update baselines; LeaseKeepAlive (LeaseRenew over the weak context, the local
`WithTimeout` lemma, drop `srvStreamIsStrong`); step 6 is a hard stop.
Build: `flock /shared/tmp/etcd-grove-build.lock systemd-run --scope -q -p MemoryMax=64G python3
etc/timed-build.py --packages=/shared/tmp/manifest-ddc.json`; gates script `/shared/tmp/k8s7f4/gates/run.sh`.

## Fifth agent (2026-11-12): item 7 started; STOPPED for two trust-base questions (81)

Done (lean-checked `-a`, 0 errors; NOT in a build; the importers of `srvStreamIs` are broken until
the Watch chain is re-proved):
- `InvGrpcStream.lean`: imports `v3rpc/SrvCtxWeak` (no move: its imports reach no grpc module;
  trusted text untouched); a section variable `context.Assumptions` in the second `defs` section;
  `srvRawStreamIsW` (RecvMsg/SendMsg/Context clauses, `srvCtxWeak ci cd ∗ libCtxOk ci ∗
  spanCtxOk ci`), `srvRawStreamIsW_of_raw`; `srvStreamIs`'s context part the weak one;
  `srvStreamIs_of_raw` over `srvRawStreamIsW`; `srvStreamInterceptorWOk ic R` (strong raw end in,
  the handler on a weak end at `ci'` with `incomingOf ci' = incomingOf ci`); the chain lemma
  `srvStreamChainWP_of_okW` for `ics ++ [icW]` (resources `[∗list] Rs ++ [RW]`).
- `_Watch_Watch_Handler.spec` on `srvRawStreamIsW` (its proof unchanged, checks).

Blockers found (reported to 81, see questions.md):
1. T-c gives `rawStreamKeyTy si.ty` (a pointer type) but not `si.v = #ls`; `v3rpc.sKey t ls l` and
   `safeMapKey_sKey` need the raw stream as `interface.mkOk (PointerType t) #ls`. The interceptor's
   insert cannot be proved without strengthening T-c (trusted).
2. `trace.SpanFromContext.spec` (axiom) takes `isContext ctx cd ∗ spanCtxOk ctx`; mvcc's
   `watchStream.Watch` calls it on the traced weak context (recvLoop, W5). Go reads only
   `ctx.Value(currentSpanKey)`.

Next once decided: the interceptor's W proof (`handler_tail` on `srvRawStreamIsW_of_raw`; the
branch: `FromIncomingContext` real spec from `libCtxOk_of_runCtx`'s `incomingCtxOk`, `Leader`,
`newCancellableContext`, the `serverStreamWithCtx` literal, insert under `smap.mu` with
`attribute [local instance 1100] v3rpc.streamKeys`, the defer's delete and `Cancel(nil)`, the
handler on `sKey` with `srvCtxWeak_cc`, `wrapperLibCtx`, `incomingOf_wrapper`); then the handlers'
`Err` level tokens (Watch main thread from `S`, the recv goroutine from `Ht4`, sendLoop from its
`threadTok`, LeaseKeepAlive/leaseKeepAlive), mvcc's contract, Results.

## Handoff point (2026-11-12, end of the fourth agent's context): items 1-6 done; item 7 next

Done (each lean-checked `-a`; items 1-5 in a full build, `95c4778916`; item 6 in the build of the
commit that adds this section):
1. `newCancellableContext` (`Spec/`+`Proof/.../v3rpc/newCancellableContext.lean`): pre `isPkgInit v3rpc
   ∗ isContext parent cd ∗ ⌜threadBound GF ≤ 2^30⌝` (the pure premise, as `GetProgressReportInterval`'s);
   post `ccHandle l (cancelCtx c) {cd with PDone := True, Done_gn := γ'} ∗ ctxValueFrom parent c1 ∗
   ctxField c ↦□ parent`. `e` (the no-leader error) from `interceptorVars`.
2. `cancellableContext.Cancel`: `ccHandle ∗ (⌜reason = nil⌝ ∨ noLeaderErr reason)` → `ContextClosed cd.Done_gn`.
3. `cancellableContext.Err`: `ccHandle ∗ levelTok ctxErrLvl ∗ (if b then ContextClosed else True)` →
   token back ∗ `(if b then ⌜err ≠ nil⌝ ∗ (isCtxErr err ∨ noLeaderErr err) else True)`.
4. `v3rpc.srvCtxWeak_cc` (`CancellableLaws.lean`, takes `Err.spec` as a hypothesis): `isPkgInit v3rpc ∗
   ccHandle l c1 cd ⊢ srvCtxWeak (ccCtx l) cd` (parentCancelCtx re-proved from its code).
   The three functions are linked (`etc/link-lean-first-v3rpc.txt`). The context assumptions come from
   `v3rpc.Assumptions` (`import_context_Assumption`): no separate `context.Assumptions` variable.
5. The stream adapter lends level 4: `grpcStreamRunOk_of_pools` bundle `levelTok 0 ∗ levelTok 4 ∗ R₁ ∗
   R₂ ∗ R₃`, `5 ≤ threadBound`; `RunAdapt.srvStreamBundle` (stream runs; unary keep `srvRunBundle`);
   `srvLevelK := srvRevokeK + 1` (5); `srvLevels_iff` replaced by `srvRevokeLevels_of_srvLevels`;
   `srvRevokeLevels_of_max` takes `max m srvLevelK`; leaseexpiry's `Main.spec` takes `srvLevels` (was
   `srvRevokeLevels`); `etcd_watch_served`'s `h1`/`h2` and `srvStreamBundle_watchSlot` at the stream bundle.
6. The monitor's map: `InvStreamInterceptor.v3rpc.streamsMapInv` holds `mp ↦$ m` (under the local
   instance `v3rpc.streamKeys`) with `[∗map] k ↦ _u ∈ m, v3rpc.streamKeyOk k` (`k = sKey t ls l ∗
   ccHandle l c1 cd`); `StreamMapKey.lean` no longer imports `InvStreamInterceptor` (the reverse now);
   `monitorLeader`'s range body proved (`Cancel(ErrGRPCNoLeader)`, `<-ss.Context().Done()` through the
   promoted `Done`), `monitorLeader` takes `Cancel.spec` (linked).

**Next: item 7** (the weakening contract, the weak stream end, the interceptor's branch), then step 5.
Design point to settle first (scratch: `/shared/tmp/k8s7f4/item7-design.md`): grpc's `srvRawStreamIs` is
trusted (prometheus's axiom, grpc's model), so do not parametrize it; `srvStreamIs`,
`grpcStreamHandlerOk`, `srvStreamIs_of_raw` and `_Watch_Watch_Handler.spec` are not trusted (the
`GenericServerStream` axioms speak only of the raw end's method values). Two options: (a) in grpc's
`InvGrpcStream`, a non-trusted weak raw end `srvRawStreamIsW` (the RecvMsg/SendMsg/Context clauses, the
context part `srvCtxWeak ci cd ∗ libCtxOk ci ∗ spanCtxOk ci`) with `srvRawStreamIs ⊢ srvRawStreamIsW`,
and `srvStreamIs`/`grpcStreamHandlerOk`/`_Watch_Watch_Handler.spec` over the weak end (needs
`srvCtxWeak` in a module grpc can import: it lives in `v3rpc/SrvCtxWeak.lean` now, whose imports are
Perennial's context, rpctypes and `auth/CtxDone`); (b) etcd-side weak definitions in v3rpc, but
etcdserverpb's handler spec would then import v3rpc (layering). (a) looks right; moving `srvCtxWeak` is a
trusted-text move (form only), list it. Then `srvStreamInterceptorWOk ic R` (strong raw end in; the
handler on a weak end with `⌜incomingOf ci' = incomingOf ci⌝`, or an early `srvErrOk` error), the chain
lemma for `ics ++ [icW]`, `newStreamInterceptor.spec`'s post `srvStreamInterceptorWOk ic True`: its
branch is `FromIncomingContext` (premise kept until step 6), `newCancellableContext(ss.Context())` (needs
`threadBound ≤ 2^30` in `newStreamInterceptor.spec`'s pre), the wrapper's raw end from `ss`'s by the
promoted `serverStreamWithCtx.{RecvMsg,SendMsg}` and its `Context` (`ccCtx l`, `srvCtxWeak_cc`,
`wrapperLibCtx`, `incomingOf_wrapper`), the insert under `smap.mu` (`streamKeyOk`, `safeMapKey_sKey`;
`attribute [local instance 1100] v3rpc.streamKeys`), the `defer`'s delete and `Cancel(nil)`.
Results' `etcd_watch_served_chain` breaks until step 5 re-proves the handlers over the weak end: do item 7
and step 5's handler part before the next full build. Gates not yet run at this point: axiom-tok
(+selftest), the collections, gen-interface, model-param, errdesc.

## Handoff point (2026-11-12, end of the third agent's context): T-f' approved; the handle started

T-f' approved by 81 (level 4 accepted). Gates still owed with the next landing: axiom-tok (+selftest),
the 55 collections, gen-interface on the six lists, model-param, errdesc.

Done since (lean-checked `-a`, 0 errors; not yet in a full build):
- `Proof/.../v3rpc/InvCancellable.lean`: `v3rpc.ccLockF`/`ccCancelF`/`ccReasonF`, `v3rpc.ccPoolN`,
  `v3rpc.reasonOk e r` (`nil` or `e`), `v3rpc.ccReasonP l e q` (fractional, timeless:
  `fractional_exists_agree` over the subtype of good reasons), `v3rpc.ccHandle l c1 cd`
  (persistent; fields `↦□`, `isContext c1 cd`, `isCancelCtxOf c γ True`, `cancelSpec`, `noLeaderErr`,
  the writer guard `isRWMutexGuard`, the reader pool `isThreadPoolL ccPoolN ctxErrLvl`).
- `v3rpc.wp_WithCancel_cancelCtx` (`WrapperMd.lean`) also returns `isCancelCtxOf c γ' True`.

**Next, in order** (each Go function a `Spec/.../v3rpc/<fn>.lean` + `Proof/.../v3rpc/<fn>.lean`, linked
through `etc/link-lean-first-v3rpc.txt` and `etc/gen-link.py --v3rpc`-style regeneration; check
`etc/gen-link.py`'s flag for v3rpc):
1. `newCancellableContext.spec`: `{{ isPkgInit v3rpc ∗ isContext parent cd }} → (l : Loc), ∃ γ',
   ccHandle l c1 {cd with PDone := True, Done_gn := γ'} ∗ ctxValueFrom parent c1 ∗ ctxField c ↦□
   parent }}` (c1 the `*cancelCtx`). Proof: `v3rpc.wp_WithCancel_cancelCtx`; the struct alloc gives
   the fields (persist `Context`, `cancel`); `sync.init_RWMutex_threadPoolL (ccReasonP l e) ccPoolN 4
   (ccLockF l) Hb` with `Hb : threadBound GF ≤ 2^30` (find where the server's proofs get it:
   `grep -rn 'threadBound GF ≤ 2 ^ 30'`); `e` from `interceptorVars`' `errVarSet ErrGRPCNoLeader`.
2. `cancellableContext.Cancel.spec`: `ccHandle l c1 cd ∗ ⌜reasonOk e reason⌝` (state it as `reason =
   nil ∨ noLeaderErr reason`, and get `= e` by the global's agreement) → `ContextClosed cd.Done_gn`.
   Lock via `sync.RWMutex.wp_Lock_guard` (no token), store, `wp_Unlock_guard`, then `cancelSpec`.
3. `cancellableContext.Err.spec`: `ccHandle ∗ levelTok 4` → `err`, token back, and after
   `ContextClosed`: non-nil, `isCtxErr ∨ noLeaderErr`. Template: `lease/Lease__Remaining.lean`
   (`threadPool.borrowL`, `wp_RLock`, defer `wp_RUnlock`, `giveBackL`). `c1.Err()` through
   `isContext`'s `#HErr`/`#HErrDone` (wp_method_call on `*cancellableContext`'s promoted path is not
   needed: `Err` is declared; `Context.Err()` is a `MethodResolve` on the loaded field).
4. `v3rpc.srvCtxWeak_cc : ccHandle l c1 cd ⊢ srvCtxWeak (ccCtx l) cd` (plus the `Err` triple as a
   hypothesis): Deadline/Done/Value promoted (`rw [method_unfold (t := ptr cancellableContext)]`,
   as `v3rpc.valueAt_cc`) to `c1`'s `isContext` clauses; `#HDoneFresh`, `#HClosedchan` are `c1`'s;
   `#HParentCC`: `parentCancelCtx(l)` re-proved from its code as Perennial's
   `wp_parentCancelCtx_self_of` (`CancelCtxContext.lean:40`), the wrapper's `Done`/`Value` stepping
   to `c1`'s (`cancelCtx.wp_Done`, `cancelCtx.wp_Value`, `wp_done_Load_known`); `c.ty ≠ stopCtx.ty`
   by `decide`/`simp`.
5. Hand `levelTok 4` to the stream handler: `grpcStreamRunOk_of_pools` (`InvGrpcRun.lean:310`)
   splits `threadTokFrom 4 ⊣⊢ levelTok 4 ∗ threadTokFrom 5` (`threadTokFrom_succ`, `5 ≤ threadBound`)
   and the bundle becomes `levelTok 0 ∗ levelTok 4 ∗ R₁ ∗ R₂ ∗ R₃` (or `levelTok 4` inside `S`):
   follow its users (`etc/importers.py --uses grpcStreamRunOk_of_pools ... --files`).
6. `streamsMapInv` over `v3rpc.streamKeys` (`attribute [local instance 1100] v3rpc.streamKeys`):
   `[∗map] k ↦ _ ∈ m, ∃ t ls l c1 cd, ⌜k = sKey t ls l⌝ ∗ ccHandle l c1 cd`; `monitorLeader`'s range
   body (`ss.(serverStreamWithCtx)`, `Cancel(ErrGRPCNoLeader)`, `<-ss.Context().Done()`:
   `serverStreamWithCtx.Context` then the promoted `Done`, received with `isContextDone`).
7. The weakening contract `srvStreamInterceptorWOk` and the weak stream end, the interceptor's
   branch (`newCancellableContext`, the map insert under `smap.mu`, the `defer`'s delete and
   `Cancel(nil)`), then step 5 (mvcc checkpoint) and step 6 (hard stop).

## Addendum T-f' written (2026-11-12): STOPPED for 81's review

81 decided option (A) with a level token. `829eb68b92`: `v3rpc.ctxErrLvl := 4` and `srvCtxWeak`'s
`"#HErr"`/`"#HErrDone"` take and return `levelTok v3rpc.ctxErrLvl`; T-f' sentences in the
docstrings of `waitLeader`, `RenewHTTP`, `Tracer.Start`; `notes/k8s-7f4-freeze.md` "Addendum T-f'"
(the level's choice, the Go reasoning, checks). Full build passes, tcb --check matches, goose --check
passes. **Next after the review:** the wrapper's handle (the plan below), handing `levelTok 4` to
the stream handler in `grpcStreamRunOk_of_pools` (`threadTokFrom 4 ⊣⊢ levelTok 4 ∗ threadTokFrom
5`, `5 ≤ threadBound`), the wrapper's `RWMutex` reader tokens in `init_RWMutex_threadPoolL _ 4`.

## Steps 3-4, third agent (2026-11-12): STOPPED at a blocker in step 4 (for etcd-grove-81)

Done (lean-checked, `etc/lean-check.py -a`, 0 errors; a targeted `lake build` of `SrvCtxWeakLaws`):
- `8227d410c2` step 3. `Proof/.../v3rpc/SrvCtxWeakLaws.lean`: R-4's `v3rpc.srvErrOk_of_weakErr`
  (`isPkgInit v3rpc ∗ isPkgInit etcdserver ⊢ □ ∀ err, (isCtxErr err ∨ noLeaderErr err) -∗ srvErrOk
  err`); `v3rpc.valueAt_cc`, `v3rpc.libCtxOk_cc`, `v3rpc.spanCtxOk_cc` (the wrapper's promoted
  `Value`); `v3rpc.wrapperLibCtx` (from `ccField l ↦□ c`, `ctxValueFrom ci c`, `libCtxOkC ci`,
  `spanCtxOkC ci`: `libCtxOk (ccCtx l) ∗ trace.spanCtxOk (ccCtx l)`).
  **Goose configuration** (`Code/.../api/v3rpc.toml`, regenerated with `etc/goose.py --project etcd`):
  the promoted methods `cancellableContext.{Deadline,Done,Value}` and
  `serverStreamWithCtx.{RecvMsg,SendMsg}` were not translated (goose emits a promoted method's
  `MethodUnfold` only when the method is listed, as `quotaKVServer.Compact`), so the wrapper's
  `Value` was uninterpreted. Now listed; the diff is only those `*_unfold` fields.
- `e6c1a31bcb` step 4's first item. `Proof/.../v3rpc/StreamMapKey.lean`: `v3rpc.sKey t ls l`,
  the local `MapKeys` instance `v3rpc.streamKeys` (use it as `attribute [local instance 1100]`
  in the files that own the monitor's map), `v3rpc.sKey_eq`, `v3rpc.safeMapKey_sKey`,
  `v3rpc.serverStreamWithCtx_intoVal_inj`.

**Blocker (a trusted-text question):** `srvCtxWeak`'s `"#HErr"`/`"#HErrDone"` give `Err()` with no
resource, but etcd's wrapper's `Err` (`interceptor.go:297-304`) takes `c.lock.RLock()`, and
Perennial's `RLock` (`sync.RWMutex.wp_RLock_of`) needs a reader token (`ownRWMutex rw P`; the
lock has `2^30 - 1`, the bound of Go's reader counter). A persistent `Err` triple with no resource
would need unboundedly many concurrent readers' tokens: it is not provable for the wrapper (rightly:
`notes/bounds-plan.md`, a reader pays with its `threadTok` through a thread pool,
`init_RWMutex_threadPool[L]`). So `srvCtxWeak (ccCtx l) cd` cannot be proved as landed. `Cancel`
(`Lock`, the guard) and `Done`/`Deadline`/`Value`/`parentCancelCtx` (promoted to the `*cancelCtx`
child) are not affected. Callers of the weak context's `Err`: `watchServer.Watch` (after `Done`),
`recvLoop` (`watch.go:203`, a forked goroutine), `leaseKeepAlive` (`lease.go:106,118,149`), and
through `Tracer.Start`'s child and the local `WithTimeout` lemma (`propagateCancel` calls
`parent.Err()` when the parent is done). Options in the report; nothing written for them yet.

**Next, once 81 decides:** the wrapper's handle (the `RWMutex` invariant `cancelReason ∈ {nil,
noLeaderErr}` with its reader tokens in a pool; `cancel ↦□` with `cancelSpec`; `ccField l ↦□ c1`;
`isContext c1`), `newCancellableContext`'s spec and proof (extend `v3rpc.wp_WithCancel_cancelCtx`
to keep `isCancelCtxOf c γ True`, needed for the wrapper's `"#HParentCC"`: `parentCancelCtx(l)`
returns `c1`, re-proved from its code as Perennial's `wp_parentCancelCtx_self_of`), `Cancel`/`Err`,
`srvCtxWeak (ccCtx l)`, `streamsMapInv` over `v3rpc.streamKeys` (keys with the wrapper's handle),
`monitorLeader` (the range body: `Cancel(ErrGRPCNoLeader)`, `<-ss.Context().Done()`), the
weakening contract and the interceptor's branch (then steps 5-6 as below).

## Revision 2 and the landing (2026-11-12)

Re-review: B1, T-e' and the gates READY; the blocker (Tracer.Start's `spanCtxOk` did not exclude the
refutation) fixed by `trace.spanValOk` (freeze "Revision 2"); Revision 1's knock-on premises reverted.
**Landed: lean `2f8cf80b7e`** (2026-11-12, `etc/land.sh`, all gates). **Next: steps 3-6 of the
re-baseline's §4** (`notes/k8s-7f4-rebaseline.md`), on this branch (merge lean first):

3. `srvCtxWeak` laws exist (`SrvCtxWeak.lean`: `srvCtxWeak_of_isContext`, `ctxDoneAny_of_srvCtxWeak`);
   add R-4's lemma (`isCtxErr ∨ noLeaderErr` ⊢ `srvErrOk`: `applyErrIs_srvErrOk`,
   `watchServer__Watch.lean:392`; `SeNL` in `newStreamInterceptor.lean`), and the wrapper's library
   facts: from `srvRawStreamIs`'s `libCtxOkC ci`/`spanCtxOkC ci`, `v3rpc.wp_WithCancel_cancelCtx`'s
   `ctxValueFrom`, `context.libCtxOkC_from`/`trace.spanCtxOkC_from` give the `WithCancel` child's; the
   wrapper's `Value` is promoted (load `ccField l`, then the child's `Value`): prove its
   `libCtxOk`/`spanCtxOk` (WP form) via `libCtxOk_of_libCtxOkC`-style reasoning over the promoted
   method (needs `isPkgInit context`).
4. The interceptor's require-leader branch and `monitorLeader` (the `sKey` map-key instance first,
   `notes/k8s-7f4-mapkey-check.lean.txt`): the weakening contract `srvStreamInterceptorWOk`
   (freeze §2 "Not trusted"), the handler on a weak end with `⌜incomingOf ci' = incomingOf ci⌝` from
   `v3rpc.incomingOf_wrapper` (`newCancellableContext`'s proof must persist `ccField l ↦□` and use
   `v3rpc.wp_WithCancel_cancelCtx` for `ctxField c ↦□ ci`); the chain lemma for `ics ++ [icW]`;
   `grpcStreamHandlerOk` on the weak end. Using the two field axioms changes the baseline at step 6.
5. Watch's chain (mvcc's `WatchStream.Watch.contract`, Q-RB4: interface diff, **checkpoint for 81**),
   then LeaseKeepAlive with `LeaseRenew` over `srvCtxWeak` and the local `WithTimeout` lemma.
6. Delete `runsNoRequireLeader`; interfaces; `etc/tcb-report.py --check --update`. **Hard stop.**

## Revision 1 (2026-11-12, the second 7f-4 agent): steps 1-6 of 81's decisions done

`notes/k8s-7f4-freeze.md`, "Revision 1", per finding. B1 by per-constructor preservation (option (b);
(a) spread into auth): axioms `metadata.incomingOf_cancelCtx` (`Incoming.lean`) and
`v3rpc.incomingOf_cancellableContext` (new `v3rpc/WrapperMd.lean`, with the proved
`v3rpc.incomingOf_wrapper` and `v3rpc.wp_WithCancel_cancelCtx`). T-e' built; `Tracer.Start` takes
`trace.spanCtxOk` (Range/LeaseRenew specs and `raftLeaseRenew` gain it); `libCtxOkC` gains otel's key,
laws `libCtxOk_of_libCtxOkC`, `spanCtxOk_of_spanCtxOkC`, `*_from`; minors. **Done (2026-11-12): 81 accepted (b), the extra forms, and `spanCtxOk` on `range_linearizable`/
`range_serializable`; full build passes; tcb --check matches (865/5); 55 collections match;
axiom-tok ok with ten new rule-7 entries for T-e' (for the review); selftest, model-param, errdesc,
gen-interface ok; m4 listed in the freeze note. STOPPED for 81's re-review.** Then
steps 3-6 of the re-baseline's §4 (the weakening interceptor contract uses
`v3rpc.incomingOf_wrapper`; `newCancellableContext`'s proof must persist the `Context` field's
points-to and call `v3rpc.wp_WithCancel_cancelCtx`).

## 81's decisions on the review, 2026-11-12 (steps 1-6 done in Revision 1, above)

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
