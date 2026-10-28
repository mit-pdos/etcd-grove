# M2 spec skeleton, review round 1 (phase 1b)

Reviewer: fresh `spec-reviewer` agent, 2026-10-28. Worktree `/shared/etcd-grove-cp`, branch `m2`.
Commit under review `51387263cb`; `HEAD` is the same commit, so nothing below is stale except one
item from the S2-S4 fork's list (marked). Rubric: `notes/spec-first-plan.md`, "Phase 1b" (same as
the agent file's; the agent file on this branch adds "a contract checked only against an unproved
spec", applied here). Go checked at the extracted copy
`.lake/spec-test/v3compactor-964dccdb42…/server` (`964dccdb4`); the pin `a20f6760f` differs from it
only in `server/auth/store.go` (`git diff --stat` in `.lake/go-src/etcd`), so the code read is the
pinned code. Nothing was built; `etc/tcb-report.py` was not run (it needs an up-to-date build).

Callers: the brief listed them; I also searched for `Compact.spec`, `compactOk`, `ctxTraceIs`,
`reqPropOkC`, `dispatchOkC`, `irrNoDelPut`, `compactRight`, `crevFrozen` across `Proof/` and `Spec/`.

## Summary of tier-1 findings

1. **The compaction mode exists in no statement** (S2, S3, S4). `reqPropOkC`, `irrNoDelPut` and
   `apply.dispatchOkC` are defined and used nowhere; every compaction statement takes the
   compaction-off server view `isServerReq`, whose KV invariant forbids a compaction entry in the
   committed log. `processInternalRaftRequestOnce.specCompact` is unprovable as stated, and with it
   `Compact.spec` and `NewServer.specCompact`. The delete-then-put premise (decision (a)) is placed
   nowhere, and `NewServer.specCompact` still hands out the watch readers.
2. **`specCompact`'s success post owns the apply thread's trace twice** (`apply.resTrace res ∗
   compactResultIs res`): unsatisfiable on the code's normal success path.
3. **`store.Compact.spec` (the arm's callee) excludes future revisions** that `specCompact` and
   `Compact.spec` admit ("any revision"), although the Go code answers them with `ErrFutureRev`.
4. **The planned glue for the compactor's environment is missing**: `NewServer.wp_proofCompact` is a
   bare `sorry` with no callee hypotheses, so `Compact.spec` was not checked against its main
   caller (the compactor's `compactableOk`), and the `m2` trust collection cannot see
   `Compact.wp_proof`/`specCompact` at all.

---

## S2: `CompactMode.lean` and `processInternalRaftRequestOnce.specCompact`

### Keep
- `compactPropOk`/`irrCompaction`/`compactPropOk_irrCompaction` (`CompactMode.lean:40-48`): small,
  pure, and they let the `Compact` glue state the request without unfolding apply's model.
- The idea of `compactResultIs` (`CompactMode.lean:91`): the post carries what `Compact` inspects
  (`result.Trace`, `result.Err`, the response's header). This avoids the "post that ignores the
  result" pattern.
- The decision to keep the compaction variants apart until they are proved, so that their `sorry`s
  stay out of the compaction-off results (`notes/m2-plan.md`, S0 "Why a variant").

### Findings

**S2-1 (tier 1: true / sufficient; the main finding). `specCompact` takes `isServerReq`, whose
invariant excludes compaction entries, so it is unprovable as stated.**
`Spec/.../EtcdServer__processInternalRaftRequestOnce.lean:108` takes `isServerReq s E ρ`.
`isServerReq` (`InvProposer.lean:428`) contains `kvInv ρ.raft ρ.kv` (`srvReqFieldsAt`), and `kvInv`
(`InvRequest.lean:229-233`) keeps `plainLog L` and `kvWork` (`logShape L`) of every committed
entry. `plainEntry` (`KVModelDefs.lean:141`) requires `plainReq rq`, whose `plainCover`
(`KVModelDefs.lean:72-81`) is `False` for a compaction. `logShape`'s `rqShape` requires
`∀ on, apply.dispatchOk on rq` (`WorkloadDefs.lean:259`), and `dispatchOk` excludes
`.compaction` (`apply/InvUber.lean:63`). The proposal's update ("which every update the server hands
raft checks of its entry", `kvInv`'s docstring) cannot commit a compaction entry under this
invariant. The Go code does commit one (`v3_server.go:392`) and the post's success case needs its
applied result. Nothing in the repository uses `reqPropOkC`, `irrNoDelPut` or `apply.dispatchOkC`
(grep: only `CompactMode.lean` itself). The apply side's specs still require `dispatchOk`
(`apply/ApplyKVL.lean:61`, `apply/DispatchKVL.lean:167`), so no apply statement can apply the
entry either. S2's plan items ("`dispatchOk` loses the compaction conjunct", "the arm's spec",
"`reqPropOk`'s compaction form") exist only as unused definitions.
*Affects:* `Compact.spec` (its glue calls `specCompact`), `NewServer.specCompact` (its run loop must
apply what the compactor proposes), `putgetc_safe`.
*Restatement:* a compaction mode in the server's request-path view, as auth's `on`. Either
`isServerReqM` takes a mode record `{auth : Bool, cmp : Bool}`, or there is a separate
`isServerReqC`. Its KV invariant keeps `logShapeC` (an `entryShapeC` whose `rqShapeC` is
`dispatchOkC ∧ (a write → irrNoDelPut)`, admitting `compactPropOk`), and its proposal permit is
`reqPropOkC`. `specCompact` takes `isServerReqC`, and so do `Compact.spec` and the compaction-mode
variants of the write paths (`Put`/`DeleteRange`/`Txn`, which take `reqPropOkC`). The apply specs
over `dispatchOkC` are the S2 arm's.

**S2-2 (tier 1: true). `specCompact`'s success post asks for two exclusive ownerships of the same
trace.** `EtcdServer__processInternalRaftRequestOnce.lean:114`: `apply.resTrace res ∗
compactResultIs res`. `resTrace res` (`apply/InvUber.lean:288`) is `res = null ∨ ∃ v, res ↦□ v ∗
(v.Err' ≠ nil ∨ traceRes v.Trace')`. `compactResultIs` (`CompactMode.lean:91`) has `res ≠ null`,
`res ↦□ v` and `apply.traceRes v.Trace'` again. On success `res ≠ null` and `v.Err' = nil`, so both
conjuncts need `traceRes v.Trace'` of the same `v`, by agreement of `↦□`. On the Go success path
the trace is never null: `applierV3backend.Compaction` returns the trace that
`traceutil.EnsureTrace(context.TODO(), …)` made (`apply/backend.go:69,80`). `traceRes t` for
`t ≠ null` is `ownTrace t e ⊢ t ↦ v` (`traceutil/Defs.lean:54-58`), and two of them are `False`. So
the post is unsatisfiable exactly when the code succeeds. The `Compact` glue discards the
`resTrace` conjunct (`EtcdServer__Compact.lean`, `icases Hres with (⟨%Herr, -, Hcr⟩ | …)`), so no
caller needs it.
*Restatement:* drop `apply.resTrace res` from `specCompact`'s success disjunct, so that
`compactResultIs` alone carries the trace.

**S2-3 (tier 1: true / no unneeded premise, at the arm's callee). Future revisions.** `specCompact`
(`compactPropOk`: any `r`) and `Compact.spec` ("at any revision (a future one is the apply's
`ErrFutureRev`)") admit `r` beyond the log. The arm's callee `mvcc.store.Compact.spec`
(`Spec/.../mvcc/store__Compact.lean:65`) requires `sint.Z rev < log.length ∧ NoDelPutAt log rev`,
which makes its own `ErrFutureRev` post disjunct dead. The Go code is safe for a future revision:
`updateCompactRev` returns `ErrFutureRev` (`kvstore.go`), and the applier returns it with a nil
trace (`apply/backend.go:73-75`). So the apply arm cannot discharge `specCompact` for
`r ≥ log.length`.
*Restatement* (one of): (i) `store.Compact.spec` takes `sint.Z rev < log.length → NoDelPutAt log
(sint.Z rev)`, where the sole writer holds the exact log; or (ii) the compaction form of the permit
bounds `r` by a revision the store has reached (`revLb γ.idx r`), which the revision compactor's
`revPermit` already gives (`□ RevLb (r + ret)`). That would also make `Compact.spec` take that
bound, and the plan rejected a per-call permit (round 3), so (i) is the better choice. Whether the
mvcc proof of (i) is a small change is **uncertain** (`store.Compact` is proved, 157 lines).

**S2-4 (tier 1: no unneeded premise / sufficiency; placement of decision (a)).** `irrNoDelPut`
(`CompactMode.lean:54`) is a semantic premise: it quantifies over every chain, every log and every
outcome of `dispatchStep`. It is stated of `rq`, the request before the header is stamped and
before the wire encoding. The apply dispatches `rq'` with `irrWireOf (withHeader rq hm) rq'`, which
can change a range end (`[0]`) and so which keys a `DeleteRange` deletes. A lemma
`irrNoDelPut_wire` is therefore needed, and it is not obviously true for range deletes. **Uncertain**
whether it holds as stated; to settle it, prove it, or restate the premise syntactically.
*Restatement:* a decidable, syntactic premise on the request: no `Txn` branch has a delete whose
range can contain a key that a later put of the same branch writes. Prove `irrNoDelPut` from it,
for `Put`, `DeleteRange` and `LeaseRevoke` by one lemma each. Callers can meet the syntactic form:
`putgetc` issues single puts.

**S2-5 (tier 2: the docstring is false of the code, the predicate is true).** `compactResultIs`'s
docstring and the brief claim that the applier "returns the compaction's trace with its error". In
Go it does not: on error `applierV3backend.Compaction` returns `nil, ch, nil, err`
(`apply/backend.go:73-75`; `applierV3Corrupt` returns `nil, nil, nil, ErrCorrupt`,
`apply/corrupt.go:45-47`), and the uber-applier copies the nil trace into `ar.Trace`
(`uber_applier.go:145`). `traceRes null` holds, so the predicate is true. Only the prose is wrong.
*Fix:* "its trace, nil on an error".

**S2-6 (tier 2: layout/coupling).** `apply.dispatchOkC` is declared in the `apply` namespace but in
an `etcdserver` file (`CompactMode.lean:61`). It belongs beside `dispatchOk` in
`apply/InvUber.lean`, or it should be removed, since nothing uses it. `compactPropOk` repeats
itself (`dispatchKind = .compaction` already implies the field is set); this is minor.

**S2-7 (tier 2: special-case family).** `specCompact` is a third family beside `spec` and
`specM on`. LESSONS (2026-10-27, `isStaticCluster`) asks for the general statement. The plan
records the reason (TCB isolation until proved) and the merge. The merge needs the mode parameter
of S2-1, not `0 ≤ retention` alone.

### Metrics
- Scope premises: `compactPropOk` (the request kind, not a scope restriction); `irrNoDelPut` cites
  `issues/etcd-compaction-delete-then-put.md` and decision 3/(a), but no statement uses it.
- Caller burden: the only caller (`Compact`'s glue) unfolds `compactResultIs` (its own package),
  `apply.traceRes` (apply's: `iunfold apply.traceRes at Htrr`), and, through `simp only`, apply's
  `irrEmpty`, `optReqIs`, `presentIs`, `irrField`, `compactionIs` (to build `irrNoHdrIs` of
  `irrCompaction`). Missing laws: `apply.traceRes_cases` (null or owned), and
  `irrNoHdrIs_compaction : (the IRR's fields, compaction p) ⊢ irrNoHdrIs p (irrCompaction r)`.
- Law coverage: `compactResultIs` has no persistence split; that is fine, it is consumed once.
- Trust exposure: `specCompact`'s proof is a `sorry` (`EtcdServer__processInternalRaftRequestOnce.lean`
  proof file, line 702).
- Testability: `compactPropOk` is decidable; `irrNoDelPut` is not as stated (S2-4).
- Strength margin: on success the code guarantees a non-null response with a non-null header and a
  non-null trace (`backend.go:67-80`). The post allows nulls, which is fine because `Compact`
  handles them.

---

## S3: `EtcdServer.Compact.spec`/`specOn`, `v3compactor.compactableOk`/`isPeriodic`/`isRevision`, `traceutil/CtxLaws.lean`

### Keep
- The freeze repair is the right shape: a per-call `traceutil.ctxTraceIs ctx none` in
  `compactableOk` (`v3compactor/Defs.lean:133-139`) and in `Compact.spec`. It is established once
  per compactor object (`isRevision`/`isPeriodic`, `Defs.lean:256,292`) from
  `wp_WithCancelBackground_noTrace` (`CtxLaws.lean`), and `Tracer.Start` preserves it (its spec's
  `∀ o, ctxTraceIs ctx o -∗ ctxTraceIs ctx1 o`, used at `EtcdServer__Compact.lean`, `hStart`). Go
  check: `EnsureTrace` reads `ctx.Value(TraceKey{})` (`pkg/traceutil/trace.go:95`). The only
  writer of `TraceKey` is `EnsureTrace` (`trace.go:109`; grep of the tree). OpenTelemetry's
  `Tracer.Start` wraps the context with `WithValue` for its own key, so `Value(TraceKey{})`
  delegates. The premise is true of the compactor's context and of a gRPC handler's context.
- The added reader slots (`srvLgReader`, `isServerRead`) match `Compact`'s body: `s.Logger()` takes
  `lgMu`, and `s.kv.Rev()` reads the store (`v3_server.go:391,429`). Before the fork, the
  statement lacked them.
- The `Trace.AddField` callee hypothesis is present (`EtcdServer__Compact.lean`, `hAddField`), and
  `Link.lean:1616` links it. **Stale**: the fork's finding "`Compact`'s callee hypotheses lack
  `Trace.AddField`" is addressed in `51387263cb`.
- `compactOutIs` carries what the compactor tests (`errors.Is` on the error) and what a gRPC handler
  fills (the header).

### Findings

**S3-1 (tier 1: true; inherits S2-1).** `Compact.spec` (`EtcdServer__Compact.lean:54`) takes
`isServerReq` with no mode and is proved over `specCompact`, so S2-1 applies: it claims that
`Compact` is safe on a compaction-off server, whose clients may commit delete-then-put
transactions. *Restatement:* take the compaction-mode server view (S2-1).

**S3-2 (tier 1: mode variant without a route / tier 2: dead statement). `Compact.specOn` has no
proof route and no caller.** `EtcdServer__Compact.lean:63` (auth on, `isServerReqM true`). There is
no `processInternalRaftRequestOnce.specCompactM`, `NewServer.specCompact` fixes
`E.authOn = false` (`NewServer.lean:374`), and grep finds no proof or use of `Compact.specOn`.
*Restatement:* delete it, with a note that auth-on compaction is a later widening (phase 0's
decision 2), or keep it only together with the mode record of S2-1 (`auth = true, cmp = true`).

**S3-3 (tier 1: sufficiency for the main caller, unchecked).** The plan's list of "glue to prove
before the review" includes "`NewServer`'s construction of `E` and the `New` call (the compactor
case)". `NewServer.wp_proofCompact` is a bare `sorry` with no callee hypotheses
(`NewServer.lean:1951-1952`). So nothing checks that `compactableOk E.c P E.R` follows from
`Compact.spec`. Two gaps are visible without the glue:
(a) `compactableOk`'s post needs `errTreeOk err` (`Defs.lean:139`), while `Compact.spec` gives
`compactOutIs` (`err = nil` or `applyErrIs err`). Grep finds no law
`applyErrIs err ⊢ errTreeOk err` and no `⊢ errTreeOk nil`. NewServer's proof would have to unfold
apply's `applyErrIs` and v3compactor's `errTreeOk`, or the laws are missing.
(b) `E.R` must hold every exclusive resource of `Compact.spec`'s precondition: `srvLeadTimeReader`,
`srvLgReader`, `E.RD`, `storeReaderC`. The plan's `E.R` (`m2-plan.md`, S4) omits `srvLgReader`,
and whether `NewServer` has a spare slot of each for the compactor's goroutine is **uncertain**.
*Restatement:* give `NewServer.wp_proofCompact` its callee hypotheses now (`EtcdServer.Compact.spec`,
`v3compactor.New.spec`), prove the construction of `E` and of `compactableOk` (the bodies can stay
`sorry` elsewhere), and add `apply.applyErrIs_errTreeOk` and `v3compactor.errTreeOk_nil` (or
state `compactableOk`'s post over `applyErrIs`).

**S3-4 (tier 2: future caller, the gRPC handler).** `v3rpc.kvServer.Compact.spec`
(`Spec/.../v3rpc/kvServer__Compact.lean`) calls the server through the contract `v3rpc.compactOk`
(`v3rpc/InvAuthAdmin.lean:154`), which nothing discharges yet (grep), so the handler is not a caller
of `Compact.spec` today. When it is linked: `compactOk` and the handler's spec take `mvcc.txnCtx`
but not `ctxTraceIs ctx none`. The serving path has it (`ServerKV.lean:99`, `srvCall`'s
`traceutil.ctxTraceIs ci none`), so add it to `kvServer.Compact.spec`'s precondition, as the other
KV handlers do. It is sufficient there: the handler passes the same `ctx`, and `isPermitted`
writes no trace (`key.go:139-147`).

**S3-5 (tier 2: stale prose).** `Compact.spec`'s docstring says "`storeReader` would assert the
store is never compacted". Since S1, `storeReader := storeReaderC` (`InvStore.lean:3315`), so the
two readers are the same predicate. *Fix:* use `storeReader` for uniformity with the other server
specs, or drop the remark.

**S3-6 (tier 2: layout).** `v3compactor/newRevision.lean` and `newPeriodic.lean` (proof files) now
import `Proof.go_etcd_io.etcd.pkg.v3.traceutil.CtxLaws`, a `Proof` module of another package and
not a callee's `Spec` (CLAUDE.md, "Layout": a proof imports only its callees' `Spec` files). They
also lost the callee hypothesis `context.WithCancelBackground.spec`. *Restatement:* a `Spec` file
`Spec/.../traceutil/WithCancelBackgroundNoTrace.lean` (or a trust-boundary-free spec of
`context.WithCancel` from Perennial) as a callee hypothesis, linked to the CtxLaws lemma in
`Link.lean`.

### Metrics
- Scope premises: `compactReqIs` (non-physical: the pilot's scope, cited); `ctxTraceIs ctx none`
  (the freeze repair, cited in `notes/decisions.md`). Both are true of every known caller.
- Caller burden (`EtcdServer__Compact.lean`), cross-package unfolds:
  `iunfold mvcc.txnCtx` (mvcc; law: `mvcc.txnCtx_of_isContext`),
  `iunfold trace.isSpan` (otel; law: `trace.isSpan_End`),
  `iunfold compactReqIs` (etcdserverpb; law: `compactReqIs_open` giving the fields),
  `iunfold apply.traceRes` (apply; S2 metrics), and apply's IRR definitions through `simp only`
  (S2 metrics). Own-package unfolds (`isServerRead`, `srvReadFieldsAt`, `srvInit`) are fine. In
  `traceutil/CtxLaws.lean`, `ctxTraceIs_cancelCtx_background` executes Perennial's
  `cancelCtx.Value` code (the justified unfold of the plan, pending Perennial's law,
  `notes/perennial-changes.md`).
- Law coverage: `compactableOk_persistent` is present; `errTreeOk` from `applyErrIs`/`nil` is
  missing (S3-3).
- Trust exposure: `Compact.spec` rests on the axioms `traceutil.Tracer.Start.wp_proof`,
  `trace.WithAttributes.wp_proof`, `attribute.Bool/Int64.wp_proof`, `traceutil.Tracer_init`
  (`etc/tcb-baseline.txt`), and on `specCompact`'s `sorry`. No tester covers them yet. Not checked
  with `--roots` (no build).
- Testability: `compactOutIs`'s pure part (`v.Revision' = log.length - 1`, null-ness) is decidable;
  `ctxTraceIs` needs a context interpretation.
- Strength margin: the code returns `resp.Header.Revision = s.kv.Rev()` read after the apply. The
  post gives a certified lower bound, and that is all the compactor and the handler need.

---

## S4: `NewServer.specCompact`, `compactorOk`/`compactorRun`, `newServer.specCompact`, `StartCompactingServer.spec`, `putgetc.Main.spec`, `putgetc_safe`

### Keep
- The split of the compactor's contract into a persistent `compactorOk c` (for `run`'s
  `Pause`/`Resume`) and a one-shot `compactorRun c` spent by `start`'s `Run`
  (`InvRun.lean`, `InvStart.lean:216`). This follows the Go code: `start` runs it once
  (`server.go:599`), and `run` pauses and resumes it from the raft loop (`server.go:777,787`). The
  run token is spent on a path that has no retry.
- The glue in `start` and `run` uses the v3compactor laws `compactorOk_Run/Pause/Resume` and never
  unfolds `v3compactor.compactorOk`. That is the law-based pattern the phase-3 lesson asks for.
- The premises `AutoCompactionMode = "revision"` and `0 < retention` cite phase 0's decision 2. Go
  creates a compactor when `num != 0` (`server.go:383`) and accepts a negative duration, so a
  negative retention is legal Go (a compaction above the store, then `ErrFutureRev`). Excluding it
  is a scope choice, which phase 0 records.
- `putgetc.Main.spec` and `putgetc_safe` have `putget`'s shape, which is phase 0's decision 4.

### Findings

**S4-1 (tier 1: faithful / sufficient; the brief's question). `NewServer.specCompact`'s post is
`NewServer.spec`'s, so the compaction mode is not enforced.** `NewServer.lean:268-403`: the post
is the same `srvBuilt …`, `srvServeBuilt srv E cfg 64`, `srvWatchBuilt`, `srvKVCloser` and
`srvWatchReaders srv E 64` as the compaction-off spec (`NewServer.lean:231-260`).
- *Watchers.* `srvWatchReaders` (`InvWatchBuilt.lean:55`) is `watchTokPool` plus 64
  `mvcc.watchReader`s, which is exactly what registering watchers needs. The watchable store's
  invariant still says that no watcher state is compacted (`InvWatchStore.lean:344,347`,
  `WsOk.st_flags`/`wo_flags`). `syncWatchers`' proof assumes the compaction revision is `-1`
  (`watchableStore__syncWatchers.lean:180`, `have HcQ1 : cQ = -1 := sorry`), which is false once
  the compactor has run. Only the absence of watchers would make it vacuous (Go: `syncWatchers`
  runs only with unsynced watchers, `watchable_store.go:237-238,363-365`), and no statement gives
  that absence. "No watchers in compaction mode" is a decision that no statement records.
- *Writes.* `srvServeBuilt` and `srvBuilt` give the compaction-off request-path view, so any client
  of the built server (v3rpc's `Txn`, the client's `kv.Txn`) can propose
  `Then(OpDelete(k, WithFromKey()), OpPut(k, v))`. Decision (a)'s premise is not where callers
  must meet it (S2-1, S2-4).
- *Restore.* `srvKVCloser` and `srvBuildGap` (the snapshot path) are still handed out, and
  `etcdserver.restorePre_of_apply` takes `crevFrozen` from a `sorry`
  (`RestorePre.lean:78-79`). In compaction mode that fact is false after the first compaction.
  "No restore in compaction mode" rests on the snapshot path being unreachable. The plan names
  "one member" for this, but `NewServer.specCompact` and `newServer.specCompact` take any peer list
  `γ.vs`; only `StartCompactingServer` fixes `γ.vs = [id]`. **Uncertain** whether D21 M3's
  no-snapshot bound (`receiptBound ≤ SnapshotCatchUpEntries + 1`, shared with the compaction-off
  spec) already makes `applySnapshot` unreachable for several members. To settle it: check
  whether `SnapApplyWalk`'s use of `restorePre_of_apply` is reached in the no-snapshot mode for
  `γ.vs ≠ [id]`.

*Restatement:* `NewServer.specCompact`'s post gives the compaction-mode views (S2-1), either no
watch readers (`srvWatchReaders srv E 0`, and a `srvServeBuilt` whose watch service is absent or
takes a premise) or a watchable-store invariant that admits compaction. It also takes
`γ.vs = [id]` if S4-1's uncertain point fails. `newServer.specCompact`, `StartCompactingServer.spec`
and their `memberBuilt`/`memberUp` posts then need the mode too (a `memberUpC`, or a mode
argument); today they are the compaction-off predicates (`newServer.lean:99`,
`StartCompactingServer.lean`'s post `memberUp s ρ E₀ lg γn id`).

**S4-2 (tier 1: process / trust exposure). The `m2` collection cannot see the compaction proofs.**
`NewServer.wp_proofCompact` takes no callee hypotheses, so `putgetc_safe`'s axioms do not include
`EtcdServer.Compact.wp_proof`'s or `processInternalRaftRequestOnce.wp_proofCompact`'s `sorry`.
`etc/tcb-collections/m2.txt` lists `sorry common.newServer.wp_proofCompact` but not
`NewServer.wp_proofCompact`, which looks stale: `newServer.wp_proofCompact` now has no `sorry`
(`examples/common/newServer.lean:141-`). The fork reported this too. *Fix:* the hypotheses of
S3-3, then `--collection etc/tcb-collections/m2.txt --check --update`.

**S4-3 (tier 2: weak side of a disjunction, checked).** `compactorOk c := ⌜c = nil⌝ ∨ ∃ T P, …`
and `compactorRun`'s `⌜c = nil⌝ ∨ …`. The weak side is false for a compactor-on server. No caller
needs to know which side holds: `start` and `run` handle both, as Go's `if s.compactor != nil`
does. So the disjunct is not vacuous for any caller, and I report it only because I checked it.
`compactorRun`'s `P` is existential, which is fine for `start`, since it only passes `P` to `Run`.

### Metrics
- Scope premises: `NewServer.specCompact`: mode `revision`, `0 < retention` (decision 2, cited);
  `newServer.specCompact`/`StartCompactingServer`: `0 < retention` (decision 2), and
  `StartCompactingServer` keeps `putget`'s `γ.vs = [id]`. A one-member premise may be missing
  (S4-1, uncertain). Decision 2's "no watches" and the S1-step-4 revision's "no watchers" have no
  premise or withheld resource.
- Caller burden: `start`/`run` unfold only their own package's definitions (`compactorRun`); the
  v3compactor laws cover the rest. `newServer.wp_proofCompact` unfolds `common`'s own definitions.
  `NewServer`'s construction of `E` is not written (S3-3).
- Law coverage: `compactorRun_ok` (run to contract) is present; `compactorOk_Run/Pause/Resume`
  added in v3compactor; `errTreeOk` laws missing (S3-3).
- Trust exposure: S4-2. `NewServer.specCompact` is otherwise `NewServer.spec`'s premises plus two.
- Size: `NewServer.specCompact` is about 135 lines, a copy of `NewServer.spec` (only the premise
  lines differ). A mode parameter would avoid the copy (S2-7).
- Strength margin: the post does not say that the compactor is non-nil or that it runs, which
  `putgetc_safe` (no panic, no stuck thread) does not need.

---

## S1: the readers (`storeReader := storeReaderC`, explicit `crev`, `ReaderSpecs.lean`, txn's `checkRangeErr`/`rangeResult`/`Range`/`Count`, the exported reads)

### Keep
- `storeReader := storeReaderC` (`InvStore.lean:3315`), phase 0's decision, with the old laws
  turned into identities. Pass-through users needed no change.
- `checkRangeErr` (`txn/InvRange.lean`) matches Go's `checkRange` (`txn/range.go:174-184`): `nil`
  at revision `0`; `ErrFutureRev` above `rv.Rev()`; `ErrCompacted` below `rv.FirstRev()`, which is
  the transaction's `compactMainRev` (`kvstore_txn.go:61,66`). A negative revision is
  `ErrCompacted` exactly when it is below `crev`.
- `rangeResult`'s four cases match mvcc's `rangeKeys` (`kvstore_txn.go:73-83`): future first, then
  `rev ≤ 0 → curRev`, then `ErrCompacted` below `compactMainRev`, and only then the context check
  of a full read, hence `crev ≤ rangeRev` on the context-error case (commit `7e4cd5790d`). The read
  holds `s.mu.RLock` while `store.Compact` takes `s.mu.Lock`, so the live `compactMainRev` that
  `rangeKeys` reads is the transaction's `crev`.
- `Count`'s compacted case (`Spec/.../txn/Count.lean`) is right: `Count` returns `0, err` on any
  error (`range.go:41-43`).
- `rangeOutcomeC_latest`, `isTxnRead_crev`: the laws a latest read needs (`putgetc`'s `Get`).

### Findings

**S1-1 (tier 2: weakest statement / abstraction). The `∃ crev` added to success-only statements
carries nothing.** `range_linearizable`, `range_serializable` (`etcdserver/Results.lean:624,668`),
`rangeReadOk`/`rangeReadOkM` (`InvRead.lean:203`, `ReadOn.lean:123`), `rangeAnsOk`
(`v3rpc/ServerKV.lean:220`), `etcdState_of_range` (`v3rpc/Results.lean:616`) all state
`∃ crev, txn.rangeResult resp GoInterface.nil log rev crev o true`. With `err = nil` only the
success disjunct is possible, and its extra conjunct `crev ≤ rangeRev rev o.base.rev` holds for
`crev = -1`, since `rangeRev ≥ 0` on a non-empty log. So the existential is equivalent to the old
`crev = -1` statement. These are trusted statements that phase 0 said would stay unchanged
("Unchanged: … v3rpc's KV results (beyond the reader)").
*Restatement:* a law `txn.rangeResult_nil : rangeResult resp nil log rev crev o wt ⊢ rangeOk resp
log rev o wt` (a crev-free success predicate, or `rangeResult … (-1)`), with the exported
statements reverted to the crev-free form.

**S1-2 (tier 2: caller burden). Clients unfold `txn.rangeResult` and split it four ways.**
`client/v3/Results.lean:1168-1174` (`etcd_rangeHandlerOk`) and `v3rpc/ServerKV.lean:677-684`
(`kvRangeOk_of_server`) each `iunfold txn.rangeResult` and discharge three impossible cases by
hand (with `rotate_left`). The added fourth case grew both. The law of S1-1 removes the unfolds.

**S1-3 (tier 2: naming).** `mvcc/Results.lean` keeps the names `mvcc_store_Read_frozen`, … for
the `specR` statements. These are exported results, and "frozen" now says the opposite of what
they state. *Fix:* rename them `_R`.

**S1-4 (tier 2: a pure `sorry` that is false in the target mode).**
`watchableStore__syncWatchers.lean:180` (`have HcQ1 : cQ = -1 := sorry`) and `RestorePre.lean:79`
(`crevFrozen E.γ` from nothing) stand in for S1 steps 4-5. Each asserts something false in a
compaction-mode server (see S4-1), not a missing proof of a true statement. In compaction-off
mode both are derivable: `server_kv_backend` still allocates `crevFrozen` (`Results.lean:851`,
`#Hfrz`), but the fact is no longer passed to the apply thread's `kvOwn` or to the watchable store.
*Suggestion:* thread `crevFrozen` through the compaction-off views (a mode-off conjunct of
`apply.kvOwn` and of the watchable store's invariant). The two `sorry`s then disappear from every
compaction-off result. The compaction-mode cases are S4-1's design.

### Metrics
- Scope premises: none new.
- Caller burden: S1-2 (two clients, `txn.rangeResult` unfolded; four-way case split each).
- Law coverage: `isTxnRead_crev`, `storeTxnReadIs_crev`, `rangeOutcomeC_live/latest` are present;
  `rangeResult_nil` is missing (S1-1).
- Trust exposure: the S1 `sorry`s of S1-4. `etc/tcb-baseline.txt` lists
  `sorry apply.rangeOutcomeIs_errIs`, but `apply/DispatchLemmas.lean` has no `sorry` at this
  commit, so the baseline is probably stale (**uncertain**, needs `etc/tcb-report.py --check`).
- Testability: `checkRangeErr`, `rangeResult`'s pure parts and `Count`'s post are decidable given
  `crev`.
- Strength margin: a read gives no upper bound on `crev` (C3 deferred, by decision).

---

## Ranking (most in need of revision first)

1. **S2** (`CompactMode.lean`, `specCompact`): the compaction mode is in no statement (S2-1),
   the success post is unsatisfiable (S2-2), and future revisions are not covered (S2-3).
2. **S4** (`NewServer.specCompact` and the examples' variants): the post is the compaction-off
   one, with watchers, unrestricted writes and restore (S4-1), and the trust exposure is hidden
   (S4-2).
3. **S3** (`Compact.spec`/`specOn`): it inherits S2-1 (S3-1), `specOn` has no route (S3-2), and
   the compactor's environment glue is absent (S3-3). The freeze repair itself is sound.
4. **S1** (the readers): true of the code; tier-2 work only (S1-1 to S1-4).

## Uncertain points (not verified)

- Whether `irrNoDelPut` survives `irrWireOf`'s range-end rewriting (S2-4). Settle it by proving
  `irrNoDelPut_wire`, or restate the premise syntactically.
- Whether `store.Compact.spec` can take `rev < log.length → NoDelPutAt …` without restructuring
  its proof (S2-3).
- Whether `NewServer` has a spare `srvLeadTimeReader`, `srvLgReader` and `E.RD` for the
  compactor's goroutine, and whether `errTreeOk` follows from `applyErrIs` (S3-3). Settle it by
  writing `NewServer`'s construction of `E`.
- Whether the no-snapshot bound makes `applySnapshot` unreachable with several members, which
  decides whether `NewServer.specCompact` needs `γ.vs = [id]` (S4-1).
- The staleness of `etc/tcb-baseline.txt`/`m2.txt` entries (S1 metrics, S4-2). Settle it by
  running `etc/tcb-report.py --check` and `--collection etc/tcb-collections/m2.txt` after a build.

No bug in the Go code was found in this round. The Go behaviors relied on above (the nil trace on
a failed compaction, `ErrFutureRev` for a future compaction, `syncWatchers` skipping when no
watcher is unsynced) are the documented or evident ones, so nothing new goes in `issues/`.
