# M2 spec skeleton, review round 3 (phase 1b)

*Copied to `lean` on 2026-11-01 from branch `m2` (M2's first attempt, paused after this round and superseded by `m2-storage-plan.md`/`m2-apply-plan.md`), which was then deleted: the commits this review names (`m2`'s, up to `98c3d7c6f2`) are no longer reachable.*

Reviewer: a new `spec-reviewer` agent, 2026-10-28. Worktree `/shared/etcd-grove-cp`, branch `m2`, commit
under review `925157e9d0` (`HEAD`). Changes reviewed: `git log b6824aebb5..925157e9d0` (9 commits). Go
code: the fork at `249d76bea` in `/shared/etcd-fork-m2`. Nothing was built or run (no `lake build`,
`lean-check` or `tcb-report`). Every claim comes from reading the text, and a claim marked
*uncertain* was not checked.

## Summary (tier 1)

1. **On a real server, the compaction arm cannot be reached through any statement: `storeCmp` is
   false there** (new; this is the author's open finding (2), and it is worse than "no source").
   - `compactPre` requires `⌜mvcc.storeCmp E.γ⌝` (`apply/Chain.lean:1002-1003`), as
     `store.Compact.spec` does (`Spec/.../mvcc/store__Compact.lean:66`).
   - `storeCmp γ := kbCmp γ.kb` and `kbCmp kb := kb = none` (`mvcc/InvStore.lean:1502-1505`). That is
     mvcc's *assumed* backend.
   - The server's store runs over the real backend. The apply thread holds
     `srvBeOwn s E ⊢ ∃ d, ⌜E.γ.kb = some d⌝` (`InvApplier.lean:554-557`, inside `srvApplyKV`, `:571`).
   - So on every server `compactPre` is `False`. The new `Compaction` triple of `applierTriples` is
     vacuous, and the arm (`uberApplier__dispatch.lean:479`) can never meet its precondition. The
     same holds for `processInternalRaftRequestOnce.wp_proofCompact` (`:717`), and through it
     `EtcdServer.Compact`, `putgetc_safe` and the on case of `NewServer`.
   - The real backend is excluded on purpose. Its model has no deletion from `Key`, no meta keys and
     no write-back budget for the job (`notes/decisions.md:4857-4886`; status-history 13641,
     13722: "the compaction over the real backend ... what remains").
   - `notes/m2-plan.md` never mentions this. Its survey (`:11`) says "mvcc's compaction-aware path is
     complete". This is a phase-0 scope gap: M2 needs the backend extension (a stage of its own),
     or a decision to scope it differently. No restatement of the server's specs fixes it.
2. **`dispatch.spec` neither takes nor returns the compaction right.**
   - Its precondition (`Spec/.../apply/uberApplier__dispatch.lean:43-48`) has no `cmpRight E`, and
     `kvOwn` (`Chain.lean:386-388`) does not contain it.
   - `uberApplier.Apply` frames it outside the call (`Proof/.../uberApplier__Apply.lean:35,79,94`:
     `Hcr` is kept, not passed in). So even with item 1 fixed, the arm has no right to give
     `compactPre`.
3. **`NewServer`'s on case still cannot be proved, for two new reasons.**
   - (a) Its post hands out `srvKVCloser srv E` in both modes (`Spec/.../NewServer.lean:243`).
     `compactRight` can only be made by consuming the closer (`compactRight_of_closer`,
     `InvStore.lean:4909`; `compactQueue γ (-1)` and the scheduler's stop token live only in
     `storeCloser`). The token's `dghostVar … (own 1)` and `schedLive`'s `DFrac.discard`
     (`schedule/Defs.lean:90-96`) are exclusive. So `cmpRight E` (needed by `uberOwn` through
     `NewUberApplier`) and `srvKVCloser` cannot both be given.
   - (b) `mvcc.New.spec`'s `cmp = true` branch returns `crevUB γ.st.idx ½ (-1)` but not
     `wsUnwatched γ`. `srvWatchBuilt`/`srvWatchReaders` need `watchPoolM true γ = wsUnwatched γ`, and
     no law derives it from the sealed `isWatchableStore` (whose disjunct `crevFrozen ∨ wsUnwatched`
     cannot be refuted without opening the store's lock invariants).
4. **The request path does not carry the mode, and the auth-on side admits compactions.**
   - `specCompact` takes `E.cmp = true`, but `isServerReq` (`InvProposer.lean:403-428`) has no
     `E.cmp = ρ.kv.cmp`. The proposal's permit needs `ρ.kv.cmp = true` (`reqPropOk`,
     `InvRequest.lean:462`), so `specCompact` (and `Compact.spec` on top of it) is unprovable as
     stated.
   - With auth on, `reqPropOkOn`'s first disjunct (`ProposeOn.lean:168-169`) still admits a
     compaction. `plainReq` includes `.compaction`, and neither `rqShape` nor `kvShapeAll` excludes
     it. So the new `sorry` `HcmpL : logCmpOk ρ.kv.cmp L` (`ServerOn.lean:666-667`) does not follow
     from `kvInvOn`. As defined it is unprovable (on an auth-on server `ρ.kv.cmp = false`), and the
     auth-on results rest on it.

Round 2's three tier-1 findings, and what became of them:
- **The mode: an off server commits no compaction.** Fixed for auth off: `reqPropOk`'s guard,
  `cmpLogOk` in `kvWork`, `cmpOk` at dispatch, `Compact.spec` with `E.cmp = true`. Open for auth on
  (item 4) and at `isServerReq` (item 4).
- **NewServer's on case provable in principle.** The pool is fixed (`watchPoolM`), but it is still
  unprovable (items 3a and 3b), and the backend gap (item 1) blocks it anyway.
- **The compaction answer gives what Compact reads.** Fixed in the vocabulary: `dispatchAnswer`'s
  compaction case, `compactAnswerIs` and `resTrace`. The derivation is still unproved and unstated
  (T2-1).

---

## T1. The apply side: `compactStep`/`Chain.hasCorrupt`, `compactPre`/`compactPost`/`compactAnswerIs`, the `Compaction` triple, `cmpRight`, `cmpOk`, `dispatchAnswer`'s compaction case

### Good
- **`compactStep` over `Chain.hasCorrupt`** (`Chain.lean:956-971`) is right for any nesting.
  `Compaction` is overridden only by `applierV3backend` and `applierV3Corrupt` (grep in `apply/*.go`:
  `backend.go:66`, `corrupt.go:45`). Auth, quota and capped promote it, and auth's admin check never
  fires for it (`needAdminPermission` is false).
- **`compactAnswerIs` matches Go.**
  - Backend error: `return nil, ch, nil, err` (`backend.go:74-75`).
  - Corrupt: `nil, nil, nil, ErrCorrupt` (`corrupt.go:45-47`).
  - Success: `resp` and `resp.Header` freshly allocated (`backend.go:67-68`), and the trace from
    `EnsureTrace(context.TODO(), …)`, which is fresh.
  - `applierV3Corrupt.Compaction.spec` states exactly that.
- **`dispatchAnswer`'s compaction case** (`InvUber.lean:288-301`) now gives the response's dynamic
  type in both outcomes and, on success, ownership of the response and its header. That is what
  `v3_server.go:422-428` needs. Round 2's T1-2 is fixed in the vocabulary.
- **`cmpOk`** is the right shape: a per-request pure guard, discharged from the entry by
  `cmpOk_of_entryCmpOk`. On an off server it makes the arm vacuous.
- **Round 2's T1-3** (stale "out of the model" prose in `dispatch.spec`'s docstring) is fixed
  there.

### Findings

**T1-1 (tier 1, item 1): `compactPre` is `False` on the server.** The evidence is above.
*Affects:* the arm, `specCompact`, `Compact.spec`, `NewServer`'s on case, `putgetc_safe`.
*Restatement:* none at this level. Choose one and record it in `notes/m2-plan.md`:
- (a) A backend stage first: the real backend's contract gets `Cmp` (deletion from `Key`, the meta
  keys, the job's budgets, `decisions.md:4866-4884`), so that `kbCmp (some d)` can hold.
- (b) Drop the server from M2's compaction claims until (a) is done.

Keep `⌜storeCmp E.γ⌝` out of `compactPre` once (a) lands: it becomes a law of the backend, not a
per-call premise.

**T1-2 (tier 1, item 2): `dispatch.spec` lacks `cmpRight E`.**
*Restatement:* move the right into the apply thread's store resources:
`kvOwn E log := … ∗ cmpRight E`. `compactPost` already returns `cmpRight E ∗ kvOwn E …` side by
side. Then:
- `dispatch.spec`, `Apply.spec` and every method's `mPre` carry it unchanged;
- `uberOwn` drops it;
- `NewUberApplier.spec` (both copies) drops `apply.cmpRight E -∗`.

That last change is also a locality fix. Go's `NewUberApplier` never touches the store's
compaction right, so the applier constructor's spec should not mention it (PRINCIPLES, "Local").

**T1-3 (tier 1, the author's open finding: `storeStop` has no source).** `storeStop E.s E.γ` is made
only by `compactRight_of_closer`, together with the right (`InvStore.lean:4909-4911`).
*Restatement:* `cmpRight E := if E.cmp then ∃ c, compactRight E.γ c ∗ mvcc.storeStop E.s E.γ else
True` (`storeStop` is persistent), and drop the separate `storeStop` conjunct from `compactPre`.

**T1-4 (tier 2, the author's open finding: `txn.isKV` has no `Compact` method spec).** This is not
a spec gap. `isKV` is concrete (`txn/Defs.lean:89-94`: the plain store or the watchable store), so
the backend's proof resolves `a.options.KV.Compact` to `store.Compact` (directly, or through the
watchable store's promoted method) and `KV.Range` to `readView.Range`. The latter does not use the
context's trace (`kv_view.go:27`). One proof-side need: the promoted `watchableStore.Compact`
wrapper. *Uncertain:* whether Goose emits a wrapper that needs its own spec.
The `rr, _ := KV.Range(...)`/`rr.Rev` dereference in Go does not panic: every error return of
`rangeKeys` has a non-nil result, except "context cancelled", and a `context.TODO()` child is never
cancelled (`kvstore_txn.go:76-121`). **No Go bug.**

**T1-5 (tier 2, stale prose).** These were written before `5fe6ed645d` added the triple:
- `Chain.lean:18-20` ("no triple of `applierSpec` is about it yet ... pending");
- `Chain.lean:33-34` ("every method but `Compaction`, whose triple M2's step 2 adds, pending").

**T1-6 (tier 2, trust; round 2's T1-4, not addressed).** The `dispatchAnswer_notNoSpace` `sorry`s
are still there (`NoSpaceDead.lean:200`, `NoSpaceDeadOn.lean:147`). Under `compactStep` the
compaction's outcome is never `.applied _ true`, so each is a short proof.

---

## T2. The request path: `reqPropOk`/`cmpLogOk`/`logCmpOk`/`entryCmpOk`, `processInternalRaftRequestOnce.specCompact`, `compactResultIs`

### Good
- `reqPropOk`'s non-write case gains `dispatchKind rq = .compaction → γk.cmp = true`
  (`InvRequest.lean:462`), and `kv_prop_au` threads it into `cmpLogOk` (`KVLemmas.lean:197-231,
  262-296`). So for auth off, round 2's "an off server can commit a compaction" is closed at the
  invariant.
- `cmpOk_of_entryCmpOk` and `entryCmpOk`'s `m.data = []` disjunct (raft's empty fillers) are
  correct.

### Findings

**T2-1 (tier 1, item 4a): `isServerReq` lacks the mode equality.** `specCompact` (and
`Compact.spec`) take `E.cmp = true` and `isServerReq s E ρ`. `reqPropOk ρ.kv` needs
`ρ.kv.cmp = true`, and nothing in `srvReqFieldsAt` links `E.cmp` to `ρ.kv.cmp`. `isServer` has the
link (`InvApplier.lean:527`, `srvBuilt`'s `Hcmpk`), but these specs do not take `isServer`.
*Restatement:* add `⌜E.cmp = ρ.kv.cmp⌝` to `srvReqFieldsAt`. It is available where it is built,
since `srvBuilt` holds it.

**T2-2 (tier 1, item 4b): the auth-on permit admits compactions, so `ServerOn.lean:667` is
unprovable.**
*Restatement:* the same guard in `reqPropOkOn`'s first disjunct (`ProposeOn.lean:168`), and
`cmpLogOk γk.cmp L` in `kvWorkOn` (`KVAuthModel.lean:574`), as `kvWork` has. A simpler alternative,
since auth on keeps the compactor off (`NewServer.specM`): exclude `.compaction` from
`reqPropOkOn` outright. Either way, the `sorry` then becomes the same proof as for auth off.

**T2-3 (tier 2; round 2's T2-1, not addressed): `specCompact` is still a separate triple and a bare
`sorry`** (`Proof/.../EtcdServer__processInternalRaftRequestOnce.lean:715-717`). With round 2's
T1-2 fixed and T2-1 above fixed, it should be a corollary of `spec`.
- **The author's open finding (3), "specCompact's pre lacks an `idxCert`", is not a gap.**
  Instantiate `spec` at `F = []` with `mvcc.idxCert_nil` (`InvIndex.lean:1174`), as
  `Compact.wp_proof` already does (`:60`).
- **`compactPropOk` is too general to be derived** (`CompactMode.lean:35-36`). It admits a request
  whose later fields (an auth field) are also set. Then `needAdminPermission rq = true` and
  `plainReq` fails, so `spec` does not apply. Go would still apply it as a compaction with auth off,
  so `specCompact` is not false, but it cannot be derived.
- *Restatement:* `compactPropOk rq := ∃ rev, rq = irrCompaction rev` (the only caller's request,
  `compactPropOk_irrCompaction`), then
  `theorem specCompact_of_spec : processInternalRaftRequestOnce.spec → specCompact`. That needs a
  law `resultIsW E ρ.rd rq' [] res lb ∗ resTrace res ⊢ compactResultIs res` for a compaction `rq'`.
  *Uncertain:* whether `irrNoZeroEnd`/`rqShape` of `irrCompaction` reduce by `decide`/`simp` (I
  expect so).

**T2-4 (tier 2, stale docstrings).** Both docstrings still say "on the server every proposer sees
(`isServerReq`: its KV invariant admits compaction entries, M2's one family ...)":
`specCompact` (`Spec/.../EtcdServer__processInternalRaftRequestOnce.lean:99-104`) and
`Compact.spec` (`Spec/.../EtcdServer__Compact.lean:36-38`). `Compact.spec`'s "(Phase 1's statement:
what the apply does with the compaction ... not stated yet ...)" (`:49-53`) is stale too.

---

## T3. `resTrace` without the error escape; `rejectResultIs`'s null trace (question 4)

### Good: verified true of every applier path
- **`dispatch`** (`uber_applier.go:91-200`) sets `ar.Trace` only from `Range`, `Put`,
  `DeleteRange`, `Txn` and `Compaction`. Every other arm leaves the zero `nil`, and `traceRes null`
  holds (`traceRes_null`).
- **The four KV methods' triples** already returned `traceRes trace` on every outcome
  (`Chain.lean:1027,1033,1039,1045`), and Go matches:
  - backend: `mvcctxn.*` return their own fresh trace, or `nil` (`txn.go:57,78`);
  - capped, corrupt and auth rejections: `return nil, nil, err`;
  - quota: forwards the backend's trace.
- **`Compaction`**: `compactAnswerIs` (above).
- **The auth layer's admin rejection** is `&Result{Err: err}` (trace `nil`), which
  `rejectResultIs`'s new `v.Trace' = null` records. `uberApplier.Apply`'s proof uses it
  (`resTrace_err … Hvf.2.2`).
- **The reason is real.** `v3_server.go:393-400` reads `result.Trace` before testing `result.Err`.

### Findings
None. The margin is that `resTrace` could say `null` on rejection, but no caller needs it.

---

## T4. mvcc: `New.spec`/`newWatchableStore.spec`'s `cmp`, `wsMode_alloc`, `watchPoolM`

### Good
- **The choice is ghost and in the right place.** `mvcc.New` is where the right's half and the
  watcher budget are both available. `wsMode_alloc` (`InvWatchStore.lean:1388-1409`) is a clean
  law, and `watchPoolM` with `watchPoolM_false` makes the off case literally today's statement.
- **Round 2's T5-1 and T5-2 are fixed at the statement level.** `wsUnwatched` replaces the pool in
  the on case (`srvWatchBuilt`, `srvWatchReaders`, `watchSrvOk`), and `New` no longer always
  freezes.

### Findings

**T4-1 (tier 1, item 3b): the `cmp = true` post lacks `wsUnwatched γ`.**
*Restatement:* `(if cmp then mvcc.crevUB … ∗ mvcc.wsUnwatched γ else mvcc.watchToks γ (2^63-3))`
in both `New.spec` and `newWatchableStore.spec`. `wsMode_alloc` already produces it.

**T4-2 (tier 2, abstraction).** The `cmp = true` branch exposes `mvcc.crevUB γ.st.idx (1:Qp).half
(-1)`: an internal ghost name, a fraction and the counter's encoding (PRINCIPLES, "No ghost names,
fractions"). Its only use is `compactRight_of_closer` with the closer.
*Restatement:* in the `cmp = true` branch, `New` does the conversion itself and returns
`compactRight γ.st (-1) ∗ storeStop s γ.st` with a watchable-store closer that no longer contains
the inner `storeCloser`. Equivalently, give the half an opaque name with the one law. This is also
what makes T5-1 below cheap.

**T4-3 (tier 2, trust).** The `syncWatchers` `sorry` (`watchableStore__syncWatchers.lean:182`) is
unchanged from round 2 (should be easy).

---

## T5. `NewServer.spec`, `NewServer.specM`, `newServer.spec`, `StartCompactingServer`, `memberBoot`

### Good
- **The premise is tied to the configuration.** `(retention = 0 ∧ E₀.cmp = false) ∨ (revision ∧
  0 < retention ∧ E₀.cmp = true)` (`Spec/.../NewServer.lean:152-154`) is a case split on the
  input. It is not a disjunction of alternative specs.
- **`envAgree` now carries `E.cmp = E'.cmp`**, so the built `E`'s mode is the stand-in's.
- **`applySnapshot.specSnap`'s `E.cmp = false`** records the Restore exclusion where it is used.

### Findings

**T5-1 (tier 1, item 3a): `srvKVCloser` in the post is incompatible with the on case.**
*Restatement:* `(if E.cmp then True else srvKVCloser srv E)` in `NewServer.spec`'s post (`:243`,
`:400`). Its only consumer is `applySnapshot.specSnap`, which already requires `E.cmp = false`.
Nothing else in `Spec/` or the examples takes it (grep).

**T5-2 (tier 2; round 2's T6-3, not addressed): `specM` still diverges from `spec`.**
`specM` keeps `retention = 0 ∧ E₀.cmp = false` (`:305`), so `spec ≠ specM false`.

**T5-3 (tier 3, size): `newServer.spec`'s `cmp` is determined by `retention`.** A parameter fixed
by another is redundant.
*Restatement:* `memberBoot … (decide (0 < sint.Z retention))`, with no `cmp` binder or
disjunction. The default arguments `cmp := false` on `memberBoot`, `AEnv` and `KVNames` also let a
call site pick the off mode silently. Prefer explicit arguments.

---

## T6. The mode bit's spread (question 3)

The facts:
- **Two bits:** `AEnv.cmp` (apply) and `KVNames.cmp` (etcdserver's KV invariant).
- **The equality between them** appears in `srvBuilt`/`InvStart`/`StartOn`/`isServer` (`Hcmpk`),
  in `NewServer`'s premise `ρ.rd.kv.cmp = E₀.cmp`, and in both `memberBoot` and `memberBootOn`.
- **`logCmpOk`** is a new premise of 8 server specs (`apply`/`applyAll`/`applyEntries` ×
  spec/specOn, plus `applyEntryNormal`'s two `entryCmpOk`).
- **`cmpOk`** is in `Apply`/`uberApplier.Apply`/`dispatch`.
- **`cmpRight`** is in `uberOwn` and the two `NewUberApplier` specs.
- **`watchPoolM`** is in three predicates.
- **`E.cmp = false`** is in `linkv3p`'s `memberAt`/`memberWatch` and in the exported
  `etcd_cache_served` and `wk_served`.

Judgment:
- **Two bits are justified.** The KV invariant is indexed by `KVNames` and must state the
  restriction purely, and the apply package does not see `KVNames`. One equality fact suffices if
  it sits in the two persistent views every consumer holds: `isServer` (done) and `isServerReq`
  (missing, T2-1).
- **Simpler placements, in order of payoff:**
  1. `cmpRight` in `kvOwn`, not `uberOwn`/`NewUberApplier` (T1-2): this fixes a tier-1 issue and
     a locality violation.
  2. `logCmpOk` folded into the existing per-entry workload fact: `entryShape`/`logShapeM` taking
     the mode, or `clusterWorkloadOk` alone. That removes 8 new premises; they follow the
     `logShape` pattern, so this is not urgent.
  3. One definition instead of two for the same fact: `cmpLogOk` (`kvWork`) and
     `logCmpOk`/`entryCmpOk` (apply specs).
  4. `newServer`'s `cmp` binder dropped (T5-3).
- **The watch side is minimal for this stage.** The `E.cmp = false` hypotheses on the two exported
  results are discharged at the one caller each from `memberBoot_cmp` (`watchkv/Main.lean:188`),
  and `E` already appears in those statements. This is the "watch API takes an off fact" design
  the round-1 repair rejected and round 2 recommended. Its reach is the predicted few sites.

---

## T7. The frozen v3compactor specs (question 5)

- **`compactableOk_server`** now takes any permit `P` and `E.cmp = true` (`CompactEnv.lean:71-78`).
  Round 2's T3-2 is fixed.
- **Nothing in the frozen specs is new that M2's callers cannot use.** The blockers are on the
  server side: T1-1, T1-2, T5-1, T4-1.
- **Still uncertain, as in round 2:** whether `NewServer` has spare `srvLeadTimeReader`,
  `srvLgReader`, `E.RD` and `storeReaderC` for `srvCompactR` beyond what `srvServeBuilt` takes.
- **Carried from round 2 (T3-3), not addressed:**
  - `v3rpc.kvServer.Compact.spec` lacks `ctxTraceIs ctx none`;
  - `newRevision.lean:9` and `newPeriodic.lean:10` import `traceutil.CtxLaws` publicly;
  - `Compact.spec`'s docstring still calls `storeReaderC` "the compaction-aware reader" (harmless
    now).

---

## Trust base

**TB-1 (tier 1, process; round 2's TB-1, not addressed).**
- `etc/tcb-baseline.txt:733-734` still lists `NewServer.wp_proofCompact`, which no longer exists
  (grep: no such theorem).
- None of the newer `sorry`s is listed: `NewServer.lean:1957`, `uberApplier__dispatch.lean:479`,
  `newApplierV3Backend.lean:322` (new this round), `ServerOn.lean:667` (new this round, and
  unprovable as stated, T2-2), `syncWatchers:182`, `store__Compact.lean:154`, `Compact.lean:1756`,
  `NoSpaceDead{,On}`.
- Read from the text only: `--check` would fail (not run).

## Issues

`issues/etcd-compaction-delete-then-put.md` now has its status line (round 2's T4-2 is fixed). I
found no new Go bug.

## Ranking (most in need of revision first)

1. **The apply side's reachability** (T1-1, T1-2, T1-3): `storeCmp` is false of the server's
   backend (a scope decision for the plan), `dispatch` lacks `cmpRight`, and `storeStop` has no
   source.
2. **`NewServer`'s on case and `mvcc.New`'s `cmp` branch** (T5-1, T4-1, T4-2): `srvKVCloser` against
   `compactRight`, the missing `wsUnwatched`, and the exposed fraction.
3. **The request path's mode** (T2-1, T2-2): `isServerReq`'s equality, and the auth-on permit that
   makes `ServerOn.lean:667` unprovable.
4. **Trust baselines and the easy `sorry`s** (TB-1, T1-6, T4-3).
5. **`specCompact` as a corollary** (T2-3), and the stale prose (T1-5, T2-4).
6. **The mode spread's simplifications** (T6), `specM` (T5-2), `newServer`'s `cmp` (T5-3), and the
   carried v3compactor items (T7).
7. **`resTrace`/`rejectResultIs`** (T3): correct as stated.

**Verified by reading code:**
- T1-1 (`kbCmp`, `srvBeOwn`), T1-2 (the dispatch spec and the Apply proof), T1-3, T1-4 (Go's
  `Range` returns);
- T2-1, T2-2 (`reqPropOkOn`, `plainCover`, `rqShape`), T2-3's `idxCert_nil`;
- T3 (all Go paths);
- T4-1, T5-1 (definitions of `storeCloser`, `compactRight`, `schedStopTok`/`schedLive`);
- TB-1 (text).

**Uncertain:**
- whether a formal exclusivity lemma for `schedStopTok`/`schedLive` exists (I relied on
  `dghostVar` own 1 against discard);
- the promoted `watchableStore.Compact` wrapper's spec;
- `irrCompaction`'s `rqShape`/`irrNoZeroEnd` by `decide`;
- `NewServer`'s spare reader slots;
- whether `tcb-report --check` fails (not run).
