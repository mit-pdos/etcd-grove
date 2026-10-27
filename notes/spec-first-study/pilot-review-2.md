# Compactor pilot: spec review, round 2

Reviewer: the `spec-reviewer` agent, run fresh. It did not read `notes/spec-first-study/pilot-review-1.md`
or the "Step 2b" paragraphs of `notes/compactor-pilot-plan.md`. Everything is from worktree
`/shared/etcd-grove-cp` (branch `compactor-pilot`, HEAD `3d9674d345`). The Go sources are at the pin in
`/shared/etcd-grove/.lake/go-src/etcd`. The rubric I used is `notes/spec-first-plan.md` "Phase 1b". It
matches the agent file. I ran nothing that writes: no build, no `lean-check`, no `tcb-report` (that
report needs an up-to-date build, so I read the trust exposure from `etc/tcb-collections/compactor-pilot.txt`
instead).

Abbreviations: `Defs` is `Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3compactor/Defs.lean`;
`CDefs` is `Proof/github_com/jonboulle/clockwork/Defs.lean`; `periodic.go`, `revision.go` and
`compactor.go` are in `server/etcdserver/api/v3compactor/`.

---

## 1. `EtcdServer.Compact.spec` / `specOn` / `compactOutIs` (`Spec/.../etcdserver/EtcdServer__Compact.lean`)

**Good (keep)**
- It has both auth modes (`spec`, and `specOn` over `isServerReqM true`), as `Put` does.
- It accepts any revision. That is right: a future revision is the apply's `ErrFutureRev`, and the
  gRPC caller passes the client's revision unchecked.
- It gives back every per-thread resource (`srvLeadTimeReader`, `E.RD`, the store reader). The
  compactor's goroutine needs this, because it calls `Compact` in a loop.
- `compactOutIs` covers the result the compactor inspects: either `err = nil` or `applyErrIs err`.
- `idCred ρ.ids 1` is pure and persistent (`idutil/Defs.lean:265`), so repeated calls cost nothing.

**Findings (verified)**

**F1.1 (Tier 1, true / sufficient for its callee: it cannot be proved over `processInternalRaftRequestOnce` as that is specified).**
- Evidence: `Compact` calls `processInternalRaftRequestOnce` with `InternalRaftRequest{Compaction: r}`
  (`v3_server.go:390`). That spec (`EtcdServer__processInternalRaftRequestOnce.lean:56`) requires
  `reqPropOk ρ.kv rq Qr`.
- Every disjunct of `reqPropOk` (`InvRequest.lean:1280-1292`) requires `rqShape rq`. `rqShape` is
  `∀ on, dispatchOk on rq` (`WorkloadDefs.lean:260`), and `dispatchOk` requires
  `dispatchKind rq ≠ .compaction` (`apply/InvUber.lean:63-64`).
- The same exclusion sits inside the `isServerReq` that `Compact.spec` takes as a premise: `kvInv`'s
  `logShape` says no compaction entry is ever committed.
- So the precondition holds, but the callee's precondition can never be met for a compaction request.
  The spec is unprovable until the server model work of scope (A) is done.
- This is known as plan work, but the spec reads as if it were already over that model. Its docstring
  says "it proposes the compaction through raft and returns" with no mention that the premise
  `isServerReq` currently forbids exactly that.
- Caller affected: its own proof, and every closed result through it.
- Restatement: keep the triple, but state in the docstring which server predicates must change and
  how (the compaction form of `reqPropOk`, `dispatchOk`, `logShape`). Better, state it now over the
  predicates that (A) introduces: see F1.2 and F1.3.

**F1.2 (Tier 1, sufficient for every caller: it takes the reader of a never-compacted store).**
- Evidence: the pre and post use `mvcc.storeReader E.s E.γ` (lines 46 and 51). That predicate
  carries `crevFrozen γ` (`InvStore.lean:3315-3319`), defined as "No compaction, ever", an invariant
  pinning the compaction revision at `-1` (`InvStore.lean:1703-1711`).
- `Compact` is the function whose purpose is to make that false. Once one compaction is applied
  (C2), no caller can produce `crevFrozen`, so no caller can call `Compact` a second time.
- `mvcc.store.Rev.spec`, which `Compact` actually needs (`s.kv.Rev()`, `v3_server.go:427`), is
  stated over `storeReaderC` (`store__Rev.lean:32-37`).
- The compactor holds whatever `R` it is given across all its calls. If `R` contains the frozen
  reader, the whole server proof with the compactor on stays inside a never-compacted store, which
  contradicts C2.
- Restatement: use `mvcc.storeReaderC E.s E.γ` in the pre and post of both `spec` and `specOn`.
  Today's callers have `storeReader_toC`.

**F1.3 (Tier 1, sufficient for the planned C3 caller: the permit is not passed into the server's state).**
- Evidence: `Compact.spec` takes no predicate about `r`. That is right for the gRPC caller. But the
  compactor's `compactableOk c P R` hands `P r` to the server, and the server's proof can only drop
  it, because `Compact.spec` has no slot to receive it.
- C3 ("`σ.compacted ≤` the revision C1 allows", plan "C3") then cannot be derived through this
  spec. The only route from the compactor's permit to the KV model is a proposal-side resource that
  the apply's compaction step receives, the way `reqPropOk`'s `Qr` / `kvOpAu` is for writes.
- The plan's design (phase 1, "The server side") says `reqPropOk`'s compaction form will be "a
  compaction at `r ≤` a revision the proposer has seen". That would make `Compact.spec`'s "any
  revision" false. It would also fail for the compactor in revision mode with a negative retention,
  which etcd accepts (`"-5ns"` via `ParseDuration`): `revPermit` then gives only `RevLb(r + ret)`,
  with `r + ret < r`.
- Restatement: parameterise the spec by a permit, `∀ (Pc : Int → IProp GF), {{ … ∗ Pc r }} … {{ … }}`,
  where `Pc r` travels with the proposal into the compaction's apply step (a `reqPropOk` compaction
  form that carries `Pc` and is unconditional in `r`). The gRPC caller instantiates `Pc := fun _ => True`.
  The compactor's glue uses `Pc := modePermit …`. Then C3 is stated over `Pc`.

**F1.4 (Tier 1 for the gRPC caller, a cited scope premise).**
- Evidence: `compactReqIs` fixes `Physical' = false` (`Defs:94`). `kvServer.Compact` passes the
  client's request (`api/v3rpc/key.go`), which may set `Physical`.
- `compactOk` (`InvAuthAdmin.lean:154-163`), the contract `kvServer.Compact.spec` takes, accepts any
  request `r`. So it cannot be discharged from `Compact.spec`.
- The scope is cited: phase 0 says "Other compactions (a client's `Compact`) stay out of the pilot's
  workload", and the docstring says the physical path is "not specified yet". So this is a known gap,
  not an error.
- `compactOk`'s post also wants `Header ↦□ h ∗ hdrW h ∗ hdrRevIn A.revR h rv`. I did not check
  whether `compactOutIs`'s `Header ↦ h ∗ h ↦ v ∗ idxCert` yields that (see uncertain points).
- Restatement, when the gRPC caller is brought in: `compactReqIs p r phys`. When `phys`, the post is
  after the `Physc` wait, and the pre adds the `bemu` reader slot that `ForceCommit` needs
  (`v3_server.go:405-416`).

**F1.5 (Tier 2, abstraction).** The post exposes `structFieldRef CompactionResponse "Header" resp ↦ h ∗ h ↦ v`
together with the store's `idxCert` and the log length. Neither caller needs the raw log: the
compactor ignores `resp`, and the gRPC caller needs `hdrRevIn`. A `revLb`-style persistent fact would
do.

**Metrics**
- Scope premises: two.
  - `Physical = false`: cited (phase 0, workload).
  - The never-compacted store, through `storeReader`: not cited, and contradicting scope (A).
- Caller burden: the compactor's glue unfolds `compactableOk`, `compactReqIs`, `compactOutIs`, and
  needs `applyErrIs → errTreeOk` plus `nil → errTreeOk`. No such lemma exists yet: `grep errTreeOk`
  finds only `Defs` and net/http's unrelated predicate.
- Law coverage: `compactOutIs` is not persistent (it holds points-to), which is fine. A lemma is
  missing: `compactOutIs E resp err ⊢ errTreeOk err`.
- Trust exposure: through the callee, the collection lists the tracing and otel axioms
  (`traceutil.Tracer.Start`, `trace.WithAttributes`, `attribute.*`, `context.WithValue`). None is
  specific to compaction.
- Testability: low. `isServerReq` is opaque, and the post's revision is decidable only with mvcc's
  model.
- Strength margin: the code returns `Header.Revision = s.kv.Rev()` read after the apply. The post
  gives a lower bound only, which is enough for the callers.

---

## 2. `Defs`: `CompactEnv`, `revGetterOk`, `errTreeOk`, `compactableOk`, `compactReqIs`, `revLb`, the permits, `compactorOk`

**Good (keep)**
- The environment is persistent contracts over a caller-chosen `R`, and the compactor's proof is
  parametric in `RevLb`, `R` and `First` (`New.spec` quantifies over every `E`). The permits
  therefore have content: the compactor must derive `RevLb (r + ret)` from `Rev()`'s results, and
  cannot invent it.
- `compactableOk`'s post carries `errTreeOk err`, the one thing the compactor inspects
  (`errors.Is(err, mvcc.ErrCompacted)`, `periodic.go:143`, `revision.go:92`). It ignores `resp`,
  and so does the code.
- `revPermit` is provable from the code (walk-through in §5). That includes `int64` wrap-around: if
  `Rev() - retention` wraps, the result is negative and is skipped by `rev <= 0`, so when `rev > 0`
  the subtraction is exact.
- `compactorOk`: `Stop`/`Pause`/`Resume` are persistent `{True}` triples. That is faithful to
  `updateLeadership` calling `Pause`/`Resume` concurrently with the goroutine (`server.go:762-785`),
  through the `RWMutex` guard in `isPeriodic` and `isLock` in `isRevision`. `Run` is once-only
  through `RunTok`.
- `compactorOk` yields the server's own `compactorOk` (`InvRun.lean:273`: `Pause`/`Resume` return),
  by dropping conjuncts.

**F2.1 (Tier 1, true, i.e. provable from the code: `perPermit`'s once-only `First` is consumed by the first compaction, but the code can compact the first sample again after a failure).**
- Concrete walk-through of `periodic.go:105-161` (full version in §5):
  - Until the window is full, `revs` is never trimmed, so `revs[0]` is always the run's first sample `v₀`.
  - The first `Compact(v₀)` with a non-full window needs the second disjunct, and so consumes `First`.
  - If that call fails with an error other than `ErrCompacted`, `lastRevision` is not updated
    (`periodic.go:150`, which runs only on success).
  - The guard `Now().Sub(lastSuccess) < baseInterval` (`:127`) cannot be used. Perennial's
    `Time.Sub` returns any duration, and `clockOk`'s `Now` gives `True`. In reality the guard
    passes anyway, because `lastSuccess` is still the start time.
  - So on the next iteration the code calls `Compact(v₀)` again, still with a non-full window. Its
    sample is only `(j+1)·retry` old on the clock, there is no `First`, and `clockLb (T₀ + period)`
    is unavailable.
- So `Periodic.Run.spec` cannot be proved with `isPeriodic`'s `compactableOk E.c (perPermit …)`.
- The claim in the docstring ("at most one compaction per run is younger than the period",
  `Defs:131-132`) is also false of the real code when the scheduling delay between `lastSuccess :=
  Now()` and the first `Rev()` exceeds `retry` (with `period = 10ns`, `retry = 1ns`). The true
  statement is "every compaction younger than the period is at one revision, the run's first sample".
- Callers affected: `Periodic.Run`'s proof, and C3, which would count compactions.
- Restatement: make the young disjunct depend on the revision, not on the call.

  ```lean
  -- CompactEnv: First : IProp GF (exclusive, once per run), FirstIs : Int → IProp GF (persistent),
  -- with laws  First ==∗ □ FirstIs v  (for any one v)  and  FirstIs v ∗ FirstIs w ⊢ ⌜v = w⌝
  -- (a one-shot ghost cell).
  def perPermit RevLb period FirstIs r :=
    ⌜0 < r⌝ ∗ ∃ T, stampAt realClock (□ RevLb r) T ∗
      (clockLb realClock (T + period) ∨ (□ FirstIs r ∗ clockLb realClock (T + retryOf period)))
  ```

  `Run`'s goroutine shoots the one-shot cell at its first sample. It can then pass `FirstIs v₀`
  again on every retry.

**F2.2 (Tier 1, sufficient for its caller `Periodic.Run`: `revGetterOk` lacks monotonicity, so the periodic proof cannot show `0 < r`).**
- `perPermit` requires `0 < r`. Unlike `revision.go` (`rev <= 0`, `:80`), `periodic.go` has no
  explicit check. It relies on `rev == lastRevision` (`:127`) with `lastRevision := 0` (`:106`)
  together with `Rev()` being monotone.
- After one success at `r₁ > 0`, a later `revs[0]` equal to `0` would pass the guard (`0 ≠ r₁`) and
  call `Compact(0)`.
- `revGetterOk` (`Defs:83-86`) gives only `RevLb v ∗ 0 ≤ v`, so the model allows `Rev()` to return
  `0` after a positive value, and `0 < r` is unprovable.
- In Go, `Rev()` is monotone and at least 1 (`kvstore.go:104`, `currentRev: 1`).
- The server can supply monotonicity. `store.Rev.spec` takes the caller's certificate `log₀` and
  returns `log₀ <+: log` (`store__Rev.lean:36-41`), and the server's `revLb` is that certificate.
- C1 as phase 0 drafted it also said "its requests' revisions never decrease". The permits dropped
  this; it is a strength margin the code meets.
- Restatement:

  ```lean
  def revGetterOk RevLb rg R := ∃ ri, ⌜rg = ok ri⌝ ∗ □ ∀ n,
    {{ R ∗ □ RevLb n }} rg.Rev() {{ v, R ∗ □ RevLb v ∗ ⌜n ≤ v ∧ 0 ≤ v⌝ }}
  ```

  This needs `RevLb 0` to start, from a law or by giving `0 ≤ v` without a bound.

**F2.3 (Tier 2, weakest pre / a mode variant that costs: `compactorOk`'s `Run` needs `First` in revision mode too).** `modePermit` ignores `First` for
`"revision"`, but `compactorOk … Run`'s pre takes `RunTok ∗ R ∗ First` in either mode. It is harmless,
since the server picks `First := True`, but the signature does not show that the token is used only
in periodic mode.

**F2.4 (Tier 2, abstraction).** `retryOf` uses Lean's `Int` `/`, which is Euclidean. It matches Go's
truncation only for positive periods. That is one reason the `10 ≤ period` premise exists (see F3.2),
and the docstring should say so, or the definitions should use `Int.tdiv`.

**Metrics**
- Scope premises: none in `Defs` itself. `isPeriodic` carries `10 ≤ period`, inherited from `New`.
- Caller burden: the server must unfold `revGetterOk` and `compactableOk` to build them from
  `store.Rev` and `Compact`. `compactorOk` must be unfolded to obtain `InvRun.compactorOk`. A lemma
  `v3compactor.compactorOk cp … ⊢ etcdserver.compactorOk cp` would remove the second.
- Law coverage: persistence is given for every predicate. Missing: `revLb_mono`
  (`revLb γ n ⊢ revLb γ m` for `m ≤ n`), which the server needs for `revPermit` with `ret ≥ 0`.
- Testability: `revPermit` is decidable given a revision trace. `perPermit` is decidable given the
  clock trace, under the intended reading (§4).
- Strength margin: monotone requests (F2.2). For revision mode, the code also guarantees
  `r = Rev() - ret` exactly, read just before the call. The permit gives `RevLb (r + ret)`, which is
  enough.

---

## 3. `v3compactor.New.spec` (`Spec/.../v3compactor/New.lean`)

**Good (keep)**
- It is a real spec in place of the old axiom whose post was `True`.
- The error disjunct is exact for invalid modes, and for a valid mode success is forced.
- A nil `lg` is handled (`compactor.go:62-64`).
- The revision mode has no premise on the retention, which matches the parser: `"-5ns"` gives a
  negative revision retention, and that is accepted.

**F3.1 (Tier 1, sufficient for `NewServer`: `compactableOk` is demanded at `New` time, which the server cannot meet; the cause is a real Go bug).**
- Evidence: `NewServer` calls `New(..., srv.kv, srv)` and then `Run()` at `server.go:383-388`,
  before `start()` sets `s.w` (`issues/etcd-compactor-started-before-start.md`). `Compact.spec`
  needs `isServerReq`, which includes `w ↦□ v.w ∗ waitInv` (`InvProposer.lean:405`).
- No restatement of `New` makes `NewServer` provable while the code races: the issue's panic is
  real. But `New` never calls `Compact` or `Rev`, so demanding `revGetterOk ∗ compactableOk` in
  `New`'s pre is stronger than `New` needs.
- Restatement: move `revGetterOk E.RevLb E.rg E.R ∗ compactableOk E.c (modePermit …) E.R` from `New`'s
  pre into `compactorOk`'s `Run` pre, which `isPeriodic`/`isRevision` could then take at `Run`.
  `New` can then be proved and called in `NewServer` as is, and only `Run` carries the obligation.
  Once the fork applies the issue's fix (start `Run` in `start()`), the server can meet it there.
  Until then `NewServer` needs a premise, and it should cite the issue.

**F3.2 (Tier 1, no unneeded premise / a premise stricter than the parser: the `10 ≤ ret` premise excludes negative periods).**
- Evidence: `parseCompactionRetention` (`embed/etcd.go:928-946`) accepts `"-1h"` via
  `time.ParseDuration`. The code then runs without panicking: retry is `-6min` and retentions is
  `11` (`periodic.go:177-189`).
- `After(negative)` fires at once, which the `clockOk` docstring already allows. Every permit is
  provable: `clockLb (T + period)` with `period < 0` follows from `stampAt_clockLb` and `clockLb_le`.
- The code needs only `|ret| ≥ 10ns`, which the docstring itself says. The old axiom's premise was
  `ret ≤ -10 ∨ 10 ≤ ret`, matching the issue file.
- "A negative period is outside the configuration" cites nothing. Phase 0 fixes "both modes, as etcd
  accepts them", with only the ≥10ns premise.
- Restatement: either `ret ≤ -10 ∨ 10 ≤ ret` (with `retryOf`/`retentionsOf` over `Int.tdiv`, F2.4),
  or keep `10 ≤ ret` and cite a new `issues/` entry. The negative-period behaviour is a busy loop that
  compacts the newest samples back to back, which makes the retention meaningless. It is a plausible
  `issues/` entry: the tiny-retention issue mentions it only as a sibling handled by upstream PR
  #22396, and no `issues/` file records it.

**F3.3 (Tier 2, strength margin).** For an invalid mode the code always returns an error, but the post
also allows the success disjunct. No caller needs the stronger form.

**Metrics**
- Scope premises: 1. `10 ≤ ret` for periodic mode cites phase 0 and the issue for `|ret| < 10`; the
  negative half is uncited (F3.2).
- Caller burden: `NewServer` must build `compactableOk` and `revGetterOk` (F3.1). That means
  unfolding both, plus `modePermit` case analysis by mode.
- Trust exposure: `clockwork.NewRealClock.wp_proof`, `zap.NewNop`, `fmt.Errorf`,
  `context.WithCancelBackground` (the collection).
- Testability: high for the mode dispatch and error. The permits are tested through §2.

---

## 4. The clock: `CDefs` and `clockwork.NewRealClock.spec`

**Good (keep)**
- The axioms chain. `After` takes any `clockLb n` the caller holds and returns `T ≥ n`, so `k` waits
  give `clockLb (n + k·d)`, and `stampAt_clockLb` links a stamp to the chain. The "bounds that cannot
  be chained" pattern does not apply.
- `stampAt_intro` is deliberately absent: a stamp is minted only by `After`. That is the right
  discipline.
- The stamp is of `□ P` with `P` chosen by the caller. With `P := RevLb v` it matches `perPermit`'s
  `stampAt realClock iprop(□ RevLb r) T` syntactically, so no properness law is needed.
- The model is true of clockwork v0.5.0's real clock. `realClock.After` is `time.After`, which by
  the monotonic clock fires no earlier than `d` after the call, and `Now` is not relied on.

**Trivial model (checked).** `clockLb := True` and `stampAt P T := □ P` satisfy every axiom:
`clockLb_init`, `clockLb_le`, `stampAt_elim` (`□P ⊢ P`), `stampAt_clockLb`, the persistence
instances, and `NewRealClock.spec`, whose channel invariant becomes `True`. The docstring states this
and says that the time content is the intended reading.

**Is the "How to read results" paragraph adequate?** Mostly, yes. It is honest, and no Iris-level
axiom set can do better without time in the operational semantics. Suggested additions, all Tier 2:

**F4.1 (Tier 2).** Say what survives the trivial model. Read trivially, `perPermit` collapses to
`0 < r ∗ □ RevLb r` ("the store had reached `r`"), so the Lean result still guarantees that
much. Only the age is the trust boundary. A reader then knows which part of C1 is checked by Lean and
which is not.

**F4.2 (Tier 2, testability).** Name the test that covers the intended reading. The reading is the
only evidence for the time content, so phase 2 should instrument the clock (a wrapper over
`NewRealClock` that logs the monotonic reading at each `After` call and channel receive) together
with `Compact` calls, and check C1's age in real time. This is the stated metric: "trust exposure …
and whether a tester covers them".

**F4.3 (Tier 2, implementation independence).** `clockOk`'s `Now` gives `True`. That is enough
today, because no proof can use `Now` given Perennial's `Time.Sub`. It is the reason
`perPermit` has a young disjunct at all (F2.1). Say so in `CDefs`, so a later strengthening (`Now`
returning a `clockLb`/upper-bound pair and `Sub` specified) is seen as what would let the
`lastSuccess` guard be used.

**Metrics**
- Trust exposure: 3 opaque axioms (`realClock`, `clockLb`, `stampAt`), 2 instance axioms, 4 law
  axioms, and `NewRealClock.wp_proof`. The tcb baseline lists only the first three and the spec
  axiom, because no proof uses the laws yet.
- Testability: none inside Lean. Testing needs the instrumented clock (F4.2).
- Laws: persistent, monotone (`clockLb_le`), elimination and stamp-to-bound. No agreement or
  fraction is needed.

---

## 5. `Periodic.Run.spec`, `Revision.Run.spec`

**Good (keep).** Both take the exclusive resources the goroutine needs. `Periodic` takes
`periodicRunTok` (the `revs` field and an `RWMutex` reader slot) plus `E.R ∗ E.First`. `Revision`
takes `E.R`; it keeps nothing of the object, so it needs no token. The posts are `True`, which is
right for a launcher.

**Walk-through: `Revision.Run` (`revision.go:65-108`), provable.**
1. `clockLb_init` gives some `n`. Each `After(5min)` needs nothing more, and its value is not used.
2. `Rev()` returns `v` with `□ RevLb v`.
3. `rev := v - ret`. If `rev <= 0`, the iteration continues. Otherwise there was no wrap-around
   (argued in §2), so `RevLb (rev + ret) = RevLb v`, and `revPermit` holds.
4. `rev == prev` does not matter for the permit.
5. `Pause` goes through `isLock` and `ctx.Done` through `isContext`.

There are no findings for `Revision.Run.spec`.

**Walk-through: `Periodic.Run` (`periodic.go:100-163`).**

Loop invariant: `revs = [v_{j-L+1} … v_j]` with `L = min(j+1, retentions)`. Each `v_k` has `□ RevLb v_k`
and `stampAt (□ RevLb v_k) T_k`, with `T_{k+1} ≥ T_k + retry`, and after the receive the goroutine
holds `clockLb (T_j + retry)`.

One iteration:
1. Sample: `Rev()` gives `v_j`.
2. Goose evaluates `ctx.Done()` and then `After(retry)`, with `P := RevLb v_j` and
   `n := T_{j-1} + retry`. This gives `T_j ≥ n` and the stamp.
3. Receiving from the `After` channel gives `clockLb (T_j + retry)`.
4. `Paused` (via the reader slot) or the `Now` guard both lead to `continue`. The bound carries over.

Cases at a compaction:
- **Full window.** `L = retentions = ⌊period/retry⌋ + 1`, so `L·retry > period` (because
  `retry ≥ 1` when `period ≥ 10`). Then `clockLb (T_{j-L+1} + period)`, and the first disjunct
  holds. ✓
- **Non-full window, first call.** `revs[0] = v₀`, and `clockLb (T₀ + retry)` holds, so the second
  disjunct holds with `First`. ✓
- **Non-full window, retry after a failed call.** The call is again at `v₀`, but `First` is gone.
  ✗ (F2.1)
- **`0 < r` after a success.** This needs monotone samples. ✗ (F2.2)

So `Periodic.Run.spec` is unprovable as its `isPeriodic` is stated. Both F2.1 and F2.2 are needed to
fix it.

The spec files themselves need no change beyond what `isPeriodic` inherits. Since `isPeriodic`'s
docstring is package-internal, I note only that it exposes fields, which is fine at this layer.

**Metrics.** No scope premises. Trust exposure is the clock (§4) plus `errors.Is` and zap.

---

## Ranking (most to least in need of revision)

1. **`EtcdServer.Compact.spec`/`specOn`.**
   - F1.1: unprovable over the current callee.
   - F1.2: a frozen store reader, which contradicts its own purpose.
   - F1.3: no slot for the permit, so C3 cannot be derived, and the planned `r ≤ seen` form
     conflicts with "any revision".
   - F1.4: the gRPC caller, under a cited scope premise.
2. **`Defs`: `perPermit` and `revGetterOk`.**
   - F2.1: the once-per-run `First` is false of the code's retry path. Restate it per revision.
   - F2.2: `Rev` needs monotonicity for `0 < r`.
   - These make `Periodic.Run` unprovable.
3. **`New.spec`.**
   - F3.1: the environment contracts belong in `Run`'s pre. `NewServer` is blocked by the real bug
     `etcd-compactor-started-before-start`.
   - F3.2: the negative-period premise is uncited and not needed by the code.
4. **The clock trust boundary.** It is adequate. Add F4.1 to F4.3 to the reading paragraph and name a
   tester.
5. **`Periodic.Run.spec`, `Revision.Run.spec`.** These are fine as stated. Periodic's problems are in
   `Defs`.

## Possible Go issue to record (not in `issues/`)

- **Negative periodic retention** (`--auto-compaction-retention=-1h`, accepted by
  `parseCompactionRetention`).
  - The retry interval becomes negative, so `clock.After` fires at once, and the loop busy-spins.
  - `getRetentions` is `11`. After the first period-check passes (or whenever `Now().Sub(lastSuccess) <
    baseInterval` with a negative `baseInterval` is false, which is always), it compacts at a sample
    taken microseconds earlier. The retention is effectively zero, and the loop burns CPU.
  - It is not a panic. Upstream PR etcd-io/etcd#22396 (open) would reject it.
  - It is mentioned only as a sibling in `issues/etcd-compactor-periodic-tiny-retention.md`. It
    deserves its own file if the spec keeps excluding it (F3.2).
- I did not reproduce it with a Go test.

## Uncertain points (not verified)

- **`compactOk`'s header facts.** Whether `compactOutIs`'s `Header ↦ h ∗ h ↦ v ∗ idxCert …` yields the
  gRPC contract's `hdrW h ∗ hdrRevIn A.revR h rv`. Settled by reading `hdrW`/`hdrRevIn` in `InvKV.lean`.
- **`applyErrIs ⊢ errTreeOk`, and `errTreeOk nil`.** I found no lemma. Settled by reading
  `applyErrIs`'s definition against `errTreeOk`'s.
- **Persistent pieces `NewServer` holds at line 383.** Whether its proof holds, at that point, the
  persistent parts of `R` (`srvLeadTimeReader` slot, `isReadView` of `srv.kv`, `E.RD`) other than
  `isServerReq`/`waitInv`. The Lean assembles `isServerReq` late (`NewServer.lean:1346`). Settled by
  reading `NewServer.lean` around 560-660.
- **`isChanBag`.** Whether its invariant is persistent and lets every receive (not just the first)
  carry `clockLb (T + d)`, as the chaining argument assumes. Settled by `Perennial/Golang/Theory/Chan/Idioms/Bag`.
- **The Lean mvcc model's revisions.** In the Lean model a fresh store's `Rev()` might be `0`
  (`v = |log| - 1`, "revision 0 is the empty store's", `Defs:73`), while Go's is `1`. If so, F2.2's
  alternative fix (`1 ≤ v`) is not available, and monotonicity is the right one.
- **Lean `Int` division.** I believe it is Euclidean (F2.4), but did not check it against the pinned
  Lean.
