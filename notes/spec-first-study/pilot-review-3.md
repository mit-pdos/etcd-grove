# Spec review, round 3: the compactor pilot (worktree /shared/etcd-grove-cp, branch compactor-pilot, at ef14a41371)

Reviewer: spec-reviewer (fresh, read-only). Read: CLAUDE.md, .claude/skills/spec-repair/LESSONS.md,
notes/spec-first-plan.md "Phase 1b" (same criteria as the agent file; the plan adds the metrics table, no
conflict), notes/compactor-pilot-plan.md up to "Step 2b" (not beyond; one line of the round-2 table showed up
in a grep: "a permit `Pc r` travels with the proposal"). Diff checked: `git diff 15bcad5f28 ef14a41371 -- Spec Proof`.
Go: v3compactor/{compactor,periodic,revision}.go, v3_server.go:382-431, server.go:375-389/560-575/755-790/950-960,
embed/etcd.go:928-947, api/v3rpc/key.go:139-151, clockwork v0.5.0 clockwork.go:27-63.
Nothing was built. Every `wp_proof` of the targets is still `sorry` (New included), so no glue has checked
any of the claims below; the walks are by hand.

## Summary of blockers (Tier 1)

1. **`periodicRunTok` gives no ownership of the `revs` slice** (not changed since round 1, so earlier rounds
   missed it): `Periodic.Run` cannot be proved, and its triple as stated is not true of the code.
2. **`EtcdServer.Compact`'s per-call permit `Pc` is vacuous** (the round-2 repair): `∀ Pc`, in the pre only,
   so the statement equals the one with `Pc := fun _ => True`. C1's permit still never gets past the boundary,
   and C3 cannot be derived from a permit each caller picks for itself.
3. **`New`'s `Run` contract cannot be met by `NewServer` at server.go:388.** This comes from the Go bug
   already in `issues/etcd-compactor-started-before-start.md`, not from a flaw in the spec. No spec can fix
   it. Recording the decision (a fork fix, or the compactor off) is now on the critical path for scope (A).
4. **`Compact.spec` cannot serve the gRPC caller, and its callee cannot accept a compaction.** Expected for
   phase 1, but these are open sufficiency failures, listed so they are not mistaken for done.

---

## Target 1: `Periodic.Run` (Spec/.../v3compactor/Periodic__Run.lean) with `isPeriodic`, `periodicRunTok`, `perPermit`, `firstSample`/`firstUnset`

### Good (keep)
- Moving the environment's contracts out of `isPeriodic` and into `runPre`, given at `Run` (diff: Defs.lean,
  isPeriodic). `New` calls neither `Rev` nor `Compact`, so `New` no longer takes contracts the server cannot
  give at that point.
- The first-sample exception now depends on the value (`firstSample γf r`, a discarded `dghostVar`), not on
  the call. I walked the retry path: a failed `Compact` (periodic.go:152-159) leaves `lastRevision`. The next
  iteration appends a sample. While `k < R-1` (R = retentions), `revs[0]` is still `s_0`, and the persistent
  `firstSample γf s_0` covers the retry. Once the window has filled, `revs[0]` slides to a later sample with a
  full window. Pause (periodic.go:119-124, `continue` back to the append) keeps sampling and keeps the bounds.
  I find no path that spends anything once-only.
- The chaining works. `After` takes `clockLb n` and returns `T ≥ n`, a stamp at `T`, and a channel carrying
  `clockLb (T+d)`. Loop invariant: sample `s_j`, stamped at its `After` (`T_j`), and after the k-th receive the
  clock has reached `T_j + (k-j+1)·retry`. Full window: `j = k-R+1`, so R waits, and
  `R·retry = (⌊period/retry⌋+1)·retry > period`, which gives `clockLb (T_j + period)`. Before the window
  fills: `revs[0] = s_0` after at least 1 wait, which gives `clockLb (T_0 + retry)`. This holds for every
  period ≥ 10ns (retry ≥ 1).
- `0 < r` holds on every path. `lastRevision` starts at 0, and `rev == lastRevision` skips (periodic.go:127).
  Samples are ≥ 0 and nondecreasing (`revGetterOk`'s new `n ≤ v`). So a `rev = 0` implies `lastRevision = 0`,
  and the iteration is skipped. The round-2 monotonicity premise is what this needs, and the server can give
  it (see Target 4).
- "At most one revision per run younger than the period" is true of the code. In fact the code is stronger:
  `s_0` is compacted only after `Now()-lastSuccess ≥ period` (periodic.go:107,127), but `Time.Sub` has no
  usable spec, so the weaker statement is the provable one.

### Findings
**F1.1 (Tier 1: true of the code / sufficient for the caller `New`).** `periodicRunTok pc`
(Defs.lean:208-210) holds `∃ s : GoSlice, revs ↦ s` and nothing about `s`: no `s ↦* vs`, no
`ownSliceCap`, and no statement that `s` is empty. `Run`'s goroutine does
`pc.revs = append(pc.revs, pc.rg.Rev())` and `rev := pc.revs[0]` (periodic.go:110,126).
- Perennial's `wp_slice_append` (Perennial/Golang/Theory/Slice.lean:1297) needs
  `sl ↦* vs ∗ ownSliceCap V sl (DFrac.own 1)`, and indexing needs `s ↦* vs`.
- With an arbitrary `s`, `revs[0]` can also be a stale positive value that has no stamp, so the call to
  `Compact` at it has no `perPermit`.
- The real state is fine: `newPeriodic` sets `revs = make([]int64, 0, R)` (periodic.go:60). Its spec's post
  (newPeriodic.lean, `periodicRunTok pc`) throws away the ownership and the emptiness.

Restatement:
```lean
def periodicRunTok (pc : Loc) : IProp GF :=
  iprop((∃ s : GoSlice, structFieldRef v3compactor.Periodic go!"revs" pc ↦ s ∗
          s ↦* ([] : List w64) ∗ ownSliceCap w64 s (DFrac.own 1)) ∗
    sync.ownRWMutex (structFieldRef v3compactor.Periodic go!"mu" pc) (perPausedInv pc))
```
`newPeriodic`'s post then gives it, from `make`.

**F1.2 (Tier 2: no unneeded premise, size).** `runPre` (Defs.lean:176-178) always contains
`firstUnset E.γf`, so the revision mode's `Revision.Run` and `New`'s revision branch also consume a ghost
variable they never use. Any caller can allocate one, so no caller is excluded. Option: move `firstUnset` into
`perPermit`'s side, e.g. `periodicRunPre E period := runPre' E (perPermit …) ∗ firstUnset E.γf`, with
`modePermit` choosing.

**F1.3 (Tier 2: law coverage).** `firstSample` has no exported persistence instance (only `perPermit`'s
instance unfolds it) and no agreement law (`firstSample γf r ∗ firstSample γf r' ⊢ ⌜r = r'⌝`). The
agreement is exactly what C3 needs to turn "at most one young revision" into a statement. `revPermit` has no
`Persistent` instance (`perPermit` has one), and neither does `modePermit`. A server proving `compactableOk`
by way of `Compact.spec`'s `□ Pc r` with `Pc := modePermit …` needs them (see F4.1 for why it can pick
`True` instead).

### Metrics
- Scope premises: 0 in `Run` (period ≥ 10 comes in through `isPeriodic`; see F2.2).
- Caller burden: N/A (New's glue is `sorry`).
- Trust exposure: clockwork's `clockLb`, `stampAt`, `realClock`, `clockLb_init`, `clockLb_le`, `stampAt_clockLb`,
  `stampAt_elim`, `NewRealClock.wp_proof` (the collection's baseline lists only the first three plus
  `NewRealClock` while proofs are `sorry`). No tester yet.
- Testability: `0 < r` and the window arithmetic are decidable. The clock part is testable only under an
  instrumented clock (Defs.lean header).
- Strength margin: the code guarantees `T + R·retry` (> period), compaction revisions that never decrease
  (phase 0's C1 third bullet, not in `perPermit`), and in real time `s_0` at about `period` old. None is needed
  until C3 is stated.

## Target 2: `New` (+ `newPeriodic`, `newRevision`, `compactorOk`, `CompactEnv`, `modePermit`)

### Good (keep)
- The post's two disjuncts are exhaustive and exclusive on a valid mode: the right one needs an invalid mode,
  so a valid mode gives the left. A nil `lg` is handled through `zap.NewNop`'s `l ≠ null`.
- `compactorOk` gives the server's `InvRun.compactorOk` (InvRun.lean:275: nil, or `Pause`/`Resume` return)
  and `Stop` (server.go:959). The `Pause`/`Resume` contracts are persistent and need nothing, which fits the
  calls from `updateLeadership` (server.go:766-781) concurrent with the goroutine (`isRWMutexGuard`/`isLock`
  persistent, the goroutine holding only a reader slot).
- The glue: periodic. `RunTok := periodicRunTok pc`, `isPeriodic` captured in the `□`, and `modePermit
  "periodic"` reduces to `perPermit … (sint.Z ret)`, which equals `Periodic.Run`'s `period = sint.Z h`.
  Revision: `int64(retention)` gives the same `sint.Z`, `modePermit "revision" = revPermit`. Both match by
  hand (not machine-checked).

### Findings
**F2.1 (Tier 1: sufficient for every caller; the caller is `NewServer`, server.go:383-388).** `NewServer` calls
`srv.compactor.Run()` before `start()`. `Run` needs `runPre`, whose `compactableOk srv P R` the server can
give only through `Compact.spec`, which needs `isServerReq s E ρ`. That has `w ↦□ v.w ∗ waitInv …`, and `s.w`
is written in `start()` (server.go:570). The proofs build `isServerReq` in `EtcdServer.start`
(EtcdServer__start.lean:449). The code really can call `Compact` before `start()`:
- revision mode: after 5 minutes on the clock;
- periodic mode: after a `Time.Sub` comparison with no spec;
- in both cases the call races with, or nil-dereferences, `s.w`.

So no `R` makes this sound. The plan's option 3b ("a contract whose resource waits for `Start`") is
impossible. This is `issues/etcd-compactor-started-before-start.md`, whose "How the proof handles it" section
is now stale (it describes N0's `{True} Run {True}`). Restatement: none inside these specs. The choices are:
- (a) a fork fix: move `srv.compactor.Run()` into `start()`, as the raft fixes are carried in the fork;
- (b) `NewServer` keeps `AutoCompactionRetention = 0`, and C2 is dropped from scope (A).

Decide before the `NewServer` glue, and update the issue's proof section.

**F2.2 (Tier 1, minor: no unneeded premise / premise stricter than the parser).** `mode = "periodic" → 10 ≤ ret`
(New.lean). etcd accepts negative periods (`time.ParseDuration`, embed/etcd.go:940), and the code runs with
them without panicking. It busy-loops with zero effective retention, but a WP is partial correctness.
- `issues/etcd-compactor-periodic-tiny-retention.md` itself says the true statement needs only
  `ret ≤ -10 ∨ 10 ≤ ret`.
- Phase 0's C2 draft says "for any accepted retention", so this premise excludes configurations C2 claims.
- With a negative period, `perPermit`'s full-window clause is trivial (`clockLb T` from `stampAt_clockLb`,
  plus `clockLb_le`). The proof would be cheap.

The docstring cites the issue and etcd-io/etcd#22396 (which would reject negative retentions), so this is a
documented scope choice, not an uncited one. Restatement if kept general:
`mode = go!"periodic" → sint.Z ret ≤ -10 ∨ 10 ≤ sint.Z ret`, with `retryOf` in Go's truncating division
(`Int.tdiv`; Lean's `/` on `Int` is, I believe, Euclidean, which differs on negatives: uncertain) and
`isPeriodic`'s `10 ≤ period` relaxed likewise. Otherwise, record the narrowing as a phase-0 decision that
also narrows C2.

**F2.3 (Tier 2: abstraction, size).** The unfolded post nests `compactorOk` > `runPre` > `revGetterOk`,
`compactableOk` (with `context.ContextDesc`, `compactReqIs`'s points-to), and `modePermit` > `perPermit`
(clock stamps, `dghostVar`). It also exposes a ghost name (`E.γf`) and `CompactEnv`'s `R`. The server needs
`γf` for C3, so exposing it is justified. The rest is large but each piece is used.

**F2.4 (Tier 2: coupling).** The compactor's `Defs.lean` imports `mvcc.InvIndex` only for `revLb`, which is
the server's instantiation of `RevLb`, not the compactor's vocabulary. `Compact.spec` (server) imports
`v3compactor.Defs` for `compactReqIs` (an `etcdserverpb` request shape), so the dependency runs backwards.
`clockwork/Defs.lean` imports the server's `BaseApply` (for the init instance), so the clock's trust boundary
depends on the server. Suggest moving `revLb` to the server side (or mvcc's API), `compactReqIs` to an
etcdserverpb/server module, and the clockwork `IsPkgInit` instance out of `BaseApply`.

### Metrics
- Scope premises: 1 (`periodic → 10 ≤ ret`). It cites phase 0 and an issue, but see F2.2.
- Caller burden: N/A (NewServer has the compactor off; New's proof is `sorry`).
- Law coverage: `compactorOk_persistent` is present. Persistence of `revPermit`/`modePermit` is missing (F1.3).
- Trust exposure: the clock axioms (Target 5) and `NewRealClock.wp_proof`. `zap.NewNop`, `fmt.Errorf`.
- Testability: the mode/error split is decidable. Everything else is resource-level.
- Strength margin: `cp` is the periodic or revision object (not needed).

## Target 3: `Revision.Run` (Spec/.../v3compactor/Revision__Run.lean) with `isRevision`, `revPermit`

### Good (keep)
- `revPermit` is true on every path. `rev := Rev() - retention` (revision.go:81) is computed in w64. `Rev()`
  is ≥ 0, so subtracting a positive retention cannot underflow. A negative retention (reachable:
  `"-5ns"`, embed/etcd.go:940) that overflows wraps to a negative `rev`, which `rev <= 0` skips. So whenever
  `rev > 0`, `sint.Z rev + ret = sint.Z (Rev())`, and `□ RevLb (r + ret)` is `Rev()`'s own `RevLb v`. There
  is no premise on the retention's sign, as it should be.
- Retries (a failed `Compact`, `prev` unchanged) recompute from a fresh `Rev()`. Nothing is once-only.
  Pause goes through `isLock`.

### Findings
- F1.2 applies (`firstUnset` is consumed for nothing).
- **Observation (not a spec defect).** A negative revision retention makes the compactor ask every 5 minutes
  for a compaction at a future revision (`Rev() + |ret|`), which the apply refuses (`ErrFutureRev`). That is a
  misconfiguration, not a panic. etcd-io/etcd#22396 (linked from the tiny-retention issue) would reject it. I
  did not create an `issues/` entry. Low value: at most a line in the existing issue.

### Metrics
- Scope premises: 0.
- Trust exposure: clock (`After` only, its bounds unused).
- Testability: `revPermit`'s pure part is decidable.
- Strength margin: monotone revisions, `rev ≠ prev` (not needed).

## Target 4: the environment contracts (`revGetterOk`, `compactableOk`, `errTreeOk`, `compactReqIs`, `revLb`, `runPre`, `CompactEnv`)

### Good (keep)
- `revGetterOk`'s round-2 strengthening (`∀ n, {{R ∗ □ RevLb n}} Rev() {{… n ≤ v ∧ 0 ≤ v}}`) can be instantiated
  from `mvcc.store.Rev.spec` with `RevLb := revLb E.γ.idx` and `R ⊇ storeReaderC`:
  - from `revLb n`, take its `idxCert log₀`, with `m = 0`;
  - the post gives `log₀ <+: log`, `log ≠ []`, `v = |log|-1` (and `|log|+3 ≤ 2^63`, so there is no wrap);
  - therefore `n ≤ |log₀|-1 ≤ v`, `0 ≤ v`, and `revLb v`.
  
  It uses the compaction-aware reader, so it does not contradict compaction.
- `compactableOk`'s post carries `errTreeOk err`, which the compactor inspects (`errors.Is(err,
  mvcc.ErrCompacted)`, periodic.go:143, revision.go:93), and it ignores `resp`, which the compactor discards.
  This is the right strength.
- Both contracts are persistent, and the resource `R` is per thread. That fits the compactor's goroutine
  running concurrently with gRPC handlers on the same server.

### Findings
- **F4.0 (uncertain).** `□ E.RevLb 0`: the server must give `revLb γi 0`, an `idxCert` of a nonempty log, at
  `Run`. This is plausible (every `Rev` post has `log ≠ []`) but I did not find where the server holds one.
- **F4.0b (uncertain).** `errTreeOk GoInterface.nil` must be proved on the success path (the post is
  unconditional). It looks provable (`S := (· = nil)`, so `TreeTyped` is vacuous), and `applyErrIs`'s
  `ptrTarget target →` must be matched with `errTreeOk`'s `∀ tii, … IsPointerError tii →`. That is small glue,
  not checked.
- **Not a finding.** The pattern "a contract with no resource over a callee that needs one" does not apply:
  `R` is threaded through both contracts.

## Target 5: the clock's trust boundary (Proof/github_com/jonboulle/clockwork/Defs.lean, NewRealClock.lean)

### Good (keep)
- True of clockwork v0.5.0: `NewRealClock` returns `&realClock{}`, whose `After` is `time.After` and whose
  `Now` is `time.Now` (clockwork.go:27-43). Go's timers use the monotonic clock. The stamp is taken at the
  `After` call of a fact held before it, which is sound.
- Chainable: `After` takes the caller's `clockLb n` and returns `T ≥ n`. A negative `d` is consistent
  (`clockLb (T+d)` follows from `stampAt_clockLb` and `clockLb_le`).
- The family is consistent: the model `clockLb := True`, `stampAt P T := □ P` satisfies every axiom (note that
  `stampAt P T := P` would not, because `stampAt_persistent` holds for every `P`).
- The header now says what survives that trivial model (the store reached `r`) and that the time content is
  the trust boundary, to be tested in phase 2. That is the honest statement.

### Findings
- **F5.1 (Tier 2: trust exposure, noted rather than required).** As the header admits, no Lean result
  distinguishes the intended reading from the trivial one. To carry information, the family would need an
  upper-bound or authoritative element (e.g. a `clockNow γc t` that only an atomic `After`/`Now` step can read,
  with `clockLb γc n ∗ clockNow γc t ⊢ ⌜n ≤ t⌝`), so that `stampAt` could not be made with a `T` larger than
  the true reading. The present form is acceptable as documented. Phase 2's instrumented-clock test is then
  the only check of it.
- **F5.2 (Tier 2: coupling).** The `BaseApply` import (F2.4).

### Metrics
- Axioms: 8 in Defs, plus `NewRealClock.wp_proof` and `opaqueInitsOk` (Init). Tester: none yet.
- Testability: lower bounds and stamps, checkable against an instrumented monotonic clock.

## Target 6: `EtcdServer.Compact` (Spec/.../etcdserver/EtcdServer__Compact.lean: spec, specOn, compactOutIs)

### Good (keep)
- Both modes are present (`spec`, `specOn` over `isServerReqM true`).
- `storeReaderC` (not `storeReader`) is right: `Compact` ends with `s.kv.Rev()` (v3_server.go:427) on a store
  that this very call may compact (the round-2 repair is correct).
- `compactOutIs` matches the code's two exits:
  - `err` set: `nil` response (v3_server.go:416-421);
  - otherwise: a response whose header has been allocated if missing and is set to `s.kv.Rev()`
    (v3_server.go:422-427).
- The resources given back (`srvLeadTimeReader`, `E.RD`, `storeReaderC`) are what the compactor's `R` must
  hold for both `Rev` and `Compact`, and `idCred` is pure. So `R := isServerReq … ∗ srvLeadTimeReader s ∗ E.RD
  ∗ storeReaderC E.s E.γ`, with `RevLb := revLb E.γ.idx`, satisfies `revGetterOk` and `compactableOk` with the
  same `R` (after `start()`, see F2.1).

### Findings
**F4.1 (Tier 1: no unneeded premise; "Repairs introduce defects").** `Pc : Int → IProp GF` is universally
quantified, occurs only in the precondition (`□ Pc r`), and appears in neither the post nor any parameter of
`isServerReq s E ρ`. A spec `∀ Pc, {□ Pc r ∗ …} … {Q}` is equivalent to its instance at `Pc := fun _ => True`.
- **What the statement does not say.** The docstring says "the permit travelling with the proposal … C3 is
  derived from it". The statement says nothing of the kind.
- **It cannot later be made to say it.** Each caller chooses its own `Pc` per call (the docstring: the gRPC
  caller's is `True`), so the apply side cannot learn anything from "this compaction came with some caller's
  `Pc r`".
- **The server can drop C1 today.** To prove `compactableOk srv (modePermit …) R` it can instantiate
  `Pc := True` and throw away the compactor's `P r`.

So C1 still stops at the server boundary, and the round-2 finding is not repaired. Restatement:
- Make the permit a server-wide parameter fixed at `NewServer`, e.g. a field `CP : Int → IProp GF` of the
  server's environment (or of `ρ`) that `isServerReq` is indexed by. `Compact`'s pre is then `□ E.CP r`, and
  the compaction form of `reqPropOk` records it (C3: every applied compaction `r` has `CP r`, given that only
  the compactor and callers who can show `CP` compact).
- The gRPC handler's `compactOk` then either supplies `CP r` or C3 carries phase 0's premise "only the
  compactor compacts".
- If C3's shape is not decided yet, drop `Pc` now rather than keep a parameter that promises something.

**F4.2 (Tier 1, expected for phase 1: sufficient for the callee).** The callee
`processInternalRaftRequestOnce.spec` needs `reqPropOk ρ.kv rq Qr`. Every disjunct of that requires
`plainReq rq`, hence `putgetKind (dispatchKind rq)`, and that excludes `.compaction`
(KVModelDefs.lean:114-120, InvRequest.lean:1280-1295). `Compact`'s glue cannot be proved until the callee's
spec gets a compaction form. The plan names this ("reqPropOk's compaction form"), but nothing yet tracks it as
a `Compact` blocker. It is also where F4.1's permit must land.

**F4.3 (Tier 1, documented gap: sufficient for every caller; the caller is the gRPC handler).**
`v3rpc.kvServer.Compact.spec` takes `v3rpc.compactOk s E A Pin ctx r Q` (InvAuthAdmin.lean:154-163). That
premise is currently discharged by no one, and it is stated for any request `r`. `Compact.spec` cannot
discharge it:
- (i) `compactReqIs p r` fixes `Physical' = false`, but clients can send `physical: true`, which takes the
  `<-result.Physc` / `ForceCommit` path (v3_server.go:402-415, `s.bemu`, `s.be`), with no spec;
- (ii) `compactOk` asks for `Header ↦□ h ∗ hdrW h ∗ hdrRevIn A.revR h rv`. `compactOutIs` gives
  `Header ↦ h ∗ h ↦ v ∗ idxCert log` with `v.Revision = |log|-1`. Whether that yields `hdrRevIn A.revR` is
  uncertain;
- (iii) `Pin` must hold `isServerReq`, `srvLeadTimeReader`, `storeReaderC`, and `compactReqIs` ownership of
  the client's request.

The docstring says the physical path is "not specified yet". Restatement: add `Physical` as a parameter
(`compactReqIs p r phys`), with the `Physc` wait under `phys = true`, before the server's gRPC closed theorem
needs `compactOk`.

**F4.4 (uncertain).** `Compact`'s own `s.kv.Rev()` needs `s.kv`'s `isReadView`/`ReadView ↦□` facts and the
link from `s.kv` to `E.s`, presumably inside `isServerReq`'s `srvIndexInvs`/`kvInv`. Not checked. The same
holds for the compactor's `revGetterOk` on `srv.kv`: a `*watchableStore` whose `Rev` is promoted from the
embedded `*store`, which needs the promoted-method dispatch to have a spec.

### Metrics
- Scope premises: 1 (`Physical' = false`, cited as the pilot's scope; see F4.3).
- Caller burden: N/A (no glue yet).
- Law coverage: `compactOutIs` is not persistent (it has points-tos), which is fine.
- Trust exposure: through `processInternalRaftRequestOnce`, the server's usual set (the collection's baseline
  lists it).
- Testability: `compactOutIs`'s pure part (`resp`/`err` split, the header revision).
- Strength margin: on success the code also guarantees that the compaction was applied (`result.Err = nil`), in
  the KV model. Not stated (C2/C3 pending), as the docstring says.

---

## Ranking (most to least in need of revision)

1. **`EtcdServer.Compact`**: F4.1 (vacuous `Pc`, the round-2 repair), F4.2 (callee cannot take a compaction),
   F4.3 (gRPC caller).
2. **`Periodic.Run` / `newPeriodic` / `periodicRunTok`**: F1.1 (unprovable as stated; a simple fix).
3. **`New`**: F2.1 (a NewServer sufficiency failure decided by the Go bug, needing a scope decision, not a spec
   edit), F2.2 (negative periods), F2.3-2.4.
4. **`Revision.Run`**: only F1.2.
5. **Environment contracts (`revGetterOk`, `compactableOk`, `errTreeOk`)**: fine. Laws missing (F1.3).
6. **Clock trust boundary**: acceptable as documented (F5.1 is a preference).

## Uncertain points (what would settle each)
- F2.2: whether Lean's `/` on `Int` is Euclidean (`Int.ediv`) in this toolchain. It matters only if negative
  periods are admitted. Check `#check (Int.instDivInt)` / `Int.div_def`.
- F4.0: where the server gets `revLb γi 0` (an `idxCert` of a nonempty log) at `Run`.
- F4.0b: `errTreeOk GoInterface.nil`, and `ptrTarget` vs `∀ tii, … IsPointerError`. Write the two-line lemma.
- F4.3 (ii): whether `compactOutIs`'s header gives `hdrRevIn A.revR h rv`. Read `hdrRevIn` and `KVAns.revR`.
- F4.4: the promoted `watchableStore.Rev` dispatch spec, and `isServerReq`'s link from `s.kv` to `E.s`.
- The New glue (the periodic/revision branches matching `modePermit` by `if` reduction on `GoString`
  equality) was walked by hand only.
- Go bugs: none new. F2.1 is `issues/etcd-compactor-started-before-start.md`, whose "How the proof handles it"
  section is stale. The negative-revision-retention behavior (Target 3) is a misconfiguration covered in
  spirit by the tiny-retention issue's link to #22396. I did not create an entry.
