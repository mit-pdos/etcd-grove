## time (S4 part): the runtime's timers and clock readings as a Go model

Branch `goose-model-overlay-rest-time` (Perennial), base `lean` 54a29571e. Commits: 02ff0ea6c (CheckAPI
ignores parameter names), 634fd62a0 (`gomodel.Choose`/`ChooseUint64` specs), 4262a17cd (the model),
then the proof port and `etc/model-tests.sh` (b3ff0ab29 proofs, 0df729ac4 model-tests, 022db9a06 a context doc line; head 022db9a06, pushed).

### What became Go
- **Real Go, translated (unchanged from before):** `Timer.Stop`, `Timer.Reset`, `AfterFunc`, `goFunc`,
  `when`, `Now`, `Since`, `Until` and the `Time`/`Duration` arithmetic.
- **Go models** (`goose/model/overlay/time/{time,sleep,tick}.go`, `[model].replaces`), each with a
  `MODEL:` comment quoting the real Go: `runtimeNow` (= `now()`), `runtimeNano` (`now()`'s mono, a
  non-positive one replaced by 1), `runtimeIsBubbled` (`gomodel.Choose`), the runtime's `newTimer`,
  `stopTimer`, `resetTimer`, and `NewTimer`, `After`, `NewTicker`, `Ticker.Stop`, `Ticker.Reset`.
  Additions (translated, no claim of their own): `makeTimerChan` (cap 0 or 1: `Choose`), `sendTimes`
  (blocking send of `Now().Add(-delta)`), `timerFunc` (calls `f(arg, seq, delay)` with
  `ChooseUint64`s), `checkWhen` (`gomodel.Stuck` where `timer.modify` throws: `when <= 0 ||
  period < 0`), `startTimer` (goroutine: `sleepUntil(w); fire()`, repeated for `period != 0`),
  `nextWhen`, `sleepUntil`, `stopTimerAt`, `resetTimerAt`, `var runtimeClock int64` with
  `runtimeClockNow` (atomic load + CAS over `runtimeNano`), `runtimeClockWaitUntil`, `whenAt`.
- Why each replaced name is a model: a goose run on the real source with every trusted name moved to
  `translate` (`gmr-time/goose-real*.log`): seven `[unsupported]: external function` (the runtime's
  push-linknamed `Sleep`, `newTimer`, `stopTimer`, `resetTimer`, `runtimeNow`, `runtimeNano`,
  `runtimeIsBubbled`); `NewTicker`/`Ticker.Stop`/`Ticker.Reset` convert `*Timer`↔`*Ticker` through
  `unsafe.Pointer` (no rule: not plain); `NewTimer`'s channel is made synchronous by the runtime
  (`syncTimer`, `godebug`), which plain Go cannot do.
- Side-by-side model vs real Go: `etc/trusted-delta.py 54a29571e..HEAD`, section "Go model overlays"
  (<details>: `gmr-time/trusted-delta.txt`, lines 165-653).

### Trusted Lean
`Perennial/TrustedCode/time.lean`: +41 −310. Deleted: the hand-written `.impl`s of `newTimer`,
`stopTimer`, `resetTimer`, `runtimeNano`, `runtimeNow`, `runtimeIsBubbled`, `syncTimer`, `After`,
`NewTimer`, `NewTicker`, `Ticker.Stop`, `Ticker.Reset`, `asynctimerchan.init`, and the helpers
`arbitraryTime`, `runtimeClock{,Type,Init,Read,Now,WaitUntil}`. Kept (primitive stubs, `trusted`):
- `now.impl` (new name for what the old `runtimeNow.impl` was): arbitrary `(int64, int32, int64)`;
  the runtime's `time_now` (bodyless, linknamed). Every result of the runtime's is one.
- `Sleep.impl`: `#()` (as before).
- `newRuntimeTimer.impl` / `newRuntimeTicker.impl` / `runtimeTimerFire.impl` over the same phantom cell
  `runtimeTimerRef` (`StructFieldRef Timer "timer" t`, a field no Go type has) as before: the runtime's
  per-timer state that trails a `Timer` in `runtime.timeTimer`; `runtimeTimerFire` is stuck on a
  `Timer`/`Ticker` the program allocated or copied (where Go's `stopTimer`/`resetTimer` read memory
  that is not a timer). Their Go bodies (gc) keep the state after the Timer in one allocation.
`asynctimerchan` is now a `[[skip]]` (its only reader `syncTimer` has no caller).

### Soundness fix (D3)
The old `arbitraryTime` (the value a timer sent) covered only `wall=0, loc=nil` times; Go sends
`Now()` times (`loc = Local`). So `if (<-time.After(d)).Location() == time.Local { panic() }` panicked
in Go and was provable safe. The model now sends `Now().Add(-delta)` (`sendTimes`), Go's own
`sendTime` value, which needs `isPkgInit time` at the timer's specs (Upamanyu's decision (1)).

### Statement changes (all approved)
- Strengthened posts (D2: Go's clock readings are positive; the models are stuck where the runtime
  throws on `when <= 0`):
  - `time.runtimeNano.spec`: `{{ (x : w64), RET #x; True }}` → `{{ (x : w64), RET #x; ⌜0 < sint.Z x⌝ }}`
  - `time.when.spec`: the same.
- New premise `isPkgInit pkg_id.time` (approved; the firing goroutine calls `Now()`):
  - `time.NewTimer.spec`: `{{ True }}` → `{{ isPkgInit pkg_id.time }}`
  - `time.NewTicker.spec`: `{{ ⌜0 < sint.Z d⌝ }}` → `{{ isPkgInit pkg_id.time ∗ ⌜0 < sint.Z d⌝ }}`
  - `time.After.spec`: `{{ clockLb n ∗ wand }}` → `{{ isPkgInit pkg_id.time ∗ clockLb n ∗ wand }}`
  - `time.After.spec_pkgInit` (what every caller uses) is unchanged, so no importer changed.
- Nothing else: `AfterFunc`, `Timer.Stop/Reset`, `Ticker.Stop/Reset`, `Sleep`, `Now`, `initialize'`
  keep their statements. `isTimer`/`isTicker` now carry the firing's persistent triple
  (`timerFiring fire True`) instead of the old fixed `noFire`.

### Specs of the additions (Spec/time/)
`now_` (primitive), `newRuntimeTimer`, `newRuntimeTicker`, `runtimeTimerFire` (primitives),
`newTimer_` (period 0, one firing from the caller's `P`), `stopTimer`, `resetTimer`, `stopTimerAt`,
`resetTimerAt` (a firing safe from nothing), `startTimer` (`(⌜p = 0⌝ ∗ P) ∨ □ P`), `timerFunc`
(`timerCallback f arg P` → `timerFiring fire P`), `makeTimerChan` (post: `∀ Ψ, |={⊤}=> isChanBag γ ch
Ψ`, so `After` picks the bag's predicate after reading the clock), `sendTimes`, `checkWhen`
(`0 < when ∧ 0 ≤ period`), `whenAt`, `nextWhen`, `sleepUntil`, `runtimeClockNow`,
`runtimeClockWaitUntil`. `clockLb` is now over the Go global `time.runtimeClock` (its points-to and a
mono counter in an invariant, allocated in `initialize'`, with atomic's `isPkgInit`).

### #print axioms
`[propext, Classical.choice, Quot.sound]` for each of: `time.wp_After`, `After.spec_pkgInit`,
`wp_NewTimer`, `wp_NewTicker`, `wp_AfterFunc`, `Timer.wp_Stop`, `Timer.wp_Reset`, `Ticker.wp_Stop`,
`Ticker.wp_Reset`, `wp_Sleep`, `wp_when`, `wp_runtimeNano`, `wp_Now`, `wp_initialize'`, `wp_now`,
`wp_runtimeClockNow`, `wp_newTimer`, `wp_resetTimer`, `wp_stopTimer` (`gmr-time/ax.log`).

### Evidence
- `etc/model-tests.sh` (adds `time`): ok. Left out by design (the `MODEL:` comments): TestAfterStop,
  TestTimerStopStress, TestChan, TestTicker, TestReset, TestTimerModifiedEarlier, TestAdjustTimers
  (Stop/Reset models do not cancel armed firings; the last three hang on a stale blocking send),
  TestTimerGC (a model timer's goroutine keeps it alive). The other 219 tests pass (each run alone).
- `go test ./goose/...`: ok.
- Builds (VM): `Perennial.Proof.time` + `Results`, and the whole importer cone (364
  modules: `Perennial.Proof.context`, `...goose_lang.std`, `...examples.channel_examples`,
  `...examples.unittest`, `...unsafememory.Link`, `...tchajed.marshal`, `Perennial.Proof.io.fs`):
  2725 jobs, ok. Not rebuilt after: 022db9a06 (one comment line in `Proof/context/Base.lean`).
- `etc/gen-link.py --check time`: ok.

### Review (review-trusted, fix mode)
No BLOCK or REWORK found; nothing to fix in the trusted files. NOTEs:
- R2: every replaced or stubbed name has the goose evidence above; the five stubs are bodyless
  runtime functions (`now`, `Sleep`) or the runtime's per-timer state (no Go type names it).
- R4/R12 (never more defined than Go): readings are arbitrary (`now`), positive where Go's are
  (`runtimeNano`); `checkWhen` is stuck exactly where `timer.modify` throws (unreachable through
  `when`); `Stop`/`Reset` do not cancel armed firings and `sendTimes` blocks where Go's `sendTime`
  drops, so the model only adds schedules (values after Stop, extra values); `runtimeTimerFire` is
  stuck on copies/zero Timers, where Go reads non-timer memory.
- R3/case 7: `runtimeTimerAlloc`'s `AngelicExit` unless the allocation lands at `runtimeTimerRef t`
  is the existing `alloc_struct` scheme (the model's own address choice), unchanged from `lean`.
- R8: 4262a17cd's message does not name the rejected alternative (hand-written Lean, the old
  TrustedCode); plan.md and this packet do. The translator change 02ff0ea6c (CheckAPI compares
  types without parameter names, as `types.Identical` does) has a unit test.
- Limitation, documented in `Proof/time/Base.lean` (`isInit`): a program that assigns
  `time.Local` cannot be verified (only `↦□` of it is handed out).

### After the adversarial review (lead, 2026-11-24 night)
- Review (fresh agent, tmp/gmr-adv-time/): no divergence reachable by a verifiable program today. Stop/Reset: every (result, later delivery) pair of Go is a model outcome; the specs post only `True`. Edge cases (zero/copied Timer and Ticker, d<=0, negative d), the sent Time, and positive `runtimeNano`: no divergence.
- Latent: `makeTimerChan` fixes a timer channel's kind at make, while gc re-reads `GODEBUG=asynctimerchan` on cap/len/send. Unreachable while setenv of `GODEBUG` is stuck. Decided: the runtime setenv hook is stuck on key `GODEBUG` (Perennial syscall; the etcd-grove side follows the same rule). Documented in the MODEL comment and in `docs/KNOWN_LIMITATIONS.md`, "time" (with the witness).
- `runtimeTimerRef`/`runtimeTimerAlloc` docstrings: soundness needs the timer cell at an address no program allocation has (ea45c778a).
- Incomplete, not unsound: `Reset` of an `AfterFunc` timer is unverifiable (`Timer.Reset.spec` requires `isTimer`).
- `Code/time.lean` at ea45c778a differs from 022db9a06 only in comments; it is rebuilt in the integration build.
