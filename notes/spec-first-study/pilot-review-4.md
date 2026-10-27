# Compactor pilot: spec review, round 4

Reviewer: `spec-reviewer` (fresh, read-only). Worktree `/shared/etcd-grove-cp` (branch `compactor-pilot`, HEAD
`678f5df2d5`). I read the rubric from `notes/spec-first-plan.md` "Phase 1b", including "Rounds". It matches the agent
file. I did not read the earlier review reports or the plan's "Step 2b" and later paragraphs.
Focus: the repair `4a7d599e6a..678f5df2d5` and the fork fix `964dccdb4`.

## Summary

- **No Tier-1 finding in the specs I reviewed.** The repair's changes are sound:
  - `modeRunPre`;
  - `periodicRunTok`'s empty slice and its capacity;
  - the permit removed from `Compact`;
  - `Run` added to the server's `compactorOk`;
  - `start()`'s handling of `Run`.
- **The fork fix `964dccdb4` is correct and complete in Go** (checked below).
- **One blocker outside the rubric (CI, introduced by the repair):** `etc/goose.py` now pins etcd at `964dccdb4`,
  but `examples/go.mod` and `examples/k8setcd3/go.mod` still replace etcd's modules with
  `...-c00a2dc06224`. `go_mod_pin_errors()` (`etc/goose.py:755-775`) reports this, so `etc/goose.py --check`, which
  CI runs, fails.
  - Also, `964dccdb4` exists only on a local branch (`goose-lean-compactorstart`) of the scratch clone, whose
    origin is `/shared/etcd-grove/.lake/go-src/etcd`. It is not on `github.com/upamanyus/etcd`. CI's clone of the
    pin and the examples' pseudo-version need it pushed.
- **Three Tier-2 findings**, one of them introduced by the repair: `CompactEnv.γf` plus `modeRunPre` push the
  compactor's internal ghost variable onto the server.

---

## Part A: the fork fix `964dccdb4` (Go)

The diff (`server/etcdserver/server.go`):
- removes `srv.compactor.Run()` from `NewServer` (line 388 is now a comment);
- adds `if s.compactor != nil { s.compactor.Run() }` to `start()` (`server.go:597-600`), after `s.w`,
  `applyWait`, `done`, `stop`, `stopping`, `ctx/cancel`, `read` and `leaderChanged` are set, and before `go s.run()`.

What I checked, all verified:

- **Every use of `s.compactor` in the fork:**
  - `server.go:384` (`New`).
  - `:598-599` (`Run`, now).
  - `:776-787`: `Pause` and `Resume` in `updateLeadership`. That runs in the raft ready handler inside `run()`,
    which starts after `Run`, so `Run` happens before any `Pause`/`Resume`, as before.
  - `:965-966`: `Stop` in `Cleanup()`.
  - No other package touches it: `embed/config.go` uses only the mode constants. No `_test.go` under
    `server/etcdserver` or `tests/` mentions the compactor.
- **Stop paths.** `Stop` is reached only through `Cleanup()`:
  - from `run()`'s deferred shutdown (the `s.stop` path, unchanged);
  - from `embed`'s `InitialCheck` failure path (`embed/etcd.go:277`), which calls `e.Server.Cleanup()` without
    `Start`.
  - In the second case the compactor has not been run. `Periodic.Stop`/`Revision.Stop` are just `cancel()` on a
    `WithCancel(Background())` context, which is harmless without the goroutine. Before the fix this path stopped a
    running goroutine; now there is none.
- **`NewServer`'s error paths after `New`.**
  - `restoreAlarms` and `tr.Start` failures now leave a compactor that was never run. `context.WithCancel(
    context.Background())` starts no goroutine, so nothing leaks.
  - The deferred `newSrv.kv.Close()` can no longer race with the compactor's `rg.Rev()` on a closed store.
  - The old leak, and the old race with `start()`'s writes, are gone.
- **Callers of `NewServer`.** There are two: `embed.StartEtcd` (`embed/etcd.go:262`, `Start()` at :282) and
  `tests/framework/integration/cluster.go:965` (`Start()` at :968). Both call `Start`, so auto-compaction still
  runs in every configuration that ran it before. The only difference is that it starts at `Start` rather than at
  construction; in `embed` that skips the window of `InitialCheck`.
- **`Start` stays non-blocking.** `Periodic.Run`/`Revision.Run` only spawn a goroutine.
- **The goroutine may call `s.Compact` before `go s.run()`.** In Go, `Compact` → `processInternalRaftRequestOnce`
  uses fields `start()` has already set, and the raft node's own goroutine was started at bootstrap. Moreover, the
  first `Compact` comes only after at least one `After(retry)` (periodic) or `After(5m)` (revision).
- **The translation** (`Code/.../etcdserver.lean`, hunks at `NewServer.impl` ~1719 and `start.impl` ~1997)
  matches: the `Run` call moved, and the rest of the diff is line renumbering.

Missing from the commit: a Go regression test for the fix, e.g. that a server built by `NewServer` and never
started makes no `Compact` call. The issue file cites only an existing embed test, and that test checks the
retention configuration, not when the compactor starts.

## Part B: the server's `compactorOk` and `EtcdServer.start`'s proof

`InvRun.lean:279-283` (new): the compactor is nil, or its `Pause`, `Resume` and `Run` all satisfy
`{{ True }} · {{ True }}`.

- **No trust-base leak (verified).**
  - It is a definition used in a premise (`srvRunBuilt`, `InvStart.lean:132-139`, inside `isServerBuilt`). It is
    not an axiom.
  - It has one producer, `NewServer.lean:1368-1372` (`ileft; rfl`: nil), under `NewServer.spec`'s
    `cfg.AutoCompactionRetention' = 0` (`Spec/.../NewServer.lean:144`, `:286`).
  - `InvBuild.lean:337`, `StartOn.lean:75` and `ServerOn.lean:300` only carry it along. No `axiom` mentions the
    compactor (I grepped).
- **`start`'s proof** (`EtcdServer__start.lean:431-444` and `:957-970`) consumes `compactorOk` correctly: the nil
  branch skips the call, and the ok branch applies `HCRun`. The proof of `run` (`EtcdServer__run.lean:546`,
  `:574`, `:1078`, `:1106`) drops the new conjunct (`-`). Both are sound.
- **The premise is false of the real compactor (Tier 2, below):** `Run`'s real contract needs `RunTok ∗
  modeRunPre`. It also reaches an exported statement: `Results.lean:2186-2192` is a result over `isServerBuilt`.
  It is not unsound, only a premise that no real compactor meets.

## Part C: can `start()` establish `modeRunPre` where it calls `Run`? (glue feasibility)

What `start` holds at `EtcdServer__start.lean:431` (`isServerBuilt`, `InvStart.lean:206-262`, after the `w` and
`applyWait` allocations), conjunct by conjunct:

- **`compactableOk E.c P E.R`, from `Compact.spec`:**
  - `isServerReq s E {ρ with wait := γw}`: obtainable. Every ingredient (`Hreqb`, `Hw`, `Hwait`, `Hdone`) exists
    before line 431. The proof now builds `Hreq` after the fork (line ~458), so the glue must move that earlier;
    that is all.
  - `idCred ρ.ids 1`: minted from `#HNR : □ (|==> idCred ρ.ids 1)` on each call. `Compact`'s post does not return
    it, so it cannot go in `R`.
  - `errTreeOk err`, from `compactOutIs`: when `err ≠ nil`, `applyErrIs` already has exactly `errTreeOk`'s shape
    (`apply/Base.lean:124`). When `err = nil`, `S := (· = nil)` gives a trivial `errorIsTree`, because
    `errorIsTree` constrains only non-nil members (Perennial `Proof/errors/Base.lean:217`).
  - `P`: `Compact.spec` takes no permit, so any `P` (in particular `modePermit`) is accepted. See the C1 note in
    target 4.
- **`□ E.RevLb 0`, with `RevLb := revLb E.γ.idx`:** available from `srvReadBuilt`'s
  `∃ log₀, idxCert E.γ.idx log₀ ∗ ⌜2 ≤ log₀.length⌝` (`InvStart.lean:~126`).
- **`revGetterOk` for `srv.kv`:** not yet established. It needs mvcc's `Rev` to return a certificate that extends
  the caller's, for the `n ≤ v` conjunct. **Uncertain**, see the end.
- **Not available: `E.R`, the per-call resources** that `Compact` returns and `Rev` needs (`srvLeadTimeReader s ∗
  E.RD ∗ mvcc.storeReaderC E.s E.γ`). `isServerBuilt` has no spare copy of any of them; it has only `Hlr`/`Hlrl`
  (logger readers). The request path's slots come from serving (`InvServe.lean:108`, K slots). None of these
  resources mentions `γw`, so `E.R` can be fixed at `New`'s call inside `NewServer`, as `New.spec` requires.
- **Not available: `New`'s `RunTok` and `firstUnset E.γf`.** Both are produced inside `NewServer`, at or before
  `New`'s call.

So the glue must add one non-persistent conjunct to `isServerBuilt`: "the compactor's run kit", meaning `RunTok ∗
modeRunPre`'s own resources, i.e. `E.R` and, in periodic mode, `firstUnset`. `NewServer` would produce it when
retention ≠ 0. That is feasible, and it is the expected glue, not a spec defect.

---

## Per target

### 1. `Spec/.../v3compactor/New.lean` (with `newPeriodic`, `newRevision`)

**Good (keep):**
- The `err` disjunct says which modes fail.
- The `RunTok` is existential, so the representation stays private.
- `modeRunPre` is at C1's permit for the mode.
- The scope premise `mode = periodic → 10 ≤ ret` cites `issues/etcd-compactor-periodic-tiny-retention.md`.
- `ret` keeps its sign for revision mode, and that is true. `Rev() - ret` cannot overflow for `ret > 0` because
  `Rev() ≥ 0`. For `ret < 0`, an overflow wraps to a negative value, which `rev <= 0` skips (`revision.go`). So
  `revPermit`'s `RevLb (r + ret)` is `RevLb (Rev())` whenever `Compact` is called, and no premise is needed.

**Findings:**
- **T2-1 (abstraction, implementation independence, caller burden; introduced or extended by the repair).**
  - The problem: `CompactEnv.γf` (`Defs.lean:191`) is a ghost name of the compactor's internal first-sample
    mechanism, and the caller must allocate it before `New`. `modeRunPre` (`Defs.lean:201-203`, new) then makes
    `Run`'s precondition depend on the mode, and the server must carry `firstUnset E.γf` from `NewServer` to
    `start` (Part C).
  - Why it is avoidable: `New`'s `RunTok` is already existential, and the caller supplies `compactableOk` at `Run`,
    not at `New`.
  - A revision-mode compactor, or another reasonable implementation, still has to accept a `γf` it never uses.
  - Caller affected: the `NewServer`/`start` glue.
  - Restatement:

    ```
    {{ … }} New … {{ cp err, RET (cp, err);
        (⌜err = nil⌝ ∗ ∃ (RunTok : IProp GF) (γf : GName),
           compactorOk cp RunTok (runPre E (modePermit mode E.RevLb (sint.Z ret) γf)) ∗ RunTok) ∨ … }}
    ```

    This drops `CompactEnv.γf` and `modeRunPre`. Periodic mode puts `firstUnset γf` inside `periodicRunTok pc γf`,
    with `newPeriodic` allocating it, and `Periodic.Run.spec` takes `runPre E (perPermit E.RevLb period γf)` as
    before. The server learns `γf` from `New`'s post, which comes before `Run`, where `compactableOk` at that `P`
    is due. A future server-wide permit fixed in `NewServer` can name it, since it is known after `New`.
    `firstSample_agree` is unaffected.
- **Scope (carried over, not new):** the premise `10 ≤ ret` also excludes negative periods.
  - What Go accepts: `time.ParseDuration("-1h")` succeeds through `embed/etcd.go:941`. The code does not panic for
    `|ret| ≥ 10`; it busy-loops.
  - It is cited (issue file, phase 0), so it passes the rubric.
  - Related Go observation, **uncertain**: `parseCompactionRetention`'s integer path,
    `time.Duration(h) * time.Hour` (`embed/etcd.go:935`), overflows for `h > 2562047`. A wrapped result can be
    negative, or tiny and positive, which would hit the tiny-retention panic. I did not check whether `issues/`
    records this or whether some `h` actually lands in [1, 9] ns.

**Metrics:**
- Scope premises: 1, cited.
- Caller burden: `γf` allocation plus threading `firstUnset` (T2-1); `RunTok`.
- Laws: `compactorOk_persistent`, `modePermit_persistent`, `firstSample_agree` (new; no consumer yet).
- Trust exposure: `clockwork.NewRealClock.wp_proof`, `realClock`, `clockLb`, `stampAt` (baseline
  `etc/tcb-collections/compactor-pilot.txt:23-26`); the `v3compactor` proofs are all `sorry`.
- Testability: the mode and `err` parts are decidable; the permits rest on the clock axioms, testable with an
  instrumented clock.
- Strength margin: `Stop`/`Pause`/`Resume` posts are `True`; that is enough for the callers.

### 2. `Periodic__Run.lean`

**Good:**
- `periodicRunTok` now owns `s ↦* [] ∗ ownSliceCap s 1` (`Defs.lean:234-237`). This is necessary, not just
  allowed: `append` needs the elements' points-to, and an in-capacity append needs the capacity. `newPeriodic`'s
  `make([]int64, 0, retentions)` gives both.
- The reader slot is exclusive and the guard persistent: that is faithful to `Pause`/`Resume` running
  concurrently with the goroutine.

**The loop walked concretely** (`periodic.go` `Run`): with `retry = min(period,1h)/10`, `R = period/retry`
(floor) and `retentions = R+1`:
- The window before the first drop: `revs[0] = s₀`, the first sample. `perPermit`'s second disjunct holds:
  `firstSample γf s₀` is set at the first `Rev()`, the stamp `T₀` comes from the first `After`'s call, and
  `clockLb (T₀ + retry)` holds once it fires.
- A full window: after a drop, `len = R+1` always, and `revs[0] = s_{i−R}`. `R+1` `After`s have fired since its
  stamp. Chaining with `T_{j+1} ≥ T_j + retry` (the clock's `n ≤ T`) gives `clockLb (T + (R+1)·retry)`, and
  `(R+1)·retry > period` by floor. That is the first disjunct.
- `continue` on Pause, and on `Now()-lastSuccess < baseInterval`, both happen after an `After`, so the chain is
  preserved.
- A failed `Compact` is retried at the same `revs[0]` with a persistent permit (`perPermit_persistent`); no token is
  spent.
- `0 < r`:
  - `rev = 0` while `lastRevision = 0` hits `rev == lastRevision`.
  - After a success at `r > 0`, every later sample is `≥ r` by `revGetterOk`'s `n ≤ v`, so `revs[0] ≥ r > 0`.
- `ctx.Done` returns.

There is no other path. **True.**

**Findings:** none in the spec.

**Metrics:**
- Scope premises: 0. `10 ≤ period` lives in `isPeriodic`, from `New`.
- Trust exposure: the clock axioms.
- Testability: the window and permit logic is testable with an instrumented clock; `firstSample` is ghost state.

### 3. `Revision__Run.lean`

**Good:** no run token is needed. `E.R` is exclusive, so a second `Run` cannot start without a second `R`; that is
faithful. The overflow analysis is in target 1, and the retry is at the same `rev` with a persistent `revPermit`.
**True and sufficient.**

**Findings:** none.

**Metrics:** scope 0; the clock is used only for `After` (5m), and nothing from it is needed for `revPermit`.

### 4. `Defs.lean` (vocabulary)

**Good:**
- `revGetterOk`'s monotone `n ≤ v` is what `0 < r` rests on.
- `errTreeOk` is derivable from `applyErrIs` in both the nil and non-nil cases (Part C).
- `compactableOk` returns `R`, and its post gives what the compactor inspects (`err` via `errTreeOk`; `resp` is
  ignored by both loops).
- `compactorOk`'s `Run` takes `RunTok ∗ RunPre`.
- The new persistence instances (`revPermit`, `firstSample`, `modePermit`) and `firstSample_agree` are correct and
  small.

**Trivial model of the clock axioms** (`Proof/github_com/jonboulle/clockwork/Defs.lean`):
- `clockLb := True`, `stampAt P T := <pers> P` satisfies every axiom. `stampAt := True` would not, because of
  `stampAt_elim`.
- Under that model `perPermit` reduces to `0 < r ∗ □ RevLb r`. The file's header says this explicitly and names
  the intended reading as the trust boundary. That is acceptable as stated.
- The axioms are true of clockwork v0.5.0: `realClock.After = time.After`, `Now = time.Now`
  (`clockwork.go:33,41`), and `time.After` fires on the monotonic clock no earlier than `d` after the call.

**Findings:**
- **T2-3 (documentation; stale after the repair):** the header at `Defs.lean:32-34` still says `runPre` includes
  "the first sample's ghost variable". It moved to `modeRunPre`, or to `RunTok` under T2-1. Similarly
  `Spec/.../NewServer.lean:143` and `:285` say "`v3compactor.New` and its goroutine not reached", but the goroutine
  is now started in `start()`.
- **C1 has no consumer (note, not a defect).** `modePermit` is proved by the compactor, but `Compact.spec` no longer
  takes a permit, so any server meets `compactableOk` at any `P` and C1 constrains nothing observable yet. The
  docstring of `Compact.spec` says so. This is honest; the rejected alternative, a per-call `Pc`, was vacuous. Make
  sure the C3 design consumes `modePermit` at the `E.RevLb` the server fixes; otherwise `firstSample_agree` and
  `perPermit` stay unused laws.

**Metrics:**
- Laws: persistence for all permits and contracts, and agreement for `firstSample`. No fractional laws are needed.
- Coupling: mvcc (`revLb` over `idxCert`), context, sync, clockwork.

### 5. clockwork trust boundary (`Defs.lean`, `NewRealClock.lean`)

**Good:**
- `After`'s `⌜n ≤ T⌝` lets waits chain, and that fixes the "bounds that cannot be chained" pattern.
- A stamp can be made only by `After`.
- `Now` gives nothing. That is honest, because Perennial's `Time.Sub` has no spec, and it is why the first sample
  has the weaker permit.
- `NewRealClock.spec` is minimal.

**Findings:** none. The trivial-model caveat is documented (target 4).

**Metrics:**
- Axioms: `realClock`, `clockLb`, `stampAt`, two persistence instances, `clockLb_init`, `clockLb_le`,
  `stampAt_elim`, `stampAt_clockLb`, and `NewRealClock.wp_proof`. Only four are in the baseline so far: the
  compactor proofs that would use the rest are `sorry`.
- Tester: phase 2's instrumented clock; not run yet.

### 6. `EtcdServer__Compact.lean` (`spec`, `specOn`, `compactOutIs`)

**Good:**
- The per-call `Pc` is removed. That is right: each caller chose it, so it said nothing.
- Both modes are present (`spec` and `specOn`).
- `storeReaderC`, not `storeReader`, avoids the "never compacted" contradiction.
- `compactOutIs` gives the compactor `errTreeOk` (Part C) and gives the gRPC handler a revision certificate.
- The precondition's resources (`srvLeadTimeReader`, `E.RD`, `storeReaderC`) are returned. `idCred` is not
  returned, but it is mintable from `□ |==>`.

**Findings:**
- **Tier 1, sufficiency for the gRPC caller (carried over; documented phase-1 scope, not introduced by this
  repair):** `compactReqIs` requires `Physical = false`, and the post says nothing about what the apply did. The
  gRPC side's `compactOk` (`api/v3rpc/InvAuthAdmin.lean:154-163`) takes any request `r` and a caller-chosen
  `Q resp`, plus `hdrRevIn A.revR h rv` and a persistent header. A physical request cannot use this spec. A `Q`
  about the compaction's effect cannot be produced until C2/C3 are stated. Phase 1b's freeze needs this caller's
  glue; I list it so that it is not lost, not as a new defect.
  - Minor: `compactOutIs` gives `h ↦ v` (exclusive), while `compactOk` wants `↦□`. The glue can persist it, so
    this is fine.

**Metrics:**
- Scope premises: 1 (non-physical; cites the pilot's scope).
- Caller burden: the compactor glue needs `isServerReq` at `start`'s fresh `γw`, plus the three reader resources.
- Coupling: apply, mvcc, context, and `v3compactor.compactReqIs`.

### 7. The server's `compactorOk` (`InvRun.lean:273-286`)

**Findings:**
- **T2-2 (no unneeded premise, interpretation; introduced by the repair's added `Run` conjunct).** See Part B: it
  is sound and not in the trust base, but the ok branch is a premise no real compactor meets, and it appears in an
  exported result over `isServerBuilt` (`Results.lean:2186-2192`).
- Its only producer gives nil. Until the glue lands, the simpler and more honest statement is
  `compactorOk c := ⌜c = GoInterface.nil⌝`, with the ok branches of `start` and `run` refuted. Otherwise, keep it,
  but say in the docstring that no real compactor satisfies the ok branch. The current docstring half-says it
  ("the glue replaces this contract").
- Caller affected: a reader of `interface/` and of the TCB report's definitions. No proof depends on it.

---

## Ranking (most to least in need of revision)

1. **The pin and go.mod consistency** (outside the rubric, blocks CI): bump the two `go.mod` files to `964dccdb4`'s
   pseudo-version, and push `goose-lean-compactorstart` to the fork.
2. **`New.lean` / `Defs.lean` `CompactEnv.γf` + `modeRunPre`** (T2-1): move `γf` into the existential `RunTok`
   before the glue builds on it.
3. **The server's `compactorOk`** (T2-2): reduce it to `nil`, or make the docstring say plainly that only nil is
   meant.
4. **`EtcdServer__Compact.lean`**: the gRPC caller's sufficiency (carried-over scope; needed before the freeze).
5. **`Defs.lean` and the `NewServer` comments** (T2-3): stale text.
6. `Periodic__Run.lean`, `Revision__Run.lean`, clockwork: nothing to revise.

## Uncertain points

- **`revGetterOk` for `srv.kv`.** It needs mvcc's `Rev` (through `watchableStore`) to return an `idxCert` of a log
  that extends any earlier certificate, for `n ≤ v`. That holds only if the store's revision never decreases. A
  snapshot restore could break it, but D19p says raft sends no `MsgSnap`. To settle: read `mvcc`'s `Rev` spec
  (`InvStore.lean`) for a prefix or monotonicity conjunct.
- **Clients' `storeReader` (`crevFrozen`) once compaction is on.** Several clients hold `mvcc.storeReader`, which
  asserts a never-compacted store (`client/v3/Results.lean:815`, the examples' `common`). With
  retention ≠ 0 the apply compacts, so `crevFrozen` cannot be handed out. The glue that lifts
  `AutoCompactionRetention = 0` has to move those clients to `storeReaderC` or make `crevFrozen` conditional. This
  is beyond the reviewed specs, but it decides whether the pilot's glue stays local.
- **Overflow in `parseCompactionRetention`'s `h * time.Hour`** (target 1): I did not check `issues/` or whether a
  wrapped value can land in [1, 9] ns.
- **I did not run** `etc/goose.py --check` or `etc/tcb-report.py` (read-only brief; a build was running). The pin
  mismatch comes from reading `go_mod_pin_errors()` against the two `go.mod` files.
