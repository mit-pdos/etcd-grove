# k8s 7g (the maintainers' checker): handoff

## START HERE

**2026-11-19 (night 18; for etcd-grove-03). 03's night-17 decisions recorded (questions.md). Done, each file
lean-checked `-a` without `--fast` (all 7 touched proof files, 0 errors): gap 2 + the ReplayPre lemma
(`7b8a12f143`), `realRequest` + `realEvents` specs+proofs (`da5687eeaf`), GMap.ofList docstring in
perennial-changes (`9438517238`). Build of targets-n17 queued all night behind full builds (never got a slot);
next build: `targets-n18.txt` (n17's + realRequest/realEvents/genList/genFrom/Apply/Model).**

- Branch `k8s-7g`, pin f551a1b46 (`--packages=/shared/tmp/manifest-f55.json`); lean not merged (still f551 at
  23d3bae205; switch to manifest-3af when lean moves). Build (tree lock shared with lean-check, see pitfalls):
  `/shared/tmp/build-slot.sh flock /shared/tmp/k8s7g/tree.lock lake --packages=/shared/tmp/manifest-f55.json build $(cat /shared/tmp/k8s7g/targets-n18.txt)`.
- Forms this night (questions.md "night 18"): `ListOptOk` (GenIn's 5th conjunct; the "MinRV ≠ \"0\"" fact is derived,
  not added: parseRVD refuses "0"); genList premise `Match = 0`; GenIn/GenInW/GenInA/CachedNoRV/InOk/wkKeysL moved
  to MDefs; ioOk carries `GenInA x`. RealMS: `genIn_stepIn`, `genIn_listConsL`, `replayPre_of`.
- NEXT, in order:
  1. `realCheck` spec + proof. Premises (from Check after RunLin2 Ok + failureFree): `lsl ↦* lops`, `opsIoOk
     (k8setcd3S g0) lops`, `IsLinearization (pM (kSpec g0) decOp) (histOf lops) (range n)`, `HistOk lops`,
     `∀ o, okOut`, `storeOwn s0 g0.st` + Model's g0 facts. Post `r ≠ Illegal ∧ (dur ≤ 0 → r = Ok)`.
     Proof: loop 1 builds `operations`/`pOps`/`watches` (per op: ioOk gives x, y, GenInA, rawOk; realRequest(x)
     with inFits from GenIn; respRep of Raw from rawOk); `L` = the entries (OpV, (x, r)); StepAgree L from
     `reqRep_agree`/`respRep_agree`; initialModel (distinct keys from `StOk g0.st`); toPorcupineModel(L);
     CheckOperationsVerbose: Illegal refuted by `realS_isLinearization` (H := the ROp history of lops) +
     `isLinearization_map` + `realM_step`; `partLins` exactly one; orderByLinearization; NewReplay with
     `replayPre_of` (stepIn via `genIn_stepIn`) and B4 `realReplay_ok` (any lin2); Validate per op; NewWatchValidator;
     ValidateWatch per watch with B5 (RealWatch ~l.871) and `realEvents`.
  2. `Check`: failureFree + realCheck calls; gen-link (`LAKE_OPTS` needed); timed full build (report the id).
  3. Report at step 5's end; then step 6 prep and STOP for the Freeze.
- Pitfalls (new): a lean-check import rebuild and a lake build on one tree must not overlap: run builds as
  `build-slot.sh flock /shared/tmp/k8s7g/tree.lock lake ...` and lean-check as `flock -n /shared/tmp/k8s7g/tree.lock
  env LAKE_OPTS=... etc/lean-check.py ...` (fails fast while the build holds it). In a `local macro` with
  `set_option hygiene false`, `decide_true` is ambiguous (`BI.decide_true`): write `_root_.decide_true` (the
  failure shows up as an un-cleaned `#(decide ..) = #true` loop condition). `wp_for HL` fails with a hyp named
  `in` (iNamed can't parse it): `irename «in» => Hin` first. A `wp_for` with `break` continues the rest twice
  (break and exhaustion): share it as a local macro (realEvents' `re_tail`). `ipersist` needs an update: `iapply
  wp_fupd` before the code (realRequest's create branch). `prepareKeyM_nil` exists in RealBridge (`= some p` form).

### Superseded (night 17)

**2026-11-19 (night 17; for etcd-grove-03). 03's night-16 decisions recorded (questions.md). Done, each file
lean-checked `-a` (not `--fast`): `realMS` + `toPorcupineModel` (`b32da0e0a4`), gap 1 (RunLin2's post exports
`HistOk lops`, same commit), `failureFree` + `orderByLinearization` (`89d6640bf7`), `initialModel` (`01b4e563ac`).
NO build ran: the queued targeted build sat behind 4 full builds; I cancelled my own queued job so lean-check
could rebuild imports alone. Next build: `targets-n17.txt` (n16's + the new modules).**

- Branch `k8s-7g`, pin f551a1b46 (`--packages=/shared/tmp/manifest-f55.json`; lean still pins f551 at 23d3bae205,
  not merged into the branch: merge it, and switch to manifest-3af when lean moves to 3afd77e35). Build:
  `/shared/tmp/build-slot.sh lake --packages=/shared/tmp/manifest-f55.json build $(cat /shared/tmp/k8s7g/targets-n17.txt)`.
- New vocabulary (`RealMS.lean`): `rexecL_notOther` (the model's answer is never `.other` given keyOk / a list's
  `listConsL` + `prepareKeyM []` some), `itemsFitL_step`, `stepIn x r` (opPre ∧ crFits ∧ the not-other facts),
  `okOut`, `boxReq`/`boxResp`/`boxM`, `realMS L init` (rep: `∃ mp, v = boxM mp ∧ itemsFitL m ∗ modelAt mp m`; ioOk: boxes,
  `decR L (i,o) = some (x,r)`, `stepIn x r`, `reqRep`, `respRep`).
- NEXT, in order:
  1. Gap 2 (ioOk facts): `listConsL x` some and `0 < Limit → MinRV ≠ "0"` are NOT derivable from `GenIn` today
     (genList keeps the input's Match/Limit when MinRV is ""/zero). Proposed form: `GenIn` gains, for a list,
     `(MinRV = [] → Match = 0) ∧ (Match = 2 → parseRVD MinRV ≠ some 0) ∧ (0 < Limit → MinRV ≠ "0")`; genList's
     premise `Match = 0 ∧ Limit = 0` (genFrom passes a fresh input); then `k8setcd3S.ioOk` gains `GenInA x`
     (Apply's `hioOk` has `HgenA`; Model.lean's `⟨rfl, rfl, Hxk, -⟩` absorbs it). The response facts of `stepIn`
     (flatE, listOrNil, objOrNil) come from `rawOk`/`RawRel`.
  2. `ReplayPre` lemma: from `stepIn` of every op (`stepIn_stepPre`) and itemsFitL along the replay (`itemsFitL_step`).
  3. Specs+proofs: `realRequest` (post `reqRep r x ∗ reqPin r x`; calls listOptions, storeKey, splitKey,
     preconditions, validateFor, tryUpdateFor, cachedObj), `realEvents` (post `evsRO r (realEventsL x rs)`;
     template `firstBookmark.lean`; needs a sub-slice lemma for `↦*□`), `realCheck` (porcupine over `realMS L init`
     with `L` from the ops' entries; Illegal refuted via `isLinearization_map` + `realS_isLinearization` + `realM_step`
     (StepAgree from `reqRep_agree`/`respRep_agree`); then B4 `realReplay_ok`, Validate, NewWatchValidator,
     ValidateWatch with B5); `Check` (initialModel's premise: distinct store keys from `StOk g0.st`); gen-link
     (`LAKE_OPTS` needed); timed full build.
- Pitfalls (new): `RealBridge` and `ErrViews` both declared `rexecL_write_deep` (renamed RealBridge's
  `rexecL_write_deepV`): RealMS imports both. A `by word` inside a `have` whose statement mentions a
  section-variable abbrev (`opGood`) gave a KERNEL "application type mismatch" (lean-check without `-a` passes):
  hoist arithmetic into its own top-level `have`. `wp_start` consumes BOTH packages' `isPkgInit` (names `Hpkg`,
  `Hpkg2`): pattern only the rest. A leftover `if decide True = true` needs `decide_True_any` (not
  `decide_true`). `wp_if_destruct` refuses `#y.WFailed'`: `cases hw : y.WFailed'`. In a slice range loop, keep
  `wp_load_slice_index` (the element is not loaded by wp_auto). `realMS`'s fields: `iunfold realMS at H`, and
  `rw [show (realMS L init).M = realM L init from rfl]`. `GMap.ofList`'s docstring says later bindings win; the
  definition keeps the FIRST (Perennial doc bug, candidate).

### Superseded (night 16)


**2026-11-19 (night 16; for etcd-grove-03). 03 accepted night 15 (questions.md "Step 5 night 15: decided"; findings
in k8s-7g-trust.md §7). realCheck's foundations done, lean-checked (`-a`, not `--fast`): closure pins (`5acda50d4c`),
RealModel + RealAgree (`5569275b5b`), RealAgreeReq (`b989613346`). NO build this night: df 36 GB (< 40) and slots
full; targets for the next build: `/shared/tmp/k8s7g/targets-n16.txt` (night 15's + the new modules + call/mdelete;
`k8s.etcd3.Check`/`Link` fail as expected until realCheck is wired).**

- Branch `k8s-7g`, pin f551a1b46 (`--packages=/shared/tmp/manifest-f55.json`). Build when df ≥ 40 GB:
  `/shared/tmp/build-slot.sh lake --packages=/shared/tmp/manifest-f55.json build $(cat /shared/tmp/k8s7g/targets-n16.txt)`.
- realCheck PLAN (decision 1). DONE:
  1. `ClosPin`: `validatePin`/`tryUpdatePin` (stronger posts of validateFor/tryUpdateFor; callers mdelete/call drop
     them, call.lean NOT re-checked: in the build). Form, recorded (questions.md night 16).
  2. `RealModel`: `isLinearization_map`, `decR L io`, `realM L init`, `StepAgree L`, `realM_step` (on an entry, realM
     steps as realS on the entry's own view, given StepAgree).
  3. `RealAgree`: `deepRep_agree`, `errRep_agree`, `respRep_agree` (errs ≠ `.other`). `RealAgreeReq`: `reqPin r x`
     (validatePin for Kind 1, tryUpdatePin for Kind 2), **`reqRep_agree`**: reqRep/reqPin of x1 and x2 on one
     `Request` ⊢ ⌜∀ m out, rstepL x1 m out = rstepL x2 m out⌝. So StepAgree follows from the entries' reps.
  NEXT, in order:
  4. ModelSpec `realMS L init`: rep k v m := ∃ mp, v = box mp ∧ itemsFitL m, modelAt mp m (persistent; Init's
     Clone gives modelOwn: `modelOwn_freeze` under wp_fupd); ioOk i o := ∃ rq ro x r, boxes ∧ decR L (i,o) = some
     (x,r) ∧ Model.Step's pure premises ∗ reqRep rq x ∗ respRep ro r. Step's spec calls Model.Step with the decR view.
     Needs a lemma `(rexecL x m).1.err ≠ .other` from keyOkL / prepareKeyM / listConsL (encOkL by scope, cf.
     RealBridge `encOkL_loop`) and `itemsFitL_exec` for the next state.
  5. Discharge gaps: RunLin2.spec's post lacks `HistOk lops` (stronger post, form); k8setcd3S.ioOk must gain OpOk's
     request facts and wInPre (decision 2), proved in Apply from kInOk; NewReplay's `ReplayPre` (stepPre along the
     replay) has no lemma yet.
  6. Go specs: failureFree, realRequest (reqRep + reqPin), realEvents, initialModel (modelAt (absR st0)),
     toPorcupineModel (isModel (realMS L init)), orderByLinearization, realCheck; Check's new proof; gen-link.
- Pitfalls (new): `#l` for a Loc is abstract (only `go.intoVal_inj`, needs `include sem in` and `(sem := sem)` at
  use sites): pins index the closure body's value list (`exprVals`), found by tracing with `set_option
  pp.deepTerms true`. `iframe` does not close a goal of two persistent hyps: `isplit; iexact`. `simp only [h]` with
  `h : x.Kind' = W64 0` leaves `W64 0 = W64 4` undecided: use `rw [if_neg n, if_pos h]` (helpers
  `rstepL_list_eq`/`rstepL_get_eq`/`rstepL_write_congr`). Struct-value injectivity: the `proj_eq` pattern (MDefs).

### Superseded (night 15)

**2026-11-19 (night 15; for etcd-grove-03). `Replay.validateGet` specified+proved, `Replay.Validate` proved
(`a63f96f8ff`); `keyFunc` specified+proved; watch.go's spec FIXED (two panics were reachable: forms below);
watch.go DONE: all 17 functions specified+proved, `ValidateWatch.wp_proof` against its accepted spec
(`89b5f62aef`, `efdd13f285`, two sub-agents; each file fully lean-checked); targeted build `build-n15`
(`/shared/tmp/k8s7g/build-n15.log`, targets `targets-n15.txt`). Not yet in Link.**

- Branch `k8s-7g`, pin f551a1b46 (`--packages=/shared/tmp/manifest-f55.json`). lean not yet moved to 3afd77e35
  (origin/lean has it): merge when local `lean` gets it, then a timed full build.
- Forms this night (questions.md "Step 5 night 15"): validateGet/Validate take `keyOkL` of a get's key;
  `replayAt` carries each state's own rv (`replayL_rv`) and `chgOk` of every change (`replayL_chgOk`);
  `wInPre` gains `x.Limit' = 0` (checkWatch panics on a limit; genWatchFrom never sets one: `GenInW` must
  gain it and flow to realCheck). Model.listItems.spec generalized in place (initialEvents' options).
- Next, in order: realCheck's design decision (below); realcheck.go; Check; the discharge list; gen-link.
- realCheck DESIGN (not started; decide first): porcupine runs over boxed `Request`/`Response` VALUES (OpV),
  whose views (reqRep/respRep) need the heap. Plan: a ModelSpec for toPorcupineModel with `M := realS`
  lifted through `decR : OpV → Option (Input × RResp)` = the view of the FIRST pOp with those values
  (classical, fixed after the ops are built); needs (i) deepRep agreement (equal values ⇒ equal response
  views; no lemma yet) and (ii) "rstepL x m out depends on x only through realRequest(x)" per kind (create's
  `op ↦□ createObjL x` agreement; get/list fields). Then B2 transfers through the lift (porcupine Filter /
  fmapH lemmas), partLins gives the one linearization, B4/B5 give realOkL on it.
- Discharge: ioOk (k8setcd3S) must gain the input facts realCheck needs (OpOk's request facts from GenIn,
  wInPre from GenInW+Skip=false), from Apply's kInOk.
- realCheck's proof never uses a rejecting run (03's condition); NewReplay/validate*/Validate comply.
- Pitfalls (new): lean-check `-a` after a lake-rebuilding edit can exceed the Bash 120 s timeout: run it
  with run_in_background. `first | (cases h; left; rfl) | cases h` (not the reverse: `cases h` on
  `some c = some ⟨…⟩` leaves the goal).

### Superseded (night 14)

**2026-11-19 (night 14; for etcd-grove-03). Night 13's drafts lean-checked and fixed (`efa0a5d726`); targeted
build `build-n14` (log `/shared/tmp/k8s7g/build-n14.log`, rc 1) fails ONLY `k8s.etcd3.Check` (needs realCheck,
expected). `NewReplay` proved (`27c8086bb2`); `Replay.validateList` specified and proved (`ee58711406`).**

- Branch `k8s-7g`, pin f551a1b46 (`--packages=/shared/tmp/manifest-f55.json`); lean is about to move
  (merge-origin4, manifest-3af): merge it when it lands, mechanical repairs only.
- etcd-grove-03 accepted night 13's forms (questions.md "Step 5 night 13: decided by etcd-grove-03"),
  incl. porcupine's exactly-one `partLins` (its proof went through, `checkParallel.lean` ~l.661).
- Forms this night (questions.md "Step 5 night 14"): new `listExpOk R x out` premise on `Replay.validateList`
  and `Replay.Validate` (equalListResponse needs a deep expected error); realCheck must discharge it.
- Next, in order: `Replay.validateGet` (spec + proof: map range over `states` with early return, the
  `stateWithoutPrefix` copy; follow `Model__validateGet.lean`'s `get_tail`: wp_Parse, wp_GRC, wp_DeepEqual_resp,
  wp_IsTooLarge), then `Replay.Validate` (dispatch on `req.Op`); ValidateWatch (watch.go's 15); realcheck.go
  (failureFree, realRequest, realEvents, keyFunc, newObjList, initialModel, toPorcupineModel's closures,
  orderByLinearization, realCheck); Check; the discharge list (night 6); report at step 5's end; step 6 prep,
  STOP for the Freeze.
- realCheck's proof must never use a rejecting validator run: each rejecting branch is shown unreachable
  from B4/B5 (etcd-grove-03's condition). NewReplay does this already (`replay_step_ok`).
- Pitfalls (new): lean-check's incremental report MISSES errors after the first changed declaration
  ("0 errors" with an unknown identifier later): always `-a` before trusting a file. `wp_auto` at the end
  leaves `Φ v` with no update: to persist a fresh allocation, `iapply wp_fupd` before `wp_auto`, then
  `ipersist`, `imodintro`. `iframe #` splits a `[∗list]` over `l ++ [x]` and leaves the tail
  (`BigSepL.bigSepL_append.1`). `simp (config := { decide := true }) only [rconsStr]` decides the
  consistency-string comparison (a plain `rw [decide_eq_false _]` does not match under the WP).
  `RealWatchFrom` lives in `k8s_etcd3` but its vocabulary is `k8s_correctness`'s.

### Superseded (night 13)

**2026-11-19 (night 13; for etcd-grove-03). lean merged (pin f551a1b46); full timed build
`20261119-042933-2307866` rc 1; step 5's watch side, the replay/validator specs and porcupine's
exactly-one linearization DRAFTED, UNCHECKED, merged into `k8s-7g` (`cf8fbe534e`, `c959e16097`).**

- Branch `k8s-7g`, pin f551a1b46: `--packages=/shared/tmp/manifest-f55.json`, `.lake/package-overrides.json` =
  its copy; gen-init with `PERENNIAL_DIR=/shared/perennial-f551a1b46`. Merge forms: questions.md "Merge of
  lean df37bd5157" (PredOk lemmas `.wp_ok`; go-cmp/maps retranslated).
- Full build (`/shared/tmp/k8s7g/build-f55.sh`, log `build-f55.log`) of the clean merge `a6e935f277`: failed
  only `k8s.etcd3.Model` (night 12's ioOk change, never rebuilt: l.127 ioOk not pure — fixed blind in
  `c959e16097`; l.328/377 `if decide True = true` left in the goal before `wp_apply`/`iapply`, probably the
  pin: add `decide_true` to the simp there), `Check` (expected), `consume`/`watchEvents`/`runWatch` (broken
  since step 0's Go change; reworked in the WIP). Everything else built.
- UNCHECKED, never elaborated (written while the build held the tree): lean-check file by file, in order:
  correctness/EvRep, RealWatchFrom, RawOk, MDefs, Calls, toWEvent spec+proof, consume spec+proof,
  watchEvents, runWatch, WatchQ, Apply spec+proof, Model, Check (still needs realCheck), porcupine Defs +
  checkParallel + lintest RunLin2 (rebuilds every lintest user: targeted build after), correctness/ReplayRep,
  WatchRep, the three new specs. Contents: `993112a24a` (watch raw events: `evRep`/`evsRO`; toWEvent →
  consume → watchEvents → runWatch return the received events, `wEventsRawOut`; `ioOk` gains `FloorOk
  g0.st.rv x` and `wrawOk`; `kInOk c f`; Apply.spec premise `uint.nat g0.st.rv ≤ g0.hist.length`; Apply's
  watch read updates `watchQ γ c (max lb s0n)`, fired past the seeds via `kInv_lb_seed` (`run_hist_ge`,
  `RealWatchFrom.run_inv`); `watch_commit` returns a pure `P`, here `WatchFromL` (`watchFromL_of_kStreamOk`)),
  `c3ac0264cc` (`ReplayRep`, `WatchRep`; specs `NewReplay`, `Replay.Validate`, `WatchValidator.ValidateWatch`,
  accepting runs only), `da58ad267e` (porcupine `partLins`: `h ≠ [] → lsls.length = 1`, see FOUND).
- Next, in order: check the drafts above; proofs of NewReplay/Validate/ValidateWatch and their internal functions
  (replay.go: validateGet/validateList/InitialEvents/EventsForRVs; watch.go's 15; `Replay.Watch` and
  `ResourceVersion` are not reached from realCheck: no spec needed, say so at the Freeze); realcheck.go
  (failureFree, realRequest, realEvents, keyFunc, newObjList, initialModel, toPorcupineModel's closures as
  an `isModel` of `realS`, orderByLinearization, realCheck); Check; the discharge list (night 6).
- FOUND (plan gap, decide in step 5): `realCheck` answers Illegal unless `len(PartialLinearizations()) == 1
  && len(...[0]) == 1`, but porcupine's `partLins` promises only "at least one". Porcupine really gives
  exactly one on Ok (`checkSingle` sets every `longest[i]` to the same `&seq`; the set dedups by pointer).
  Drafted (`da58ad267e`): `porcupine.partLins` strengthened in place (`h ≠ [] → lsls.length = 1`; proof in
  `checkParallel.lean` near l.640, from `ps = replicate _ p0` and the set's keys nodup) — a stronger post
  on a proved spec (form). Fallback: the glue's check to `len(...[0]) == 0` (trusted glue text: STOP).
- Pitfalls (new): never edit Lean files in the build tree while a build is queued or running (lean-check
  cannot run then either): draft in a scratch worktree. `etc/tier-check.py --check`: a `<F>.wp_proof` name
  makes a module a proof module (PredOk's derived lemmas renamed `.wp_ok`).

### Superseded (night 12)

**2026-11-19 (night 12; for etcd-grove-03). (b1) applied and verified; call.lean and Apply.lean proved against the
new specs (lean-check `-a --fast`, 0 errors); targeted build `/shared/tmp/k8s7g/build-n12.sh` (log `build-n12.log`).**

- Branch `k8s-7g`, pin 6d365ee1a (`--packages=/shared/tmp/manifest-6d3.json`; switch to manifest-f55 on lean's
  "Merge origin/lean (d52bb9be66)"). Commits: `43815f4447` (b1: `tooLargeErrIs` + Code/retry; NewTooLarge's post at
  retry 0; callers; `errRep_tooLarge_of_is`), `4adfdf4efc` (call: rawOk of errors/objects/lists; `respIs_call` gives
  the rejection's sentinel `eR` and a non-Annotated object; `ListModel.loop_items_mem`; call.spec's list post on
  `plainOut`), `3b9071bcee` (Apply; `ioOk` carries `⌜Kind=5 ∨ plainOut y = otherL⌝ ∨ rawOk x y`; `linU`'s post at any
  `o'` with the same step; `contAt` at any `y'` with the same `plainOut`). Forms: questions.md "Step 5 night 12".
- Build: read `build-n12.log` first. Expected failures: `k8s.etcd3.Check` (realCheck not yet called) and what imports
  it; anything else is new (call/Apply/InvSteps/WatchQ were only lean-checked with `--fast`).
- Next, in order (step 5): runWatch + watch.go specs, replay.go (8), watch.go (15), realcheck.go, Check (runs
  realCheck on the history; `uint.Z s0.rv' < 2^62` at istart; each op's Raw facts come from `RunLin2`'s `ioOk` list),
  the discharge list (night 6 below); report at step 5's end; step 6 prep, STOP for the Freeze.
- Freeze list additions this night: `apierrors.tooLargeErrIs` and `NewTooLargeResourceVersionError.spec` (b1).
- Pitfalls (new): `contAt` is an `abbrev` (a wand): `iapply` of a lemma concluding `contAt …` tries to apply it; state
  conversions with an explicit `have h : contAt … ⊢ contAt … := …` then `ihave H := h $$ HΦc`. `iunfold`/`unfold` of
  a definition in an IPM goal with persistent hyps in scope can break `ipureintro` (istart error): `iclear` them first.
  Named holes (`?hpl`) in a macro used twice clash: put pure facts as `⌜…⌝` premises of the lemma instead.

### Superseded (night 11)

**2026-11-19 (night 11; for etcd-grove-03). IsNil attack accepted, threading done; step 5 started (RawOk, listOut,
valsOk invariant). STOP: `rawOk` of a too-large answer needs facts the store's `tooLargeErrIs` lacks (questions.md
"Step 5 night 11").**

- Branch `k8s-7g`, pin 6d365ee1a (`--packages=/shared/tmp/manifest-6d3.json`; switch to manifest-f55 on lean's
  f551a1b46 merge). Commits: `61089b1368` (IsNil minor 1; `listIs`/`finalizeList` non-nil items; `UpdateList`
  clause on metadata only), then the step-5 commit (see git log): `RawOk.lean` (RawRel moved, `rawOk`), `listOut`
  posts the list's read-only deep value, `valsOk` invariant (`KOk.vals`, `KOk.ins` val bound, `hval` on
  kOk_ok/kOk_errW and InvSteps' create_au/rw_au/write_err_commit/get_read_au/get_maker; `listQ`/`plainL` carry
  `valsOk`), `call.spec` (QL premise + `valsOk`; post `plainOut y = …` + `rawOk x y`).
- Checked (lean-check `-a`, 0 errors): ListDefs, finalizeList, GetList (`--fast`), RawOk, listOut, Inv, InvSteps,
  Seed, RealBridge. NOT rebuilt through the slot yet; build-optA rerun was cancelled (slots busy) to keep
  lean-check free: rerun `/shared/tmp/k8s7g/build-optA.sh Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.ListContract`
  after the call/Apply work (or now, for the raft-kv fixes alone).
- Broken on purpose (step 5 in progress): `call.lean` (new spec: GetList needs `hQL` projected to 3 conjuncts;
  list_ok: `listIs` → listOut's new pre, itemOk of the items from `valsOk` + a `kListL` membership lemma
  (items ⊆ decoded kvs of the store read); errors: `rawOk` from `errIs` (storageErrIs/invalidErrMsg are
  persistent `↦□`, rejections need `errStrCell` of eD/eU from drvInit); too-large: the STOP), `Apply.lean`
  (pass `Hgen.2.2.1` as `hval`; QL discharges `valsOk` via `listQ_pure`/`plainL_pure`), Check.
- Next after the decision: finish call, then Apply, runWatch, replay.go, watch.go, realcheck.go, Check (istart's
  `uint.Z s0.rv' < 2^62`), the discharge list; report at step 5's end; step 6 prep, STOP for the Freeze.
- Pitfalls (new): `ipersist` needs a WP/fupd goal (do it before the last `wp_auto`); `swap` does not exist
  (`by_cases …; case neg => …`); `rw [if_pos h0]`/`if_neg` on `kStep`'s kind tests (simp leaves `W64 1 = W64 0`);
  `exact hA` against a goal about another seeded kv times out at whnf (split the cases by hand).

### Superseded (night 10b)

**2026-11-19 (night 10b; for etcd-grove-03). MakeSlice attack ACCEPTED (minor 2 applied, minor 1 recorded).
STOP: `reflect.Value.IsNil.spec` needs `b = false → s ≠ slice.nil` (trusted text, pending attack).**

- Branch `k8s-7g`, pin 6d365ee1a (`--packages=/shared/tmp/manifest-6d3.json`; switch to manifest-f55 on lean's
  f551a1b46 merge). Why IsNil: `finalizeList`'s `false` branch keeps the caller's slice, and the old post said
  nothing about it, so an empty list's items could be `slice.nil` (questions.md "Night 10"; trust.md top entry).
  Written: `Spec/reflect/Value__IsNil.lean` post `… ∧ (b = false → s ≠ slice.nil)`; Go `TestIsNilFalseNonNil` PASS.
- Done with the accepted MakeSlice fact: `listContractOk'`'s MakeSlice-0 clause gives `⌜s' ≠ slice.nil⌝`
  (ListContract discharges `Hs.2.2.2`; growSlice/finalizeList take it).
- Build `/shared/tmp/k8s7g/build-optA.sh` (log `build-optA.log`) ran: rc 1 on raft kv/kvdurable/kvreconf/kvdurablenoax/
  kvwitness (option A: facts by `rfl`, Get/Read continuations in the `∀ o'` form; fixed, lean-check `-a` clean, not yet
  rebuilt through their Results) and on `k8s/etcd3/Check` (step 5's known work). Rerun it after the IsNil threading.
- Next after the IsNil attack: `finalizeList`'s post and `listIs` (GetList's success post) in a non-nil-items form
  (`∃ pl s, … ⌜s ≠ slice.nil⌝ …`, in place), then step 5 in the order below (night 10).

### Superseded (night 10)

**2026-11-19 (night 10; for etcd-grove-03). Option A ACCEPTED; empty-list blocker: option 1 (questions.md
"Step 5 night 9 decided"). `reflect.MakeSlice.spec` gains `s ≠ slice.nil`: STOP for its independent attack.**

- Branch `k8s-7g`, pin 6d365ee1a (`--packages=/shared/tmp/manifest-6d3.json`; switch to manifest-f55 when lean's
  f551a1b46 merge comes in). Trusted text: `Spec/reflect/MakeSlice.lean` post `s ≠ slice.nil` (header "Never nil"),
  Go `examples/k8s/etcd3/trustspecs_test.go` `TestMakeSliceZeroNonNil` (PASS), `notes/k8s-7g-trust.md` top entry.
  No proof uses it yet (ListContract reads only `Hs.1`; lean-check of the spec: 0 errors).
- Build `/shared/tmp/k8s7g/build-optA.sh` (log `build-optA.log`): queued for a slot (both held by full builds).
  Read it first; fix what it reports.
- After the attack: thread the fact through `listContractOk'`'s MakeSlice-0 clause, `finalizeList`, `GetList.spec`'s
  post (non-nil-items `listAt` form; Freeze list). Then step 5 in order: `RawOk.lean` (`RawRel` moved from
  RealBridge below MDefs, `rawOk x y`, `ioOk` with it), `listOut` gives back `listAtItems`, call's post
  (`plainOut y = …` + `rawOk`), Apply, runWatch (watch.go specs), replay.go (8), watch.go (15), realcheck.go, Check,
  discharge list; report at step 5's end; step 6 prep, STOP for the Freeze.

### Superseded (night 9)

**2026-11-19 (night 9; for etcd-grove-03). Option A done (lintest's applySpec generalized in place); STOP:
blocker on the list's Raw (an empty list's `Items` slice: nil-ness not provable over the store's contract).**

- Branch `k8s-7g`, pin 6d365ee1a (`--packages=/shared/tmp/manifest-6d3.json`). Commit: option A (see git log):
  `lintest.applySpec` returns `o'` with `⌜∀ s, S.M.step s (i, o') = S.M.step s (i, o)⌝`; `wp_apply_commit` takes
  `£ 1 ∗ £ 1`, reopens the invariant at return and swaps the record (`InvOk.swap`, `swapRec`, `run_map_congr`);
  runClient's clock read before the call makes 2 credits; the libraries (counter, logkv*, txnlin, partition, raft
  kv/kvreconf/kvdurable/kvdurablenoax/kvwitness) give `o' = o`; `k8s_etcd3.Apply.spec` returns `o'`
  (`Check`'s closure passes it). Links regenerated with LAKE_OPTS: all identical. Build: `/shared/tmp/k8s7g/
  build-optA.sh` (targets `optA-targets.txt`, log `build-optA.log`).
- BLOCKER (report of night 9): `RawRel` (step 4) needs a list's raw object `.list (some its)` (the real model's
  list is never nil, and `reflect.DeepEqual` tells nil from empty), but for an empty list `GetList`'s `Items` is
  the `reflect.MakeSlice(t, 0, 0)` of `finalizeList`, and neither the trusted `reflect.MakeSlice.spec` nor the
  store's `listContractOk'`/`GetList.spec` says it is non-nil. Go evidence that it is:
  `/shared/tmp/k8s7g/makeslice/main_test.go` (pass).
- Next after the decision: `RawOk.lean` (`RawRel` moved from RealBridge below MDefs, `rawOk x y`, `ioOk` with
  it), `listOut` gives back `listAtItems`, call's post (`plainOut y = …` + `rawOk`), Apply, runWatch (events
  rep, with watch.go's specs); then replay.go (8), watch.go (15), realcheck.go; Check; discharge list.

### Superseded (night 8)

**2026-11-19 (night 8; for etcd-grove-03). STOP: blocker on `call`/`Apply`'s Raw (lintest's commit fixes the
returned value; the store's error is allocated after the linearization point). Floor work done; questions.md
"Step 5 night 7 decided" recorded.**

- Branch `k8s-7g`, pin 6d365ee1a (`--packages=/shared/tmp/manifest-6d3.json`). Commits: `11b0a7ba6a` (RealRun
  checked: update's object by `NoOp` cases, `itemOk_rv`), `66c5987877` (the floor: `floored` spec+proof, `minRVL`
  with the floor, `FloorOk`/`flooredL` moved to KModel, `genList`/`genFrom`/`genWatchFrom`/`genWatch` post
  `FloorOk f x` (premise `uint.Z f < 2^62`), `cacheFloor tbl f` (`newWCache` gives it, `newCache` gives
  `cacheFloor tbl 0`), `Gen` takes it and posts `FloorOk`; InvSteps' `step_box` reads `plainOut`
  (`kStep_plain`, `lOut_plain`, `otherL_plain`); WatchQ commits `plainOut y`).
- Verified: lean-check `-a` of RealRun, RealB4, RealValidate, InvSteps, WatchQ, floored, minRV, genList, genFrom,
  genWatchFrom, genWatch, newWCache, newCache, Gen (0 errors). No slot build this session (queued one cancelled:
  slots held for hours by full builds).
- BLOCKER (report of night 8): `lintest.applySpec` commits `∃∃ s' o` at the linearization point and then must
  `RET #o` (the same value). With `Output.Raw`, `call`'s answer holds the store's `err` (`NewKeyNotFoundError`,
  `NewKeyExistsError`, `NewInvalidObjError`, too-large), allocated after the store's read/txn, so the value to commit
  is unknown at the linearization point (objects and lists are fine: `out`/`l` are allocated before the call; the
  rejection sentinels are globals). Prophecy patches can only resolve u64/bool. Options in the report.
- Next after the decision: call's post (`plainOut y = callOut …` + `rawOk x y`), Apply, runWatch; then replay.go
  (8) and watch.go (15) specs/proofs; realcheck.go; Check (also needs `cacheFloor` from `newWCache` with
  `f = s0.rv`, `uint.Z < 2^62` from `g0.st.rv ≤ |hist| < 2^60`, and `Gen`'s post now `GenInA x ∧ FloorOk f x`).
- Pitfalls (new): `(try trivial)` and `exact hf` (a `2 ^ 62` bound) can hit "maximum recursion depth", which
  `try`/`first` do NOT catch: use `try rfl`, pass such hypotheses as explicit arguments (`wp_apply wp_genList _ _ c
  hasC f hf`); `rw [show W64 0 = …]` rewrites every `W64 0`: rewrite the other way; a zero-valued field is `↦□ 0`
  (`OfNat`), not `W64 0`: state specs with `0`; in a `wp_join`, a pointer the cases read must be persistent
  (`ipersist floor`) or listed.

### Superseded (night 7)

**2026-11-18 (night 7; for etcd-grove-03). Step 5 started after 03's go (questions.md "Step 4 DONE, step 5 go").**

- Branch `k8s-7g`, pin 6d365ee1a (`--packages=/shared/tmp/manifest-6d3.json`). Commits this session: `2dee37288a`
  (B4 returns each watch's configuration: `ReplayAt`, `RunOk`, floor, `watchOkL`, for B5), `9f679c501c` (`plainOut`:
  `outEqual.spec` returns `decide (plainOut a = plainOut b)`; `decOp` gives `ansOf (plainOut y)`; `step.spec`'s post is
  `stepL g x (plainOut y)`; `mlistL_plain`/`mstepL_plain`/`watchOkL_plainOut`; `Model`, `step`, `outEqual` re-checked),
  then `RealRun.lean` + B4's `hpres`/`hn` restated (see Forms).
- Forms decided (report): `plainOut` (KModel, `@[reducible]`); B4's `hpres` as accepted was FALSE (RunOk bounds
  `rv < 2^63`, a write at `2^63 - 1` breaks it): now takes `rv + 1 < 2^63` and returns `rv' ≤ rv + 1`; `drive` carries
  `rv + |l| < 2^63`; `realReplay_ok`'s `hn` is `st0.rv + |H| < 2^63` (was `2^64`). `RealRun.kstepL_runOk` discharges
  `hpres` from `OpFits x` (`crFits x ∧ |Val| < 2^62`).
- FINDING for 03: step 3 left `correctness/replay.go` (8 functions: `NewReplay`, `Replay.Validate`, ...) and
  `watch.go` (15: `WatchValidator.ValidateWatch`, ...) without Go specs/proofs (only model.go + consistency.go are
  done); `realCheck`'s proof needs them. Not on the step-5 list.
- UNCHECKED (written while both build slots were held by other sessions' full builds, no lean-check allowed during a
  build): `RealRun.lean` (new) and the `hpres`/`hn` restatement in `RealB4.lean`. First thing: `lc.sh -a` both
  (RealB4 checked clean before the restatement, at `2dee37288a`).
- Next, in order: read the targeted build (`/shared/tmp/k8s7g/build-s5a.sh`, log `build-s5a.log`) for the broken driver
  files (minRV/genList/genWatchFrom/Gen gained `floor` in step 0: `minRVL` needs `flooredL`; call/Apply/runWatch need
  `plainOut` in their posts plus Raw facts); InvSteps' `step_box` now has `ansOf (plainOut y)`; then call's Raw facts
  (`rawOk x y`: `respRep` of `y.Raw'` with `RawRel x (plainOut y) rr`, persistent, into `ioOk`), Apply, runWatch;
  realcheck.go specs; Check.
- `plainOut` ripple still to do (not yet built): InvSteps' `step_box` (from `decOp_box`) now reads `ansOf (plainOut y)`;
  its linearization-point lemmas (`contAt g0 x otherL Φ`, `kStep_ans`, `lOut_ans` uses at l.602/694/879/910/1032/1345)
  state the model's output as the Go answer. Generalize them to any `y` with `plainOut y = <model output>` (a
  `step_box_plain (hy : plainOut y = o)` lemma), since `call`'s answer carries the store's `Raw`. `Check.spec` needs new
  premises on `g0` for `RunOk g0` (Main discharges them from `seed`'s concrete history).
- Pitfalls: model outputs' `Raw' = zeroValDef` proofs: `unfold …; repeat' split; all_goals (try simp only [apply_ite
  (f := Output.Raw'), ite_self]); all_goals (repeat' split); all_goals rfl` (plain `split` cannot see an `if` under a
  `have`).

### Superseded (night 6)

**2026-11-18 (night 6; for etcd-grove-03). Step 4's bridges B1-B5 proved, no `sorry`: B1-list, B2, B4 this
session. Report at step 4's end sent (discharge list below). Decisions of 03 recorded (questions.md, trust §6).**

- Branch `k8s-7g`, pin 6d365ee1a (`--packages=/shared/tmp/manifest-6d3.json`). Commits this session: `1855dd0b93`
  (B1-list `rstepL_list` in `RealBridge`; B2 `RealLin.realS_isLinearization` over the generic
  `porcupine/Filter.isLinearization_filter`), `2419423e11` (`RealValidate.rvalidateL_point`), `7b1381e273`
  (`RealB4.realReplay_ok`: any `lin2`, `NewReplay` ok, `Validate` accepts all).
- Forms decided (report): `RawRel`'s list items `itemOk`; `CfgOk`, `HistCfgOk`, `RunOk`, `OpOk`, `FloorOk`; `ROp`,
  `kM h0` (`pM (kSpec h0)` with `ansOf`), `realS`, `unaryOf`; B2/B4 take "kstepL keeps CfgOk/RunOk" as premises.
- Verified: all new files by lean-check (full `-a` re-checks) and the targeted build (optC list + `RealB4`, rc 1 only on
  `outEqual` = the known `decide (a = b)` breakage to restate in step 5; every other target up to date):
  `/shared/tmp/k8s7g/build-optC.sh` (log `build-optC.log`).
- Next (step 5, after 03's go): the discharge list (report of night 6 / below); one cheap B4 extension first:
  `drive`/`realReplay_ok` should also return, per watch, a configuration `hv` with `ReplayAt s0 R hv`, `RunOk hv`,
  `watchOkL` (from `kM_step.1`) so B5 composes with the same `R`.
- Step-5 discharge list: per op (`OpOk`): no `EOther` output (`failureFree`), `RawRel x y r` (call's `Raw` post,
  list items `itemOk`), lists: `Match ∈ {0,1,2}`, `listConsL` some, `prepareKeyM [] ListKey` some; others:
  `keyOkL (storeKeyL Key)`; `FloorOk st0.rv` (D7g-1). Configurations: `RunOk h0` (seeded store) and `kstepL` keeps
  `RunOk` on unary ops (pure; needs `inFits`, no wrap); `st0.rv + |H| < 2^64`. Conversion: `H` from `lops`
  (`decOp`/`Raw` → `ROp`), porcupine's run on `fmapH unaryOf H`, `realOkL`'s ops = `vals _ lin2`, `reqRep`.
  B5's (`hreq`, `WatchFromL`, `HistSorted`, length = revision, `rmWf (absR st0)`); `outEqual.spec` restated as
  plain-field equality (decided); `call.lean` broken (pre-existing).
- Pitfalls (new): `W64 0` vs `0` (`0#64`) in goals: rewrite with `w64_z : W64 0 = 0 := rfl` or prove `¬rq = 0` by
  `exact`; `rw [if_neg h]` fails when `(absR st).rv` was simp'd to `st.rv` in the condition only (instance
  mismatch): `rw [if_neg (show ¬ … (absR st).rv … from h)]`; `split`/`cases` on `PStep`/`PSilent` name only the
  non-index fields (`| ok ho`, `| obs o hob hok`, `| perm p hpp`); `erw` for `replayL`'s initial map
  (`(absR st).rv` vs `st.rv`).

### Superseded (night 5)

**2026-11-18 (night 5; for etcd-grove-03). Option (C) done (Go + Lean); B1 for writes and gets proved
(`RealBridge.lean`, no `sorry`); B1-list, B2, B4 left. Paused at a context stop.**

- Branch `k8s-7g`, pin 6d365ee1a (`--packages=/shared/tmp/manifest-6d3.json`). Commits: Go `2324797d5a`
  (`Output.ErrMsg`, `preMsg`, `invalidObj(key, msg)`, `outEqual`; `TestInvalidMsg`; retranslated, goose `--check`
  clean; whole driver Go suite green, log `/shared/tmp/k8s7g/gotest-optC.log`); Lean `b521d378c2` (store model
  `KPreF`/`KErr.invalidObj key msg`/`respIs` with `invalidErrMsg`; specs take `c.S.preF pr`; `errOut`,
  `invalidObj`, new `preMsg`, `mdelete`, `mupdate`, `Refine` (`preMsg_rel`), `Calls`, `Inv`, `MDefs`,
  `outEqual`; RModel's Option-valued `preMsgL` renamed `checkMsgL`); B1 writes `rstepL_write`, gets
  `rstepL_get` (`8dc51b298a`).
- Decision record: `questions.md` "Step 4 STOP decided" (gitignored, local) and `notes/k8s-7g-trust.md` §6
  (Freeze list). The store-vocabulary change (7e-frozen `respIs`) awaits acknowledgement.
- Verified: store files, `Refine`, `Calls`, `errOut`, `invalidObj`, `preMsg`, `mdelete`, `mupdate`, `Inv`,
  `RealBridge` (and its imports `RealWatch`, `ModelFit`, ...) by lean-check; targeted build of the rest queued
  (`/shared/tmp/k8s7g/build-optC.log`: outEqual, MDefs, ListSpecD, KList, RefineList, Apply, InvSteps,
  Model__update/delete, store__Delete/deleteOnce/updateOnce, storage Link). `call.lean` stays broken (step 5).
- Next, in order:
  1. **B1-list**: `rvalidateListL x (absR h.st) (rlistL ..) r` for the driver's `mlistL x h` answer: Exact
     (`listRespRVL = some req`: `histAtL h.hist req` has rv `req`), NotOlderThan (rv in range), consistent
     (`equalListRespL`: `rlistL` on `absR h.st` = the driver's list on the current store: `scopeR`/`ListModel.loop`
     vs `listLoopL`, `prepareKeyM [] ` vs `"/objs"`, `itemsL_absR` gives the key order).
  2. **B2**: a generic porcupine lemma (filtering a history by a predicate under a simulation of models:
     `IsLinearization M H π → IsLinearization M' (filter H) (reindex π)`), then `pM (kSpec h0)` on a failure-free
     history stays a singleton `{⟨h, []⟩}` (no pending: `PReach` from `[]` is the identity), and B1 is the step.
     Statement over `H : List (Op (Input × Output × RResp))`; `realS init` := `SeqModel RM (Input × RResp)` with
     `rstepL`.
  3. **B4**, as scoped (B3b `ReplayAt`, `replayAt_prefix`, B3a to move to porcupine's `lin2`).
- Premises added by B1 (step 5 discharges): `RawRel` per unary op (the Raw/plain-field relation), `keyOkL
  (storeKeyL x.Key')`, `StOk st` (sorted, no `Annotated` object), `rmWf (absR st)`, `0 < st.rv`.
- Note for step 5: `outEqual.spec`'s `decide (a = b)` is false once `Raw` differs (Go ignores `Raw`); known
  pre-existing breakage, to restate as equality of the plain fields.
- Pitfalls (new): never `cat >> /dev/null` before a heredoc (blocks on stdin); a `simp` on `RawRel` with `h4 :
  x.Kind' ≠ W64 4` needs `simp only [..., h4, ↓reduceIte]` (full `simp` turns `W64 4` into `4#64` first);
  `if_neg`/`if_pos` rewriting is more reliable than `simp` for `rexecL`'s kind tests.

**2026-11-18 (night 4; for etcd-grove-03). STOP before B1/B2/B4: B2 as scoped is false (the precondition
message is not in the plain output; questions.md "Step 4 STOP"). Waiting for the choice of fix; nothing else
changed. B3, B5 proved and accepted.**

**2026-11-18 (night 3; for etcd-grove-03). Step 4: B3 (a and b) and B5 proved, no `sorry` in
`RealReplay`/`RealWatch`; B1, B2, B4 left (statements not yet written). Paused at a context stop.**

- Branch `k8s-7g` (worktree `/shared/etcd-grove-k8s7g`), pin 6d365ee1a: `--packages=/shared/tmp/manifest-6d3.json`;
  `.lake/package-overrides.json` = that manifest. lean 1b298c1e70 merged (`741bc81066`).
- Done this session: `RealReplay`/`RealWatch` built through the slot (rc 0); B5 `212cb98b18`, `93e37ced04`
  (`validateWatchL_of_watchOkL`: `fromW` inverts `toWEvL`; the cut is `N ++ E`, `E` at most one error;
  `reliableOkR_prefix` is the core: the window `[max mn (s0+1), mx)` of a prefix `T'` of the driver's `T`,
  `eventsInL_window` + `eventsForRVsL_eq`); nonissue `k8s-correctness-watchrange-requested-rv-wrap` (`6a0ab49a7b`,
  B5's `hreq`); B3a `0062bd8daa` (`replayL_perm`: the accumulator is `runOf init kv` for the writes `kv` that moved
  the RV; `RInv` adds: each object stored past `init.rv` was left by the write at its RV, each write is some op's
  answer (`wrObj`/`gOf`), each op's object answer past `init.rv` is the write at that RV; two runs' `kv` agree index
  by index). Earlier: statements `edee4c6d0f`, B3b `0c6a267190`..`8a27a2b8ae`.
- Forms decided this session (to report): none beyond the accepted ones (B5 needed no new premise past `hreq`).
- Next, in order:
  1. **B1** (scope §2.3): `rexecL x (absR st)` vs `mstepL x st` under `absR`/`respOf`, and the list as `mlistL`
     (`itemsL_absR` in `RealWatch` already gives the key order of `absR`); `rvalidateGetL`/`rvalidateListL` accept
     what `kstepL` accepts. Write the statements as forms of the scope's prose (form decisions; report them).
  2. **B2**: no failed call ⇒ `pM (kSpec h0)` keeps one configuration, no pending write; the unary projection of
     its linearization is one for `realS` (by B1).
  3. **B4**: along any `lin2`: `NewReplay` succeeds; stale Get and Exact/NotOlderThan lists validate (B3b's
     `ReplayAt` at the op's configuration, `replayAt_prefix`, B3a to move to porcupine's `lin2`).
  4. Report at step 4's end.
- Premises still to discharge (step 5): Step's output premises; `WatchFromL`, `HistSorted`, length = revision,
  `rmWf (absR st0)`, B5's `hreq`; `inFits`/`crFits`; `reqRep` from `realRequest`; B3a's `hn` (`init.rv + |l1| <
  2^64`). Pre-existing breakage and step-6 link-list entries as below (History, 2026-11-18 late).
- Pitfalls (new): `etc/lean-check.py`'s first check after an edit sometimes prints the previous diagnostics: use
  `-a` (waits for the file) or check twice; no `swap`, `conv_lhs`, `List.reverseRecOn` (no Mathlib:
  `List.eq_nil_or_concat`); `ext` on `GMap` gives an `Option` `↔` goal: `refine GMap.ext (fun k => ?_)`; `rw` with
  `List.filter_eq_self.2`/`_nil_iff.2` picks the first filter: state the two halves as `have`s; `(repeat' split)
  <;> simp_all` does not `subst` a `{…} = o` (split by hand, `simp only [DeepV.obj.injEq] at h; subst h`).
  Earlier: no Mathlib (`Classical.byContradiction`, `Nat.le_trans`); `split at h` may rewrite the goal; `cases e`
  leaves hypotheses (`generalize … at h ⊢`); `GMap.ofList` unfolds via `show`.
- Build: `/shared/tmp/build-slot.sh lake --packages=/shared/tmp/manifest-6d3.json build MODULE...`
  (LEAN_NUM_THREADS=4; `/shared/tmp/k8s7g/build3c.sh EXTRA…`); check: `/shared/tmp/k8s7g/lc.sh -a FILE`.

## History

- 2026-11-18 night 2 START HERE (superseded): B3b proved; B5's plan (done as planned) and B3a's (done
  differently: the writes as a sequence, not strong induction on revisions).

- 2026-11-18 late START HERE (superseded): step 3 done through `Step`; pitfalls there kept below.

- 2026-11-18 night START HERE (superseded): step 3 update/delete/execute (`af26175d28`, `de06cdaa56`);
  pitfalls kept: `iexists l; iexists _; isplitr; …; iexact Hl` for struct points-to; `have h : … := rfl`
  + `isimp only [h] at H` where `iexact` will not unfold; tryUpdate closure: `iunfold k8s_etcd3.tryUpdateD
  at H'` then `rw [show (0 : w64) = W64 0 from rfl]`; `-…Obj.mk.injEq` in simp on record equalities;
  `iapply wp_fupd` before the last `wp_auto` to `ipersist`/`imod` at the end; `section meta` is a parse
  error; `etc/gen-init.py` needs `PERENNIAL_DIR=/shared/perennial-6d365ee1a`.
- 2026-11-18 evening START HERE (superseded): step 3 to listResponseRV/equalListResponse
  (`284724cd7a`); pitfalls kept: interface calls through `meta.List` need the `haveI : List'.ty ≤u
  InterfaceType _` workaround (perennial-changes.md); `x == nil` on an interface is a `match`
  (`deepRep_nil_iff`/`errRep_nil_iff`); `iunfold deepRep at H`; `wp_start_folded` for `append`
  itself; `ihave … : P $$ [H]` gives P as a goal.
- 2026-11-18 morning START HERE (superseded): pitfalls kept here:
  - `wp_for` takes the whole spatial context: drop every `"_" ∷ True` leftover.
  - A case split whose branches converge before any allocation: `refine ?k` / `rotate_left` /
    `exact ?k`; once `wp_auto` allocates, use `wp_join at next with [...]`. Never `all_goals` over
    the rest of a function.
  - A spec whose post is pure: `wp_apply … as … H` then `icases H with %H`.
  - Struct split/recombine: `typedPointsto_not_null_dup`, `iStructNamed`, `typedPointsto_combine`.
  - `wp_apply` already runs `wp_auto`; `+noauto` when you must `ipersist` first.
  - Driver specs need `[reg : EtcdGrove.k8s.CompactorRegistry]`; proofs `[driver_sem : …etcd3.Assumptions]`.
  - Never `wp_func_call` into `fmt.Errorf` (R1 audit): use its spec.
- Paused 2026-11-18 at the STOP for the attack on V + `SuggestsClientDelay` (`067bd749fa`).
- Paused 2026-11-17 for the Hctx repair, at `0196b813e6` (step 3 through `listItems`).

- Step 2's START HERE (2026-11-17): the pure model in `RModel.lean`/`RReplay.lean` (see the commit
  `2e775cc56e`); `KModel`/`KList` build against `Output.Raw` (its `MDefs.Output_intoVal_inj` was left
  broken and fixed in step 3's first commit).
- Scope and Go experiment `ecf71b5f6a`; experiment patch `notes/k8s-7g-experiment.patch`
  (scratch only; its switches are gone from the real driver); nonissue
  `k8s-correctness-watchvalidator-cut-before-bookmark`.

## Re-running the experiment

```
# scratch tree: git archive k8s-7f6 examples third_party | tar -x -C /shared/tmp/k8s7g/src
# then apply notes/k8s-7g-experiment.patch, and copy upstream's types/model/replay/watch/consistency/
# storage.go (module cache, k8s.io/apiserver@v0.0.0-20261021221356-9c4ec15b8038/pkg/storage/testing/
# correctness) into examples/k8s/etcd3/correctness/ with notes/k8s-7g-d30g.patch applied
cd /shared/tmp/k8s7g/src/examples/k8s/etcd3
export PATH=/usr/local/go/bin:$HOME/go/bin:$PATH TMPDIR=/shared/tmp GOWORK=off GOFLAGS=-mod=mod
systemd-run --scope -q -p MemoryMax=32G go test -count=1 -v -run 'TestD30gRealModel|TestDeepEqualFacts|TestValidatorDepartures' . ./correctness
K8S7G_FLOOR=1 systemd-run --scope -q -p MemoryMax=32G go test -count=1 -v -run 'TestRealChecker$' .
/shared/tmp/k8s7g/partruns.sh   # k = 3, six schedules (K8S7G_SCHED), the floor on
```

Switches: `K8S7G_PATCH` (D30g, default 1), `K8S7G_SETRV` (decimal `SetResourceVersion`, default
1), `K8S7G_FLOOR` (the seed floor, default 0), `K8S7G_TRUNC` (cut after the first Error, default
1), `K8S7G_REQUIRE_OK=1` (fail unless the real checker is `Ok`).
