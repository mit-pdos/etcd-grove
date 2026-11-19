# k8s 7g (the maintainers' checker): handoff

## START HERE

**2026-11-19 (night 10b; for etcd-grove-03). MakeSlice attack ACCEPTED (minor 2 applied, minor 1 recorded).
STOP: `reflect.Value.IsNil.spec` needs `b = false → s ≠ slice.nil` (trusted text, pending attack).**

- Branch `k8s-7g`, pin 6d365ee1a (`--packages=/shared/tmp/manifest-6d3.json`; switch to manifest-f55 on lean's
  f551a1b46 merge). Why IsNil: `finalizeList`'s `false` branch keeps the caller's slice, and the old post said
  nothing about it, so an empty list's items could be `slice.nil` (questions.md "Night 10"; trust.md top entry).
  Written: `Spec/reflect/Value__IsNil.lean` post `… ∧ (b = false → s ≠ slice.nil)`; Go `TestIsNilFalseNonNil` PASS.
- Done with the accepted MakeSlice fact: `listContractOk'`'s MakeSlice-0 clause gives `⌜s' ≠ slice.nil⌝`
  (ListContract discharges `Hs.2.2.2`; growSlice/finalizeList take it).
- Build: `/shared/tmp/k8s7g/build-optA.sh` (log `build-optA.log`), ran this night: see the report / log.
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
