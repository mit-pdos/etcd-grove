# k8s 7g (the maintainers' checker): handoff

## START HERE

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
