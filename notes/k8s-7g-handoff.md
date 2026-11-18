# k8s 7g (the maintainers' checker): handoff

## START HERE

**2026-11-18 (night 2; for etcd-grove-03). Step 4 in progress: B3b proved; B3a and B5 left (`sorry`), then
B1, B2, B4 (scope §5). Statements accepted (questions.md "Step 4 statements decided").**

- Branch `k8s-7g` (worktree `/shared/etcd-grove-k8s7g`), pin 6d365ee1a: `--packages=/shared/tmp/manifest-6d3.json`;
  `.lake/package-overrides.json` = that manifest. lean 1b298c1e70 (fmt-soundness) merged (`741bc81066`, clean, no
  repair needed: every step-3 target rebuilt, rc 0 but for the WIP RealReplay at the time).
- Done: statements `edee4c6d0f`; B3b `0c6a267190`..HEAD: `simR_init`, `simR_step`, `replayAt_prefix` and helpers
  (`chgListL_filter`/`_snoc`, `rstepL_true`, `rexecL_bump`, `ofList_items`/`_rewrites`, `fI_eq_of_absR`,
  `kstepL_hist`). Forms (to report): `SimR` gains `s0 ≤ rv` and `rmWf acc.1` (so `simR_init` takes
  `rmWf (absR h0.st)`, already an accepted step-5 discharge); B5 gains `hreq` (MinRV parses below `2^63`,
  from `InOk`): without it B5 is FALSE (`watchRangeL`'s `req+1` wraps at `2^64-1`, the driver's Nat range does not).
  RealReplay now imports `KWatchBridge` (for `changeAtL_one`, `fI`, `SortedI`).
- Next, in order:
  1. **B5** (`RealWatch.lean`). Plan: `fromW` (inverse of `toWEvL` on `t < 5`; `raw = all.map fromW` since
     `watchOkL` rejects `t ≥ 5`); the cut `C` of `realEventsL` is a prefix of `all` with an error only last;
     `lastErrOkL` from that; `bookmarksOkR (C.map fromW)` ↔ `bookmarksOkL (nonErr C)` (state map `uint.nat`,
     exact: `wmax`/comparisons are by `uint.nat`), prefix of `nonErr all`; reliable part: `E := tail.filter (t≠3)
     = eventsInL x hs lo hiF` (driver), RVs strictly increasing (`HistWf`: `evAtL` at `r` has RV `r`), later
     events of the full list have RV `≥ hiT` (events increase; a non-bookmark after a bookmark `b` is `> b`,
     `bmStepL`'s `lb`), so `eventsInL lo' hiT = T'`; `lo'`/`lo` window lemma (all `T'` RVs `≥ f(loT)`);
     revisions `≤ s0` give no event (`WatchFromL`); then `eventsForRVsL R x lo hi = (eventsInL x hs lo hi).map
     fromW` for `s0 < lo`, `hi ≤ rv+1` from `ReplayAt.2` (`chgListL`; `evAtL` needs `2 ≤ r`: `1 ≤ s0`).
     Watch-list: initial events = `listItemsL x WKey (absR (histN brv))` (sorted keys: `sortedKeysL_unique`,
     `storeKeyL` keeps the order) and `ReplayAt.1` at `brv` (`s0 ≤ brv` by `WatchFromL`). Existing lemmas:
     KWatchStream `eventsInL_split`/`_one`/`_eq_nil`, `evRangeL_cons`, `bmStepL_none_foldl`.
  2. **B3a** `replayL_perm`. Plan: by strong induction on revisions `r` from `init.rv`: the bump at `r` in `l1`
     (op A) and in `l2`: same op → same state (deterministic from equal states); else A is a no-op update in
     `l2` returning the stored object at A's key with RV `r` (`rmWf`: init objects `≤ init.rv`; invariant: an
     object stored at `k` with RV `> init.rv` was written by the bump at that RV at `k`), so the `l2` bump at
     `r` wrote the same object at the same key; states and changes equal (`rewrites ⊆ items` for create vs
     update). Number of bumps equal by symmetry. `rexecL_bump` gives the shape of a bump.
  3. B1, B2, B4 (scope §2.3), statements as forms of the scope's prose; then report at step 4's end.
- Premises still to discharge (step 5): Step's output premises; `WatchFromL`, `HistSorted`, length = revision,
  `rmWf (absR st0)`, B5's `hreq`; `inFits`/`crFits`; `reqRep` from `realRequest`. Pre-existing breakage and
  step-6 link-list entries as below (History, 2026-11-18 late).
- Pitfalls (new): no Mathlib (`by_contra`, `le_trans` absent: `Classical.byContradiction`, `Nat.le_trans`);
  `split at h` on a `match` may rewrite the goal too (`try rw [hs]`); `cases e` does not touch hypotheses
  (`generalize … at h ⊢` first); `GMap.ofList` unfolds to `<[k := v]>` via `show`.
- Build: `/shared/tmp/build-slot.sh lake --packages=/shared/tmp/manifest-6d3.json build MODULE...`
  (LEAN_NUM_THREADS=4; `/shared/tmp/k8s7g/build3c.sh EXTRA…`); check: `/shared/tmp/k8s7g/lc.sh -a FILE`.

## History

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
