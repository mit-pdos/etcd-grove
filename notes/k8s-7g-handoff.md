# k8s 7g (the maintainers' checker): handoff

## START HERE

**2026-11-18 (later). Step 3 DONE (decided). Step 4: B3 and B5's STATEMENTS written (proofs `sorry`),
STOP for their review: `RealReplay.lean` (B3a `replayL_perm`, B3b `simR_init`/`simR_step`/`replayAt_prefix`,
vocabulary `rmWf`, `HistSorted`, `chgListL`, `ReplayAt`, `SimR`), `RealWatch.lean` (B5
`validateWatchL_of_watchOkL`; `toWEvL`, `realEventsL`, `WatchFromL`). After the go: prove them, then B1,
B2, B4 (scope §5). lean unchanged since fb68edfec8 (fmt-soundness not landed yet).**

(Previous: step 3 done through `Step`.)

- Branch `k8s-7g` (worktree `/shared/etcd-grove-k8s7g`), pin 6d365ee1a: `--packages=/shared/tmp/manifest-6d3.json`;
  `.lake/package-overrides.json` = that manifest. Scope `notes/k8s-7g-scope.md`; decisions `questions.md`
  (untracked; last three sections); trust `notes/k8s-7g-trust.md` (clause 4 accepted).
- Done this round (commits `6c09889608`..HEAD): clause 4 accepted + m2 header; `itemsFitL` kept by every step,
  non-nil closures (`tryUpdateFor`/`validateFor`); the too-large error's delay and code pinned
  (`NewTimeoutError`/`NewTooLargeResourceVersionError` posts, `errRep .tooLarge`); `storage.isErrCode`,
  `IsNotFound`, `StorageError.Unwrap` specs; `correctness/ErrViews.lean`; `equalListResponse` takes a flat
  output error; `Model.validateGet`, `Model.validateList`, `Model.Step` proved. Forms: questions.md "(late)".
  Targeted build `/shared/tmp/k8s7g/build3c.sh` (output `/shared/tmp/k8s7g/build-s3d.out`).
- Premises still to discharge (step 5): `Step`'s `(rexecL x m).1.err ≠ .other`, `flatE out.err`, the output
  object shapes, `inFits`/`crFits` and the list premises from `realRequest`/`InOk`; `reqRep` from `realRequest`.
- Known breakage, pre-existing since step 0 (step 5): `call`, `consume`, `Check`, `Gen`, `genList`,
  `genFrom`, `genWatch`, `genWatchFrom`, `minRV`, `newWCache`, `outEqual`, `runWatch`, `watchEvents`,
  driver `Link`/`Results`. `etc/tcb-baseline.txt` and collections not updated for 7g axioms (step 6).
  Link lists (step 6) need the new specs: `Model.validateGet/validateList/Step`, `storage.isErrCode/IsNotFound/
  StorageError.Unwrap`.
- Pitfalls (new):
  - Paths that converge with different Lean contexts: `wp_join (v := #b) at (if: (if: #(d) then _ else
    #false) then _ else #false) with [ptrs]` for a condition; for whole branches, `set_option hygiene false
    in local macro` (Model__validateGet). In a macro `$H` is an antiquotation: write `$$ [H]` then `· iexact H`.
  - A predicate defined by `match` (`errRep`, `deepRep`, `apiErrAt`, `errCodeAt`): `simp only [errRep, …]`
    before `iintro`; `unfold` leaves the match.
  - `ihave %h : ⌜P⌝ $$ []` + `· iapply lemma; iframe A B` to apply a lemma whose premise is a `∗`.
  - `wp_apply` already runs `wp_auto`: a following `wp_auto` fails "no progress". `wp_if_destruct` too.
  - `obtain ⟨rfl, rfl⟩` on `n = m` eliminates the variable you still need: `obtain ⟨rfl, h⟩; subst n`.
  - builtin `max`: `have hmax : #(functions go.max [go.uint64, go.uint64]) = max.impl go.uint64 2 :=
    FuncUnfold.func_unfold (f := go.max) (type_args := List.replicate 2 go.uint64)`, `simp only [hmax]`.
  - `simp_all` on large contexts hits max recursion: prove pure facts in separate lemmas (`getL_*`, `listL_*`).
- Build: `/shared/tmp/build-slot.sh lake --packages=/shared/tmp/manifest-6d3.json build MODULE...`
  (LEAN_NUM_THREADS=4); check: `/shared/tmp/k8s7g/lc.sh -a FILE` (full output `/shared/tmp/k8s7g/lc.out`).

## History

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
