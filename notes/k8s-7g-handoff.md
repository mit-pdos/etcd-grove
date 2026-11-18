# k8s 7g (the maintainers' checker): handoff

## START HERE

**2026-11-18 (evening; for etcd-grove-03). Step 3 in progress: listResponseRV and equalListResponse
proved; checkpoint report sent (large context).**

- Branch `k8s-7g` (worktree `/shared/etcd-grove-k8s7g`); lean fb68edfec8 merged (`4efa3c4d43`, pin
  6d365ee1a). `--packages=/shared/tmp/manifest-6d3.json`; `.lake/package-overrides.json` = that manifest.
  Scope: `notes/k8s-7g-scope.md`. Decisions: `questions.md` (local, untracked).
- Done: steps 0-2; step 3 so far: `keyInScope`, `checkKey`, `Get/ListReadConsistency`, `NewEmptyModel`,
  `Model.Clone/Equal/get/create/listItems/validCacherContinue/list` (to `897279346e`), and
  **`Model.listResponseRV`, `Model.equalListResponse`** with driver `ObjList.GetResourceVersion/
  GetContinue/SetContinue/DeepCopyObject` (`284724cd7a`). All build in a slot or check clean (`-a`).
- Next, in order: `update`/`delete`/`execute`, then `validateGet`/`validateList`/`Step`, then step 4.
  - `update`/`delete` need (forms, proved specs): `storage.NewInvalidObjError.spec`'s post to name the
    inner error (`errors.New(msg)`: `Proof/errors/NewVarCell.lean` has the cell), and
    `storage.Preconditions.Check.spec`'s invalid case to give the message (`SprintfOut.v_str`), since
    `invalidE` is a deep view with the message; a premise that the model's items fit `DObj`
    (`tryUpdateD` takes `objAtD`) and `inFits x`.
  - OPEN (asked in the report): `reflect.DeepEqual.spec_k8s` clause 2 needs deep views of both
    errors, but `Step`'s write branch, `validateGet` (MinRV "") and `validateList`'s consistent branch
    (`equalListResponse`) compare an output that may hold a too-large error. Either a premise on
    `Step`'s output, or a clause "a too-large `*StatusError` vs a deep error: false" (trusted).
- Known breakage, pre-existing since step 0 (step 5 re-proofs): `call`, `consume`, `Check`, `Gen`,
  `genList`, `genFrom`, `genWatch`, `genWatchFrom`, `minRV`, `newWCache`, `outEqual`, `runWatch`,
  `watchEvents`, and the driver's `Link`/`Results`.
- `etc/tcb-baseline.txt` and the collections do not list the 7g axioms yet (step 6).
- Pitfalls (new):
  - Interface method calls through `meta.List` (`accessor.GetResourceVersion()`): add
    `[meta_sem : …api.«meta».Assumptions] [metav1_sem : …apis.«meta».v1.Assumptions]` and the
    `haveI : List'.ty ≤u InterfaceType _ := ⟨hle2.underlying_unfold.trans hle1.underlying_eq⟩` of
    `Model__listResponseRV.lean` (notes/perennial-changes.md, 2026-11-18).
  - `x == nil` on an interface becomes a `match x, nil`: `rcases iface_cases x` then `rw` (or
    `deepRep_nil_iff`/`errRep_nil_iff`, Defs.lean). Unfold deep views in the context with
    `iunfold deepRep at H` (plain `unfold` leaves proof mode).
  - `wp_start` runs `wp_func_call`; for a lemma about `append` itself use `wp_start_folded`.
  - `ihave … : P $$ [H]` gives P as a goal with H, not a wand: state such facts as lemmas.
- Older pitfalls: see History (2026-11-18 morning START HERE).
- Build: `/shared/tmp/build-slot.sh lake --packages=/shared/tmp/manifest-6d3.json build MODULE...`
  (both slots are often busy for an hour); check: `/shared/tmp/k8s7g/lc.sh -a FILE` (lean-check with a
  filtered view; full output in `/shared/tmp/k8s7g/lc.out`).

## History

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
