# k8s 7g (the maintainers' checker): handoff

## START HERE

**2026-11-18 (resumed after the attack; for etcd-grove-03). Step 3 in progress; checkpoint report sent.**

- Branch `k8s-7g` (worktree `/shared/etcd-grove-k8s7g`); lean 49bd7924e6 merged (`4063a12bf8`, pin
  6d365ee1a). `--packages=/shared/tmp/manifest-6d3.json`; `.lake/package-overrides.json` = that manifest.
  Scope: `notes/k8s-7g-scope.md`. Decisions: `questions.md` (local, untracked).
- Done: steps 0-2; attack on V + `SuggestsClientDelay` passed, R2/R4 applied, axiom file added
  (`1674097f92`); step 3 proved so far: `keyInScope`, `checkKey`, `Get/ListReadConsistency`, driver
  `Obj.DeepCopyObject`/`SetResourceVersion`, `newObjList` (new), `NewEmptyModel`,
  `Model.Clone/Equal/get/create/listItems/validCacherContinue`, **`Model.list`** (`897279346e`);
  `errRep .other` now says `≠ nil` (`cf3b9ec2ae`, form).
- Next, in order: `listResponseRV` (needs new driver specs `ObjList.GetResourceVersion` (via `rvString`),
  and a premise: output object nil or a list, since `ListAccessor.spec` has no `*Obj` row);
  `equalListResponse` (`ObjList.GetContinue/SetContinue/DeepCopyObject` specs; `reflect.DeepEqual.spec_k8s`
  clause 2); then `update`/`delete`/`execute`; `validateGet`/`validateList`/`Step` (needs `errRep .tooLarge
  delay` tied to `SuggestsClientDelay`'s answer: add `∃ st d, …, delayV st d = (_, delay)` to errRep's
  tooLarge case, provable from `NewTooLargeResourceVersionError`'s details); then step 4.
- Known breakage, pre-existing since step 0 (step 5 re-proofs; not from the merge): `call`, `consume`,
  `Check`, `Gen`, `genList`, `genFrom`, `genWatch`, `genWatchFrom`, `minRV`, `newWCache`, `outEqual`,
  `runWatch`, `watchEvents` (driver signature/`Output.Raw` changes), and the driver's `Link`/`Results`.
  Everything else in `/shared/tmp/k8s7g/leaves2.txt` builds (`/shared/tmp/k8s7g/build-merge2.out`).
- `etc/tcb-baseline.txt` and the collections do not list the 7g axioms yet (step 6).
- Pitfalls:
  - `wp_for` takes the whole spatial context: drop every `"_" ∷ True` leftover
    (`repeat (irename : ("_" ∷ True : IProp GF) => H; iclear H)`).
  - A case split whose branches converge before any allocation: `refine ?k` / `rotate_left` /
    `exact ?k` (after `clear` of the case hypothesis); once `wp_auto` allocates, use
    `wp_join at next with [hyps the branch reads]` (Model.list's Exact check). Never `all_goals` over
    the rest of a function (copies it).
  - A spec whose post is pure: `wp_apply … as … H` then `icases H with %H` (a `%H` in `as` may vanish
    when the precondition left a side goal: `· iframe #`).
  - Splitting a struct for field loads and recombining for a method call:
    `icases typedPointsto_not_null_dup _ _ _ $$ H with ⟨H, %Hn⟩` before `iStructNamed H`, then
    `iapply typedPointsto_combine _ _ _ Hn; simp only [TypedPointsto.typedPointstoDef, …]; iframe`.
  - `functions f [] ≠ func.nil`: `FuncUnfold.func_unfold` + `go.intoVal_unfold GoFunc` (`getAttrs_ne_nil`).
  - lean-check without `-a` may report 0 errors before reaching them: use `-a` before trusting a check.
  - `wp_apply` already runs `wp_auto`: write `(try wp_auto)` after it; `+noauto` when you must
    `ipersist` before the function returns.
  - Driver specs need `[reg : EtcdGrove.k8s.CompactorRegistry]`; proofs `[driver_sem : ...etcd3.Assumptions]`.
  - Never `wp_func_call` into `fmt.Errorf` (R1 audit): use its spec.
- Build: `/shared/tmp/build-slot.sh lake --packages=/shared/tmp/manifest-6d3.json build MODULE...`
  (both slots are often busy for an hour); check:
  `LAKE_OPTS=--packages=/shared/tmp/manifest-6d3.json etc/lean-check.py --max-open 2 -a FILE`.
- Go runs: `cd examples/k8s/etcd3; GOWORK=off systemd-run --scope -q -p MemoryMax=32G go test
  -count=1 -run 'TestPlainWrapperTypedNil|TestStatusChecksPlain|TestSuggestsClientDelay' .`

## History

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
