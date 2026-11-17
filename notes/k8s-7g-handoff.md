# k8s 7g (the maintainers' checker): handoff

## START HERE

**Paused 2026-11-17 (user, via etcd-grove-03): the Hctx soundness repair goes first; 7g resumes after it lands.**

- Branch `k8s-7g` (worktree `/shared/etcd-grove-k8s7g`); lean 3cd4b72599 merged. Pin c6b39d4f8:
  `--packages=/shared/tmp/manifest-c6b.json`; `.lake/package-overrides.json` is that manifest.
  Scope (approved): `notes/k8s-7g-scope.md`. Decisions: `questions.md` (local, untracked).
- Done: steps 0-2 (`e9bf69f83a`, `47eae5838c`, `11962185aa`, `50faaad1a3`, `2e775cc56e`). Step 3 proved:
  `keyInScope`, `checkKey`, `Get/ListReadConsistency`, driver `Obj.DeepCopyObject`/`SetResourceVersion`,
  `NewEmptyModel`, `Model.Clone`, `Model.Equal`, `Model.get` (`54887034bf`), `Model.create` (`348f1a01da`),
  `Model.validCacherContinue` (`540f6eab11`), `Model.listItems` (`105b090e97`).
- STOP 2 applied (`50be6070ef`): `maps.Keys.spec_objMap` → `(f : GoFunc)`; `ListAccessor.spec` gains the
  `*ObjList` row (reflector callers use `.1`). Both in `notes/k8s-7g-trust.md` §4 for the joint attack.
- Last commit: `versioner.UpdateList.spec` pre weakened in place to `metaAtD` (proved spec;
  `ListContract.lean` frames the items); `ListSpecD.listObjOutL` gets `Raw := zeroValDef`.
- Next, in order: `newObjList` spec/proof (driver, new: `p ↦ zero ObjList`); `Model.list` (loop as
  `listItems` plus `ListModel.lstep` for limit/hasMore/total/lastKey, `mlistPCT.wp_proof` for the token,
  `meta.SetList.spec_objList`, then `UpdateList` on the fields `iStructNamed` gives); `listResponseRV`,
  `equalListResponse` (ListAccessor `.2`); then the step-4 bridges that need no blocked function.
- Blocked: `update`/`delete`/`execute` until the Perennial pin bump to 6d365ee1a (Sprintf `%v`);
  `validateGet`/`validateList`/`Step` until the apierrors fix (soundness-1117). Do not touch View.lean,
  HasStatusCause, IsTooManyRequests, SuggestsClientDelay.
- Known breakage, pre-existing (step 0's `Output.Raw`/`call` change, fixed in step 5): `call.lean`
  (and so the driver's `Link`) does not build; `RefineList`, `ListSpecD`, `ListContract` do.
- Pitfalls:
  - `wp_for` takes the whole spatial context: after `iStructNamed` on an owned struct, drop its
    `"_" ∷ True` leftover (`irename : ("_" ∷ True : IProp GF) => H; iclear H`) or iNamed fails on "?".
  - `wp_apply` already runs `wp_auto`: write `(try wp_auto)` after it.
  - Iris hypothesis with explicit args: `wp_apply Hf $$ %M %DFrac.discard [] [HI]` (the `isPkgInit`
    premise is discharged automatically). `iunfold` fails on `modelAt` (use `modelAt_pkg`).
  - A file whose imports are not built hangs lean-check: build it first with the build slot.
  - `#versionerV` parses as `#version`: write `#(versionerV)`. `go!""` → `([] : GoString)`.
  - Driver specs need `[reg : EtcdGrove.k8s.CompactorRegistry]`; proofs `[driver_sem : ...etcd3.Assumptions]`.
- Build: `/shared/tmp/build-slot.sh lake --packages=/shared/tmp/manifest-c6b.json build MODULE...`;
  check: `LAKE_OPTS=--packages=/shared/tmp/manifest-c6b.json etc/lean-check.py --max-open 2 FILE`.
- Go runs: `cd examples/k8s/etcd3; GOWORK=off systemd-run --scope -q -p MemoryMax=32G go test
  -count=1 -run 'TestListAccessorObjList|TestMapsKeys' .`

## History

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
