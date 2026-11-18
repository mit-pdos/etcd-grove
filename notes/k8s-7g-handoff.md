# k8s 7g (the maintainers' checker): handoff

## START HERE

**Resumed 2026-11-18 (user, via etcd-grove-03). At the STOP for the attack on V + `SuggestsClientDelay`.**

- Branch `k8s-7g` (worktree `/shared/etcd-grove-k8s7g`); lean b0bb9df7c3 merged (pin 6d365ee1a,
  apierrors-fix). `--packages=/shared/tmp/manifest-6d3.json`; `.lake/package-overrides.json` is that
  manifest. lean has moved since (49bd7924e6, incomingof): merge again before the next full build.
  Scope (approved): `notes/k8s-7g-scope.md`. Decisions: `questions.md` (local, untracked).
- Done: steps 0-2; step 3 proved: `keyInScope`, `checkKey`, `Get/ListReadConsistency`, driver
  `Obj.DeepCopyObject`/`SetResourceVersion`, `NewEmptyModel`, `Model.Clone/Equal/get/create`,
  `validCacherContinue`, `listItems`; `UpdateList.spec` pre weakened (`0196b813e6`).
- Pending attack (trusted text, `notes/k8s-7g-trust.md` top): V in `View.lean` (`plainLeaf`, `.plain`
  arm, M2 header) and `SuggestsClientDelay.spec` (header only; statement unchanged). Go:
  `TestPlainWrapperTypedNil` (new), `TestStatusChecksPlain`, `TestSuggestsClientDelay`.
  Until it passes, these do not build: `Calls.lean` (`clientErr_notTooLarge`: `iexists .plain` needs
  `ileft` + `Or.inr`; `sentV_plain`: same), and the `.plain` branches after `iunfold apiErrAt` in
  `call.lean:143`, `watchChan__syncPaginated:362`, `store__GetList:1094`,
  `handleCompactedErrorForPaging:53`, `interpretListError:93` (the pure fact is now `plainLeaf ∨ wrapper`).
- Next, in order (after the attack): repair those; add `Proof/.../errors/SuggestsClientDelay.lean` axiom;
  `newObjList` spec/proof (driver, `p ↦ zero ObjList`); `Model.list` (loop as `listItems` plus
  `ListModel.lstep`, `mlistPCT.wp_proof`, `meta.SetList.spec_objList`, `UpdateList`); `listResponseRV`,
  `equalListResponse` (ListAccessor `.2`); then `update`/`delete`/`execute` (unblocked by the pin);
  `validateGet`/`validateList`/`Step`; then step 4.
- Known breakage, pre-existing (step 0's `Output.Raw`, fixed in step 5): `call.lean` and the driver's `Link`.
- Pitfalls:
  - `wp_for` takes the whole spatial context: after `iStructNamed` drop its `"_" ∷ True` leftover.
  - `wp_apply` already runs `wp_auto`: write `(try wp_auto)` after it.
  - `wp_apply Hf $$ %M %DFrac.discard [] [HI]`; `iunfold` fails on `modelAt` (use `modelAt_pkg`).
  - A file whose imports are not built hangs lean-check: build it first with the build slot.
  - `#versionerV` parses as `#version`: write `#(versionerV)`. `go!""` → `([] : GoString)`.
  - Driver specs need `[reg : EtcdGrove.k8s.CompactorRegistry]`; proofs `[driver_sem : ...etcd3.Assumptions]`.
  - Pin 6d3: `ArgWf` has a named-string case (one more `Or.inl`).
- Build: `/shared/tmp/build-slot.sh lake --packages=/shared/tmp/manifest-6d3.json build MODULE...`
  (targets of the merge check: `/shared/tmp/k8s7g/targets.txt`); check:
  `LAKE_OPTS=--packages=/shared/tmp/manifest-6d3.json etc/lean-check.py --max-open 2 FILE`.
- Go runs: `cd examples/k8s/etcd3; GOWORK=off systemd-run --scope -q -p MemoryMax=32G go test
  -count=1 -run 'TestPlainWrapperTypedNil|TestStatusChecksPlain|TestSuggestsClientDelay' .`

## History

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
