# k8s 7g (the maintainers' checker): handoff

## START HERE

**2026-11-18 (night; for etcd-grove-03). Step 3: update/delete/execute proved; STOP for the
independent attack on `reflect.DeepEqual.spec_k8s` clause 4 (new trusted text) before
`validateGet`/`validateList`/`Step`.**

- Branch `k8s-7g` (worktree `/shared/etcd-grove-k8s7g`), pin 6d365ee1a: `--packages=/shared/tmp/manifest-6d3.json`;
  `.lake/package-overrides.json` = that manifest. Scope `notes/k8s-7g-scope.md`; decisions `questions.md`
  (untracked; last two sections); trust `notes/k8s-7g-trust.md` (top: clause 4).
- Done this round: clause 4 + Go test `TestDeepEqualTooLarge` (`54eee2867d`, PENDING attack); Check /
  NewInvalidObjError posts name the message, driver `errVarOk` holds the errorString, `Model.delete`
  (`70a127d5d3`); `Model.update`, `rvStr_inj` → Codec (`7b9ccdeba2`); `Model.execute` + `reqRep`
  (`af26175d28`); Calls fix (next commit). Targeted build `/shared/tmp/k8s7g/build3b.sh` (all of the
  above + Model__update/execute, Init, Calls, store GuaranteedUpdate/conditionalDelete): rc 0
  (`/shared/tmp/k8s7g/build-s3c.out`, 8086 jobs). `etc/gen-init.py --check` clean.
- Next, in order (after the attack): `validateGet`, `validateList`, `Step` (clause 4 for the output's
  too-large error; a premise excluding `.other` expected errors); then step 4.
- Premises to discharge in this branch (questions.md, night forms): `itemsFitL` invariant, closures
  non-nil (strengthen `tryUpdateFor`/`validateFor` posts), `reqRep` from `realRequest`.
- Known breakage, pre-existing since step 0 (step 5): `call`, `consume`, `Check`, `Gen`, `genList`,
  `genFrom`, `genWatch`, `genWatchFrom`, `minRV`, `newWCache`, `outEqual`, `runWatch`, `watchEvents`,
  driver `Link`/`Results`. `etc/tcb-baseline.txt` and collections not updated for 7g axioms (step 6).
- Pitfalls (new):
  - `iexists l, _` then `iframe Hl` can fail on a struct points-to: `iexists l; iexists _; isplitr; …; iexact Hl`.
  - `iexact` does not unfold `rvStr (W64 0)` / `DObj.ofObj … .uid`: state facts with `have h : … := rfl`
    and `isimp only [h] at H`, or give the model's equation in the reduced form.
  - A tryUpdate/validate closure: `ihave #H' := H; iunfold k8s_etcd3.tryUpdateD at H'`, then
    `rw [show (0 : w64) = W64 0 from rfl]` (TTL) before `iapply H' $$ %x %o %r %_ [Ho]`.
  - simp on `decide ({o with RV := 0} = {u with RV := 0})` expands `Obj.mk.injEq`: pass
    `-…etcd3.Obj.mk.injEq` and close the leftover implication with `simpa`.
  - `ipersist` of a fresh points-to after `wp_apply` finished the program: `iapply wp_fupd` first,
    `imodintro` before `iapply HΦ`. Spatial leftovers before `ipureintro`: `iclear «$res0» …`.
  - `section meta` is a parse error (keyword); `etc/gen-init.py` needs `PERENNIAL_DIR=/shared/perennial-6d365ee1a`.
- Older pitfalls: History.
- Build: `/shared/tmp/build-slot.sh lake --packages=/shared/tmp/manifest-6d3.json build MODULE...`
  (LEAN_NUM_THREADS=4); check: `/shared/tmp/k8s7g/lc.sh -a FILE` (full output `/shared/tmp/k8s7g/lc.out`).

## History

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
