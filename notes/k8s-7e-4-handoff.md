# k8s 7e-4 handoff (2026-11-10, branch `k8s-7e`, worktree `/shared/etcd-grove-k8s7d`)

Read first: `notes/k8s-7e-2-handoff.md` ("7e-4 Draft: where it starts", the order), `notes/k8s-7e-scope.md`
§3, §5 (the 7e-4 obligations), §6, and `questions.md` ("k8s 7e-4", the forms decided). Rules:
`/shared/tmp/coord-81/common-rules.md`. Scratch: `/shared/tmp/k8s-7e-4/`. Do not merge lean until
etcd-grove-81 says so.

## Done (first session, 2026-11-10)

1. **`Refine.lean`** (`65b457744d`, no `sorry`): `KRel ks g` over 7e-3c's `PairRelH`/`ItemRelH` (whole
   object at the item's resource version, canonical bit); `krelS_iff` (7e-3c's `KRelS` of etcd's store
   is `KRel` of its `absK`); `outOf` on the 17-field `Output` (`.tooLarge` → `tooLargeL`); `crObjL`,
   `crFits`, `mkObj` (the `Create` object: `splitKeyL` namespace/name, UID, value, node, app; moved here
   from `Inv`); `refine_create` (premise `crFits x`), `refine_delete` (rejection on the node,
   `rejD eD x.HasReject' x.Reject'`), `refine_update` (premise `inFits x`; `updObj_with`,
   `sameObjL_toObj`), `refine_get` (`ETooLarge`).
2. **Store: stronger guarantees to its callers** (`2216c7d274`; a form, `questions.md`): `KvNext`'s step
   case gains `KvExt σ σ'` (same base and compaction, changes a prefix); `k8sAu1`/`k8sAuRW`'s COMM gain
   `KeysIn c.pfx σ σ'` (every new key is old or under the prefix), from new hypotheses `hk` of
   `k8sAu1_kvAu1`/`k8sAuRW_kvAu1`/`k8sAusRW_kvAu1`, discharged by `keysIn_optPut`/`keysIn_optDel`
   (`Steps.lean`) in `store__Create`/`deleteOnce`/`updateOnce`; `FirstRead` gives `keysIn_refl`. The
   store's `Link` builds (capped).
3. **`Inv.lean`** (`cf62d305bc`, no `sorry`; lean-check clean, built capped): see "The invariant's design"
   below.

## Next, in order

1. **`InvSteps.lean`** (the only file of step 2 left; `GSt`→`HSt` and `histOwn`→`shistOwn` already
   replaced, uncommitted edits none). What changes:
   - `revOwn_next`: take `KvNext σ σ'` (not `σ' = σ ∨ rev+1`); keep `RevOk`'s third clause (every entry
     `KvExt` to the current state: transitivity of `KvExt` with the step's, `KvExt σ' σ'` refl). Prove
     `kvExt_trans`, `kvExt_refl` (pure, in `Inv` or here).
   - `inv_next`: the store's COMM now gives `KvNext σ σ' ∧ kvRoom σ ∧ KeysIn c.pfx σ σ'` (create),
     `KvNext σ σ' ∧ KeysIn c.pfx σ σ'` (RW, `b = true`); thread `KeysIn` to `kOk_ok`/`kOk_pend`.
   - `kOk_ok`/`kOk_pend` now take `hc : CfgD c` (from `c.S = driverSpec`, `c.pfx = kpfxD`), `hk4 : x.Kind'
     ≠ W64 4`, `hn : KvNext`, `hki : KeysIn`. `H.ins n x` now gives `InOk x ∧ isWriteL x = true`.
   - `kStep_ans`: `refine_step` needs `KRel (c.abs σ) cf.st.st`: from `krel_abs c hc σ _ _ |>.2 hrel.2.1`.
   - **Gets and `ETooLarge`**: a `Get` above the state's revision now answers `tooLargeL` (Err 6, an
     `.ok` answer), not `EOther`. So `readQ`'s commit condition `n ≤ σ.rev` (D5) goes: the read commits at
     the first firing at the prophesied revision `R`, whatever `n`; `kStep_min` (now "Err ≠ 6 → min ≤
     rev") is no longer needed by `get_read_au`; `kStep_err4`/`read_err_commit` stay for a client error
     (`EOther`). Rename InvSteps' local `errOutL : Output` (clashes with `KModel.errOutL e k r`) to
     `otherL` (KModel's, `errOutL (W64 4) [] 0`), also in `Calls`/`call`/`Apply`.
   - `cachedObj_of_item`/`ansOk_step`/`ansOk_read`: `cachedOf y = objOfL y`, `cachedObjOk`'s pure part is
     now `fitsD ob ∧ ob.ResourceVersion' ≠ W64 0`; `dobjOf_toObj` replaces `dobjOf_mk`;
     `AnsFrom`'s object is `objOutL (o.toObj (W64 rv))`.
   - **Lists, new** (`list_read_au`, `listCall`): as `getCall`/`get_read_au`, with `lOut x σ` for
     `(kStep …).2`, `lOut_name` for `ansOk` (a list caches nothing), `kOk_list` for the commit. The first
     page's `Q R σ` must give `kvWf c σ ∧ kvWfHist c σ ∧ kvKeysShort σ` (`H.wf`, `H.hwf`,
     `keysOk_short σ H.keys`) and record `σ` in `γ.r` (`revOwn_elem`). The later pages' `P σ σ'` (B5 (a),
     Scope §5): fire at the server's state `σ'`, open `kInv`, read `σ`'s element of `γ.r` against `RevOk`'s
     third clause: `KvExt σ σ'` gives `kvSameHist σ σ' ∧ σ.rev ≤ σ'.rev` (prove `kvExt_sameHist`); define
     `P σ σ' := ⌜kvSameHist σ σ' ∧ σ.rev ≤ σ'.rev⌝ ∗ (what getList needs of a later page: kvWf …)`; check
     `store.GetList.spec`'s use of `P` before fixing it.
2. `Cache.lean` (cached objects on the 8-field `Obj`), `Calls.lean` (`GenIn` with `InOk`'s new
   conjuncts: workload key, node/app lengths, `parseRVD … = some n ∧ uint.Z n < 2^63`, the list's match,
   `"/objs/" <+:`, `0 ≤ Limit`, `prepareKeyM … isSome`; `errIs` on the 17-field `Output` with
   `ETooLarge`; `callPre`/`callAt` with the list kind), `call`, `errOut`, `Apply`. Then report (after 2 is
   the checkpoint; the report waits until InvSteps builds).
3. Generator, Link, Adequacy, Results, the Scope §5 discharges (`notes/k8s-7e-2-handoff.md`, 7e-4 order
   items 4-6). The seeds: `kOk_init` needs `KRelH g0 σ0`, `g0.hist.length = σ0.rev` (3), `kvWfHist`,
   `keysOk σ0` (the seeds' keys `ns-1/pod-1`, `ns-2/pod-2`; revision 1 empty).

## The invariant's design (`Inv.lean`)

- `InOk x`: `x.Key' ∈ wkKeysL` (7e-0's four keys), UID/node/app shorter than 256, `∃ n, parseRVD x.MinRV'
  = some n ∧ uint.Z n < 2^63`, and for a list (`Kind = 4`): match ∈ {0,1,2}, `"/objs/" <+: ListKey`,
  `0 ≤ sint.Z Limit`, `prepareKeyM "/objs" ListKey Recursive` some. (`inOk_crFits`, `inOk_inFits`.)
- `KOk c g0 S σ M nx` (`g0 : HSt`): `closed`, `wf : kvWf c σ`, `hwf : kvWfHist c σ`, `keys : keysOk σ`
  (every revision's keys are `mkeyL` of the workload's), `fresh`, `ins` (pending: `InOk ∧ isWriteL`),
  `cfg : ∃ cf, S cf ∧ KRelH cf.st σ ∧ cf.st.hist.length = σ.rev ∧ pend perm`.
- `CfgD c := c.S.dec = driverCodec.dec ∧ c.pfx = kpfxD`; `krel_abs`: `KRel (c.abs σ) g ↔ KRelS σ.store
  σ.rev g`.
- Lemmas: `cfg_step` (a non-list step at related states: `KRelH` of the advanced configuration, the
  history length, the outputs equal), `krelH_step`, `kvWfHist_step`, `keysOk_step` (with `newKey_eq`),
  `keysOk_short` (`kvKeysShort` from `keysOk`), `kvNext_at`, `refine_lOut` (`lOut x σ = mlistL x h`),
  `kOk_init`, `kOk_ok`, `kOk_list`, `kOk_errW`, `kOk_errR`, `kOk_pend`.
- `RevOk Mr σ` gains `∀ n s, Mr !! n = some s → KvExt s σ`.
- Inv's store-history ownership is renamed `shistOwn` (MDefs has the model's `histOwn`).

## Builds

Targeted, capped (check of record until step 5):

```
cd /shared/etcd-grove-k8s7d && export TMPDIR=/shared/tmp
systemd-run --scope -q -p MemoryMax=64G lake build --packages=/shared/tmp/manifest-ddc.json \
  Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Inv \
  Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.InvSteps
```
Edit loop: `LAKE_OPTS=--packages=/shared/tmp/manifest-ddc.json python3 etc/lean-check.py -a -q $PWD/<file>`
(only after the imports are built capped). Green so far: the store's `Link`, `Refine`, `Inv`.

## Pitfalls (this session)

- `swap`, `by_contra` do not exist; `List.Nodup.length_le_of_subset` (core) for counting.
- `decide` instance mismatch after `simp` (goals `decide p = decide p`): finish with `congr`.
- `linkv.` prefixes: `linkv.MStore.put`, `linkv.mStep`, `linkv.runOps`, `linkv.MOp.run`.
- `(kSpec g0).step x c` does not `rw` as `kstepL x c`: `rw [show (kSpec g0).step x c = … from h]`.
