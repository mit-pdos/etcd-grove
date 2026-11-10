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

4. **`InvSteps.lean`** (no `sorry`, built capped with `Inv`, `Refine`): `kStep_ans` (takes `hc : CfgD c`,
   `hk4`; a `Get` never answers `EOther`), `kvExt_refl`/`kvExt_trans`/`kvNext_ext`/`kvExt_sameHist`,
   `revOwn_next` on `KvNext` (keeps `RevOk`'s history clause), the AU lemmas (`create_au`, `rw_au`,
   `pend_au1`, `pend_rw`, `get_read_au`, `get_maker`) take `hc : CfgD c` and thread `KeysIn`;
   `kStep_err4` is now `kStep_get_ne4`; InvSteps' nullary `errOutL` is KModel's `otherL`
   (`ansOf_otherL`). **`readQ`'s commit condition is `σ.rev = R` only** (a `Get` below its minimum answers
   `ETooLarge`, committed at `R` too); its `n` parameter is unused, to drop with `call`/`Apply`.

5. **Lists in `InvSteps`** (second session, no `sorry`, built capped with `Cache`, 7350 jobs,
   `/shared/tmp/k8s-7e-4/b1.log`): `listOutDriver_err`, `lOut_ans` (a list never answers `EOther`),
   `listCall` (as `getCall`, output `lOut x σ`, no `ansOk`), `listQ c γ γc R σ` (`kvWf ∧ kvWfHist ∧
   kvKeysShort ∧ room`, `γ.r`'s element of `σ`, the commit bit at `R`), `listP σ σ' :=
   ⌜kvSameHist σ σ' ∧ σ.rev ≤ σ'.rev⌝`, `listQ_pure`/`listQP_pure` (`GetList`'s two premises),
   `revOwn_ext`, `list_read_au` (commits with `kOk_list`), `list_later_au` (from `RevOk`'s last clause),
   `list_maker`, `list_makerP`, `listCall_take`.

## Stopped at step 2: `errOut`'s `ETooLarge` (second session, 2026-11-10; reported to etcd-grove-81)

Go `errOut` now calls `storage.IsTooLargeResourceVersion(err)` on every error that is not a
not-found/exists/invalid `*StorageError`, before the sentinel test. Its spec needs a view
(`apierrors.apiErrAt err w`). Views exist for: the too-large `*StatusError` (`tooLargeErrIs`), the
410 `*StatusError` of `listErr` (`.status st []`, `tooLargeV` false), and the sentinels
(`*errorString`: `.plain` from `errors`' method sets, provable). Not for:
- **(A) the client's errors** (`unkErr`'s/`kClientErr`'s `clientErr`): nothing says their type is
  outside `APIStatus`'s type set. Scope §5 assigns this to 7c-3 (not landed).
- **(B) `storage.InternalError`** (`unkErr`'s second branch: `NewInternalError` of a transformer
  error): it has `Unwrap() error` (`errors.go:232`), so it is no leaf and no view fits; its inner
  error is unconstrained (`transformerOk`'s `TransformToStorage` may fail with any `errStrOk` error;
  `NewInternalError.spec`'s post is `True`). New finding, not in the Scope.
Recommended: (A) as the Scope says, via 7c-3 (until then a named pending hypothesis, which reaches
the closed results as `Client.List`/`Client.GetAt` already do); (B) an `ObjSpec` field `trErr` for the
transformer's errors (as `encErr`), `transformerOk`'s error branches conditioned on it,
`NewInternalError`'s post `ie.err' = ei`, `unkErr`'s branch `∃ ie, err = mkOk InternalError ie ∧
c.S.trErr ie.err'`; the driver's `trErr` is `False`. Both change exported statements: 81 decides.
Planned forms, not yet made: `errIs` on `errOutL`, with `(tooLargeErrIs err ∗ ⌜y = tooLargeL⌝)` and the
`EOther` case carrying `∃ w, apiErrAt err w ∗ ⌜tooLargeV w = false⌝`; `GenIn x := InOk x ∧ kind ≤ 4 ∧
Val ≤ 2^20 ∧ CachedNoRV x`; `call`/`Apply` take `threadTok` (lintest's `applySpec` lends it) and
`⌜threadBound GF ≤ 2^30-1⌝`; `callPre`/`callAt` gain the list kind (`listQ`/`listP`-shaped `QL`, `PL`).

**Decided by etcd-grove-81 under the user's delegation (2026-11-10), as recommended:**
(A) stays with 7c-3; the driver carries a named pending hypothesis until then; k8s-7e lands after 7c-3
and 7e-1. (B) approved: `ObjSpec.trErr`, `transformerOk`'s error branches under it,
`NewInternalError`'s post `ie.err' = ei` (a proved spec, `Proof/k8s_io/apiserver/pkg/storage/
NewInternalError.lean`: no trusted text, so no Go test needed), `unkErr`'s InternalError branch
`∧ c.S.trErr ie.err'`, the driver's `trErr` `False`; every other `ObjSpec` instance gets a true
`trErr` (there is none: `driverSpec` is the only one, checked by grep). Planned forms accepted.
**(B) done** (third session): built capped with the compactor's `Results`, the store's and cacher's
`Link`, the driver's `ObjSpec`/`Contract`/`ListContract`/`InvSteps`/`Cache` (7982 jobs,
`/shared/tmp/k8s-7e-4/b2.log`).

## Third session (2026-11-10): (B), `Calls`, `errOut`, `call.spec`; stopped for context

Done (each commit checked; capped builds `/shared/tmp/k8s-7e-4/b2.log`, `b3.log`, `b4.log` green):
- (B) above (`ca80696501`).
- `Calls.lean` (no `sorry`, lean-check clean): `sentV` moved up; `clientErrPlain` (the pending hypothesis
  of (A): `∀ ii, clientErr (ok ii) → typeSetContains ii.ty APIStatus.ty = false`; write it
  `clientErrPlain (sem := sem)`, else instance search sticks); `notTooLarge err := ∃ w, apiErrAt err w
  ∗ ⌜tooLargeV w = false⌝`; `errIs` on `errOutL`, disjuncts in order notFound, exists, invalid,
  **tooLarge** (`tooLargeErrIs ∗ ⌜y = tooLargeL⌝`), sentinel, other (`⌜y = otherL⌝ ∗ notTooLarge err ∗
  …`); `drvInit_sents` (the sentinels from `drvInit`; `errVarOk` is an abbrev `icases` cannot open);
  `clientErr_notTooLarge`; `unkErr_errIs` takes `hpl : clientErrPlain` and gives `errIs err otherL`
  (InternalError and encErr branches are `False` for the driver); `sentV_plain` (`*errorString` is
  `.plain`: `go_type_set` and its method set); `respIs_call`'s tooLarge case is the new disjunct;
  `GenIn x := InOk x ∧ Kind ∈ {0..4} ∧ Val ≤ 2^20 ∧ CachedNoRV x` (so `.2.2.1` is the value bound,
  `.2.2.2` `CachedNoRV`); `delete_noOdd`/`delete_user` take the `HasReject` bool; `listPre c QL PL`
  (GetList's two update premises); `callOut c eD eU x σ` (`lOut` for a list, else `kStep`'s).
- `errOut.lean`: proved; takes `wp_IsTooLarge : storage.IsTooLargeResourceVersion.spec`. **Add it to
  `etc/link-lean-first-k8s-etcd3.txt`'s `errOut` line at the Link step.**
- `Spec/.../call.lean` restated (accepted forms): binders `QL PL`; premises `clientErrPlain (sem :=
  sem)`, `threadBound GF ≤ 2^30-1`, `QL`'s and `QL ∗ PL`'s `GetList` premises; pre `threadTok ∗ (if
  Kind = 4 then listPre c QL PL else callPre …)`; post `threadTok ∗ (⌜y = otherL⌝ ∨ ∃ σ, (if Kind = 4
  then □ QL (σ.rev) σ else callAt x Φ Q σ) ∗ ⌜y = callOut c eD eU x σ⌝)`.

Next, in order:
1. `call.lean`'s proof: the old branches with `threadTok` framed through, `y = callOut` (`if_neg`),
   `unkErr_errIs … hpl`, `otherL` for the old `errOutL`, `rejD eD x.HasReject' x.Reject'`, the 8-field
   `Obj` (`objAtD_pt` now takes `o.toObj n`; `cachedOk_of`'s `e` must be redone with `DObj.toObj`).
   The **list branch** (`in.Kind == KList`): `l := &ObjList{}` (an `L.listAt lx [] 0 [] none` for the
   driver's `driverListSpec`, `ListSpecD.lean`), `listOptions` (`listOptsV x`), `store.GetList.spec`
   (its pure premises from `InOk`'s list conjuncts and `prepareKeyM`, `selPredOk` from `PredOk.lean`'s
   `predOk_driver`, `listContractOk` from `ListContract.lean`'s `driver_listContractOk`, `rangeStreamOff`
   from where `New`'s callers get it, ctx facts as for `Get`), then on `listErr` `errOut` with
   `errIs err otherL` (`unkErr_errIs`, or the 410 view: `.status st []`, `tooLargeV` false, `ErrOther` as
   for a `*StatusError`), on `tooLargeErrIs` `errOut` with the tooLarge disjunct, else a **new
   `listOut.spec`** (`listOut(l)`: `encodeItems`, `ListRV`, `Continue`, the remaining count pointer)
   giving `listOutDriver x R a` from `listIs`; then `lOut x σ = …` by unfolding `lOut` with
   `parseRVD`/`prepareKeyM` (the `matchOptL`/`listRevL` of `listOptsV x`).
2. `Apply.spec`/proof: take and return `threadTok`, `clientErrPlain`, `threadBound`; Get path's `readQ`
   `n` drop; the list path with `listCall`, `list_maker`, `list_makerP`, `listQ_pure`, `listQP_pure`,
   `listCall_take` (`InvSteps`), `lOut_name` for `ansOk`.
3. The generator, Check, Main* (handoff step 4 of etcd-grove-81's list), then report.

## Fourth session (2026-11-10): `call` proved

Done (each commit checked; `call`, `listOut` built capped, `/shared/tmp/k8s-7e-4/b8.log`):
- `call.lean` proved (no `sorry`) on the restated `call.spec` (`25ff73d407`): the old branches with
  `threadTok`, `otherL`, `callOut`, `splitKey` (a new callee), the 8-field `Obj` (`mkObj_toObj`,
  `updObj_cases` redone, `storedSize_small` on `encodeWith tagV1 (o.toObj 0)`); the list branch:
  `&ObjList{}` split by `iStructNamed` into `driverListSpec.listAt … [] 0 [] none`, `predOk_driver`,
  `driver_listContractOk`, `background_neverDone` (local: `ctxNeverDone` of `Background()`),
  `store.GetList.spec`, then `listErr_errIs` (EOther), `list_tl` (ETooLarge, `errOut`'s tooLarge
  disjunct) or `list_ok` (`listOut`, `listObjOut_eq`: `listOutDriver`), against `lOut` (`hout`).
- New `listOut.spec`/proof (`listObjOutL` in `ListSpecD`), `Calls.listErr_errIs`.
- Forms decided (report at the step-4 checkpoint; `questions.md` is gitignored, so they are here):
  1. `cachedObjOk` gains `ob.Annotated' = false` (`objAtD` holds an annotation-free record).
  2. `InOk`'s list conjunct gains `x.ListKey'.length ≤ 2 ^ 20` (GetList's `opKeyMax`; Gen draws
     short keys: **Gen's proof must give it**).
  3. `call.spec` gains `c.resourcePrefix = "/objs"`, `c.di = decoderI`, `c.vi = versionerI`, and the
     persistent pre `rangeStreamOff` (GetList's premises). **Apply/Check/Main discharge them**
     (`rangeStreamOff` from `noStreaming` in Main; `c.di`/`c.vi` from `New`'s post).
  4. `call.wp_proof`'s callees: `+ splitKey, listOptions, listOut, store.GetList` and
     `predOk_driver`'s 7 (`SelectionPredicate.Matches/Empty`, `labelSel.Matches/Empty`,
     `fieldSel.Matches/Empty`, `getAttrs`), `driver_listContractOk`'s 6 (`apimeta.GetItemsPtr`,
     `reflect.MakeSlice/Copy/Append`, `decoder.DecodeListItem`, `versioner.UpdateList`). **Put them
     on `call`'s line of `etc/link-lean-first-k8s-etcd3.txt` at the Link step**, with `listOut`'s
     line (`encodeItems`).

Next: step 2, `Apply` (below), then 3-6 of etcd-grove-81's list.
- `Apply.spec`: lintest's `applySpec` is `{{ inOk i ∗ threadTok }} … {{ RET #o; ioOk ∗ threadTok }}`;
  add `threadTok` both sides, premises `clientErrPlain (sem := sem)`, `threadBound GF ≤ 2^30-1`,
  `c.di = decoderI`, `c.vi = versionerI`, and `rangeStreamOff -∗` with the other persistent args.
- Every `wp_call` use: new args `QL PL` (non-list: `fun _ _ => True`, its premises trivial),
  `hc hrp hdi hvi hAs hse hpl htb …`, the pre's `rangeStreamOff ∗ threadTok`, the post's
  `threadTok ∗ …`, `callOut` (`if_neg`) for the old `(kStep …).2`.
- `Hgen.2.1` has five cases now (`Kind = 4` the list). List, prophecy `EOther`: as a `Get`'s
  (`read_err_commit`); else `listCall`/`list_maker`/`list_makerP`/`listQ_pure`/`listQP_pure`/
  `listCall_take` (`InvSteps`), `lOut_ans`/`lOut_name` for `ansOk`.
- `readQ`'s unused `n`: drop it (InvSteps, Apply).

## Forms decided (accepted by etcd-grove-81, 2026-11-10, all five)

1. `Refine`: `ItemRel`/`PairRel` → `KRel` over 7e-3c's `PairRelH`; `mkObj` moved to `Refine`
   (`crObjL`/`mkObj`, premises `crFits`/`inFits`).
2. Store: `KvNext` gains `KvExt`; `k8sAu1`/`k8sAuRW` COMM gain `KeysIn c.pfx σ σ'` (hypotheses `hk` of
   `k8sAu1_kvAu1`/`k8sAuRW_kvAu1`/`k8sAusRW_kvAu1`). Accepted on condition that every consumer outside
   the driver builds: checked 2026-11-10 with `etc/importers.py` (`--uses KvNext/k8sAu1/k8sAuRW/
   k8sAu1_kvAu1/k8sAusRW_kvAu1/StepOk` on `Updates.lean`, and on the store's write specs): outside the
   store's own package and the driver, the only importers are the compactor's `MainLinked`/`Adequacy`/
   `Results` (plus list-path specs that do not use them); targeted capped build of
   `compactor.Results`, `cacher.Link`, `etcd3.Link`: green, 7952 jobs (`/shared/tmp/k8s-7e-4/imp.log`).
3. `Inv`: `InOk` grown (workload key, UID/node/app < 256, RV < 2^63, the list's match/prefix/limit/
   `prepareKeyM`); `KOk` over `HSt` (`KRelH`, history length, `kvWfHist`, `keysOk`); `CfgD c` premise of
   the update lemmas; `RevOk`'s history clause; `histOwn` in `Inv` renamed `shistOwn`.
4. `readQ`: a `Get` commits at the prophesied revision whatever its minimum (`n` unused until
   `call`/`Apply`).
5. The list read updates moved from step 2 to the start of step 3.

## Next, in order

1. ~~Lists in `InvSteps`~~ (done, item 5 above). Was: `listCall`/`list_read_au`/`list_maker`, as `getCall`/`get_read_au`/
   `get_maker`, with `lOut x σ` for `(kStep …).2`, `lOut_name` for `ansOk` (a list caches nothing),
   `kOk_list` for the commit. The first page's `Q R σ` must give `kvWf c σ ∧ kvWfHist c σ ∧ kvKeysShort σ`
   (`H.wf`, `H.hwf`, `keysOk_short σ H.keys`) and record `σ` in `γ.r` (`revOwn_elem`). The later pages'
   `P σ σ'` (B5 (a), Scope §5): fire at the server's state `σ'`, open `kInv`, read `σ`'s element of `γ.r`
   against `RevOk`'s third clause: `KvExt σ σ'` gives `kvSameHist σ σ' ∧ σ.rev ≤ σ'.rev`
   (`kvExt_sameHist`); `P σ σ' := ⌜kvSameHist σ σ' ∧ σ.rev ≤ σ'.rev⌝ ∗ …` (check what
   `store.GetList.spec`/`pagedChunks` need of a later page's `P` first).
2. `Cache.lean` checks unchanged (lean-check, 2026-11-10). `Calls.lean` (errors from line 59: `errIs`'s
   7-field `Output` literals → `errOutL e k r`, an `ETooLarge` branch (`apierrors.tooLargeErrIs`, as
   `IsTooLargeResourceVersion`'s spec gives), `errVarOk` destructuring, `KErr.tooLarge` in `outOf`'s
   cases, `delete_noOdd` gone), then `Calls.lean` (`GenIn` with `InOk`'s new
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
