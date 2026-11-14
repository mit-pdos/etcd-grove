# auth-lease S2 Draft: the apply layer at the latest state with a lessor

2026-11-14 · branch `auth-lease` · plan `notes/auth-lease-scope.md` §2.2 with the CP0 fixes (approved by
etcd-grove-81, 2026-11-14: `questions.md`). Design before plumbing (`notes/spec-first-plan.md`): each changed
statement old → new, with the callee specs it is proved from. The statements marked **probed** are proved
in `Scratch/AuthLeaseProbe.lean` (unlinked, no `sorry`); they move to their files unchanged up to names.

## 0. What S2 does

The auth-on apply thread's KV methods (`authApplierV3.{Put,Txn}.specL`, `AuthApplyLatest*.lean`) assume
today that the lessor finds no lease (`apply.lookupNil`, `apply.lessorNil`). S2 drops that premise: the
checks run over the lease owner's resource lent from `kvOwn` (`mPreRest_lend`, as the class track does),
the verdict at the latest state includes the lease part (`checkLeasePuts`), the posts carry the lease class
(`kvPostFL` gains `chainLeaseClass`, Q5), and a revocation gets a latest-state triple. S2 keeps the server's
coupling (`srvLessorNil` stays until S3) but repairs the server-side consumers of the changed verdicts (§6,
review r2 F3): `uberKVL_of_base`, `applierKVL_auth` and their `Results` exports lose `lookupNil`/`lessorNil`
premises, and the lemmas that read the latest verdict against the mode-`on` model take the auth-on log's
"no lease" fact (`plainCover`) until S3 replaces it by the lease part of the model.

## 1. Vocabulary (pure, `apply/AuthLatest.lean` or a new `apply/AuthLeaseLatest.lean`)

```lean
/-- the lease part of a check at the latest state, passed: an admin there (no revision check,
`IsAdminPermitted`, `store.go:915-936`), or every key `I` attaches to `id` write-granted there. -/
def apply.leasePassedL (M) (hs) (ai : auth.AuthInfoM) (I : GMap LeaseItem w64) (id : w64) : Prop :=
  latestOk M hs (fun stl => auth.adminOk stl (some ai) ∨
    ∀ k : GoString, I.lookup ⟨k⟩ = some id → granted1 stl ai (k, [], .write))
/-- refused: not an admin there and some key of `id` not write-granted there (CP0 fix 1: a refusal is
`refusedL`'s form, not `¬ leasePassedL`, which `latestOk` makes unprovable at `hs = []` and in `any`). -/
def apply.leaseRefusedL (M) (hs) (ai) (I) (id) : Prop :=
  latestOk M hs (fun stl => ¬ auth.adminOk stl (some ai) ∧
    ∃ k : GoString, I.lookup ⟨k⟩ = some id ∧ ¬ granted1 stl ai (k, [], .write))
/-- the lease's keys of the cache's shape whenever auth is enabled (what makes a key check exact). -/
def apply.leaseShapedL (M) (hs) (I) (id) : Prop :=
  latestOk M hs (fun stl => stl.enabled = true → ∀ k, I.lookup ⟨k⟩ = some id → auth.reqShape k [])

/-- the puts of a wire transaction, nested transactions' and both branches' (CP0 fix 4; in `apply`'s
namespace, beside `txnMay`, review r1). -/
mutual
def apply.opPutsW : txn.TxnOpW → List OpFull | .put o => [o] | .txn _ ts es => opsPutsW ts ++ opsPutsW es | _ => []
def apply.opsPutsW : List txn.TxnOpW → List OpFull | [] => [] | op :: ops => opPutsW op ++ opsPutsW ops
end
def apply.txnPutsW (t : txn.TxnModelW) : List OpFull := apply.opsPutsW t.thenOps ++ apply.opsPutsW t.elseOps

/-- the outcome decided at the latest state for a request checked with permissions `perms` and the
leases `ids` (`authOutL` with the lease part): rejected with a permission or a lease refused, or the
inner chain's outcome with all granted. -/
def apply.authOutLL (M hs ai c rq log) (perms : List Perm3) (I) (ids : List w64) (oc : Outcome) : Prop :=
  (oc = .rejected .auth ∧ (refusedL M hs ai perms ∨ ∃ id ∈ ids, leaseRefusedL M hs ai I id)) ∨
    (chainStep backendStep c rq log oc ∧ passedL M hs ai perms ∧ ∀ id ∈ ids, leasePassedL M hs ai I id)
```

`authOutL` stays a `def`, with the law `authOutL_iff : authOutL M hs ai c rq log perms oc ↔ authOutLL … perms ∅
[] oc` (review r3: an `abbrev` would break every `rcases` on it), so DeleteRange keeps its statement's text.

## 2. The store's contract: `isAuthStoreL` gains the recorded latest state (CP0 fix 2)

Old (`apply/AuthLatest.lean:204`): the three permission checks and `IsAdminPermitted`, each over `L hs`.
New: the same, `∗ □ (∀ hs, L hs -∗ L hs ∗ auth.latestSnap M hs)`.
- Why: `leaseKeysClass`'s admin disjunct (the class `kvPostFL` now states) needs a recorded state; the admin
  triple gives only the latest verdict (`adminVerdictL`).
- Proved from: `isAuthStoreL_of_authInv` (the only constructor) by `latestResC_snap` (**probed**:
  `auth.authOwn_latestSnap`).
- Users: unchanged (they destructure with `-` for the new clause).

## 3. The checks

**`apply.checkLeasePuts.specL`** (replaces `specNil`, `AuthApplyLatestPut.lean:45`), **probed**:
```lean
∀ st le RD on Lf hs γl L I ai info dq id,
{{ isPkgInit apply ∗ isAuthStoreL st RD on Lf ∗ txn.isTxnLessor le γl ∗ lease.lessorUser γl L I ∗
    ai ↦{dq} info ∗ RD ∗ Lf hs ∗ ⌜leaseShapedL on hs I id⌝ }}
  checkLeasePuts st ai le id
{{ err, RET err; lease.lessorUser γl L I ∗ ai ↦{dq} info ∗ RD ∗ Lf hs ∗ authApplyErrIs err ∗
    ⌜on.isOn = false → err = nil⌝ ∗ (∀ _ : err = nil, leaseKeysClass on info I id) ∗
    ⌜(err = nil → leasePassedL on hs (authInfoM info) I id) ∧ (err ≠ nil → leaseRefusedL on hs (authInfoM info) I id)⌝ }}
```
Proved from `txn.isTxnLessor`'s `Lookup` and **`apply.checkLeasePutsKeys.specL`** (new, **probed**: the same
over `lease.leaseOwnOpen γl L I id l`, from `isAuthStoreL`'s admin and `IsPutPermitted` triples and
`lease.Lease.Keys.spec`; `keys_open` gives the two-way key fact, CP0 fix 5).

**`apply.checkPutAuth.specL`** (`AuthApplyLatestPut.lean:56`), **probed**: `lookupNil le` becomes
`txn.isTxnLessor le γl ∗ lease.lessorUser γl L I` (given back); the shape premise gains
`leaseShapedL on hs I o.leaseID`; the class gains `leaseKeysClass on info I o.leaseID`; the verdict:
`err = nil → passedL … (putPerms o) ∧ leasePassedL … I o.leaseID`,
`err ≠ nil → refusedL … (putPerms o) ∨ leaseRefusedL … I o.leaseID`. Proved from `checkLeasePuts.specL`.

**`apply.checkTxnPermission.specL`, `CheckTxnAuth.specL`, `txnPermTL`, `checkTxnReqs_latest`**
(`AuthApplyLatestTxn.lean:209-311`): the same change over the transaction's puts:
- premise `lookupNil le` → `txn.isTxnLessor le γl ∗ lease.lessorUser γl L I`, given back;
  `⌜shapedMay on hs (txnMay t) ∧ ∀ o ∈ apply.txnPutsW t, leaseShapedL on hs I o.leaseID⌝`;
- class: `txnClass on info t.toModel ∗ txnLeaseClass on info I t.toModel` (`AuthClass.lean:302`);
- verdict: `err = nil → (∃ L, txnChecked t L ∧ passedL … L) ∧ ∀ o ∈ apply.txnPutsW t, leasePassedL … I o.leaseID`;
  `err ≠ nil → refusedMay … (txnMay t) ∨ ∃ o ∈ apply.txnPutsW t, leaseRefusedL … I o.leaseID`.
- Proved from: `checkPutAuth.specL` at each put (the Löb induction's step as today), `txnLeaseClass`'s
  structure (`opsLeaseClass` mirrors `opsPutsW`: a lemma `txnLeaseClass_of_puts`).

## 4. The methods

**`kvPostFL`** (`AuthApplyLatest.lean:107`, exported through `Results.lean`): gains
`chainLeaseClass E.authMode info (mvcc.leaseItemsOf (mvcc.stateAfter log)) c rq oc`, as `kvPostF`
(Q5). Its two lemmas: `auth_reject_kvPostFL` adds `chainLeaseClass_auth_rejected`; `auth_pass_kvPostFL`
takes `kvPostF`'s lease class (as today it drops it) and a `reqLeaseClass … rq` premise, giving
`chainLeaseClass_auth_pass` (as `AuthLemmas.lean:75-94`). `kvPostFL_kvPostF` (if any user wants the
class track's post) is then an identity up to `X`.

**`apply.authApplierV3.Put.specL`** (`AuthApplyLatestPut.lean:76`): drops `apply.lessorNil p`; the
verdict `authOutL … (putPerms o)` becomes `authOutLL … (putPerms o) I [o.leaseID]` with
`I = leaseItemsOf (stateAfter log)`, in `putPreW`'s `X` and `kvPostFL`'s; the shape premise gains
`leaseShapedL E.authMode hs I o.leaseID`. Proved from `checkPutAuth.specL`, `mPreRest_lend` with `authIs`'s
lessor field (`put_lend`, **probed**), `reqLeaseClass_put`, the new `auth_pass_kvPostFL`.

**`apply.authApplierV3.Txn.specL`** (`AuthApplyLatestTxn.lean:246`): drops `lessorNil p`; its `X` becomes
```lean
fun oc => (oc = .rejected .auth ∧ (refusedMay … (txnMay tw) ∨ ∃ o ∈ apply.txnPutsW tw, leaseRefusedL … I o.leaseID)) ∨
  (chainStep backendStep c rq log oc ∧ (∃ L, txnChecked tw L ∧ passedL … L) ∧
    ∀ o ∈ apply.txnPutsW tw, leasePassedL … I o.leaseID)
```
and the shape premise gains the puts' `leaseShapedL`. Proved from `CheckTxnAuth.specL`, `mPreRest_lend`,
`reqLeaseClass_txn`.

**New: `apply.authApplierV3.LeaseRevoke.specL`** (`checkLeasePuts` then the inner `LeaseRevoke`,
`apply/auth.go:191-196`):
```lean
∀ E c inner p r rq id log T rs Pre Q Post info L hs,
{{ isPkgInit apply ∗ authIs E p inner ∗ authIsL E p L ∗ applierSpec E c inner ∗ applyTok E ∗
    revokePreW E (.auth E.authOn c) (mkOk authApplierV3 p) info r rq id log T rs Pre Q Post
      (authOutLL E.authMode hs (authInfoM info) c rq log [] I [id]) ∗
    L hs ∗ ⌜leaseShapedL E.authMode hs I id⌝ }}
  p.LeaseRevoke(r)
{{ resp err, RET (resp, err); applyTok E ∗ L hs ∗
    kvPostFL E (.auth E.authOn c) (mkOk authApplierV3 p) info rq log []
      (fun o => revokeOutcomeIs resp err o ∗ revokeResAfter E rq T rs resp err o) Pre Post
      (authOutLL E.authMode hs (authInfoM info) c rq log [] I [id]) }}
```
where `I` abbreviates `mvcc.leaseItemsOf (mvcc.stateAfter log)` (written out in the Lean statement, as
`Put.specL`'s). The floor is `[]` (review r2 F4): a revocation's outcome is `.applied`, its floor fact would come only from the
backend's `writer_floor`, which the auth layer does not hold, and nothing consumes it (`kvFloorOk` covers put,
delete and txn only); `floorOkO [] log oc` holds outright. The resource family is `L`, as Put's. `revokePreW` is `revokePre` with `certPreW` for `certPre` (the
certificates of the outcomes the verdict admits, as `putPreW`; at auth on the apply thread cannot certify
a refused revocation's log). Its admin shortcut has no revision condition and a keyless lease passes for
any principal, the empty header included (Scope E5), which `leasePassedL` says. Proved from
`checkLeasePuts.specL` and the inner chain's `LeaseRevoke` triple (`applierSpec`'s, as the class track's
`authApplierV3__LeaseRevoke.lean`).

## 5. The packaging

- **`applierKVL`** (`DispatchKVL.lean:83`): its Put and Txn triples take the new verdicts (`authOutLL`,
  the puts' shapes); a fifth triple, `LeaseRevoke`, as above. **`applierKVL_auth`** drops `lessorNil p`
  (proved from the four `specL`s and the new `LeaseRevoke.specL`).
- **`kvOutL`** (`DispatchKVL.lean:47`, the latest dispatch's verdict): with `I = leaseItemsOf (stateAfter log)`,
  `.put => ∃ o, rq.put = some o ∧ authOutLL M hs ai ci rq log (putPerms o) I [o.leaseID] oc`; `.txn` gains the
  puts' lease parts as `Txn.specL`'s `X`; new `.leaseRevoke => ∃ id, rq.leaseRevoke = some id ∧
  authOutLL M hs ai ci rq log [] I [id] oc`; range and delete unchanged.
- **`kvShapedL`** (`DispatchKVL.lean:66`, exported; review r1 M2): gains `log` and the lease shapes, with
  `I = leaseItemsOf (stateAfter log)`: `.put => ∀ o, rq.put = some o → shapedL M hs (putPerms o) ∧
  leaseShapedL M hs I o.leaseID`; `.txn => ∀ t, rq.txnW = some t → shapedMay M hs (txnMay t) ∧ ∀ o ∈ txnPutsW t,
  leaseShapedL M hs I o.leaseID`; new `.leaseRevoke => ∀ id, rq.leaseRevoke = some id → leaseShapedL M hs I id`.
- **The four latest layer triples widen to the revocation** (review r2 F1, F2: one triple per layer, not a
  parallel family): `uberApplier.dispatch.kvSpecL` (`DispatchKVL.lean:159`), `uberApplier.Apply.kvSpecL`
  (`ApplyKVL.lean:54`), the contract `apply.uberKVC` (`ApplyFnKVL.lean:69`) and `apply.Apply.kvSpecL`
  (`ApplyFnKVL.lean:107`):
  - their kind premise `isKVKind (dispatchKind rq) = true` becomes `authKVKind (dispatchKind rq) = true`
    (`authKVKind k := isKVKind k || k == .leaseRevoke`, `apply/Chain.lean` beside `authChecks`);
  - `rqOk .none x.log rq` becomes `rqOk E.lm x.log rq` (the revocation's arm needs `E.lm = .revocable`, which
    `revokeRes` holds; at a KV kind `rqOk` does not depend on the mode, so the existing callers pass the same
    fact);
  - they thread the revocation's resources as `dispatch.spec` does (`uberApplier__dispatch.lean:58-81`):
    `revokeOwn E rq ∗ ltHalf E T` in; out `revokeOwn E rq` back, `revokeAnsR`, `ltHalf E (revokeIds …)` and
    `E.RO (revokeRest …)` (at `dispatch`), their `A` variants `revokeIdsA`, `revokeRestA`, `revokeAnsRA` at the two
    `Apply` layers, exactly as `dispatch.spec`/`Apply.spec` state them; off a revocation these are identities
    (`revokeOwn_nonRevoke`, `revokeIds_nonRevoke`, `revokeRest_nonRevoke`, `revokeIdsA_nonRevoke`,
    `revokeRestA_nonRevoke`), but `ltHalf E T` is a real half when `E.lg`: the KV caller passes its `HLt` through
    and rewrites (review r3 S1);
  - `kvShapedL … rq` becomes `kvShapedL … x.log rq`; the verdict `kvOutL` is the new one.
  The lease class stops at the auth applier's methods (`kvPostFL`, Q5): `applyAuthRes` (`InvUber.lean:195`)
  carries no class to the server and nothing past the methods consumes one, so the layers' posts do not state
  `chainLeaseClass` (the Scope's "carried through dispatch" is dropped; recorded for the Freeze).
- **`uberKVL_of_base`** (`UberKVLBase.lean:40`): drops `apply.lookupNil le`.
- **`Results.lean`**: `apply_applier_kv_latest` drops `lessorNil p`; `apply_put_latest`, `apply_txn_latest`
  restated; new `apply_lease_revoke_latest`; `server_uber_kvl`/`server_uber_kvl_on` keep `srvLessorNil` until
  S3 (their proof then just forgets it).
- Deleted: `apply.checkLeasePuts.specNil`, `wp_nil`, `apply.lessorNil` (and `lookupNil` once S3 removes
  `srvLessorNil`; until then `lookupNil` stays for `ServerOnDefs`/`UberOn`).

## 6. Glue (proved in Draft), and the server-side repairs S2 owns

Glue: `applierKVL_auth`, `uberKVL_of_base`, the `Results` exports (they pass the methods' triples on); the four
layer triples' proofs where they only pass the revocation's resources through (`Apply.kvSpecL` over
`dispatch.kvSpecL`).

Server-side consumers of the changed `kvOutL`/`kvShapedL` (review r2 F3), repaired in S2 so the branch builds:
- `authOutL_of_kvOutL` (`KVOutcomeOn.lean:256`): a rejection can now come from a lease refusal, so it takes
  `plainCover rq` (no lease on the request, `KVModelDefs.lean:75`) and `leaseItemsOf_ne_zero`
  (`LeaseItems.lean:90`: lease `0` attaches no key, so its lease part passes);
- `authTie_of_kvOutL` (`ApplyNormalOn.lean:240`) gains the same premise; `kv_outcome_on_latest`
  (`Results.lean:1802`, exported) with it;
- `kvShapedL_of_log` (`ApplyNormalOn.lean:78`) and its caller (`EtcdServer__applyEntryNormal.lean:1746`): the
  `log` argument; the lease shapes from `plainCover` (lease `0`: no key);
- `kv_entry_pre_on` (`ApplyEntryOn.lean:129`): its proof covers the new refusals (vacuous under `plainCover`); its
  statement does not change, nor does `kv_outcome_on_latest`'s;
- `srv_uberKVL`, `srv_uberKVL_on` (`UberOn.lean:125, 152`): `applierKVL`'s fifth (revocation) method spec;
- `uberKitM` (`UberKit.lean:38`, the bundle `NewServer` takes) gains a `LeaseRevoke.specL` conjunct for
  `srvUberOn_of_kit`, so `server_new_auth_on`'s tuple (`Results.lean:2131`) gains `apply_lease_revoke_latest`;
- the one real caller of the widened `Apply` triple, `EtcdServer__applyEntryNormal.lean` (≈1720, its `wp_apply
  hK`): passes `HLt`, `rqOk_kv` (new: at a KV kind `rqOk .none log rq → rqOk lm log rq`) and rewrites the
  identities;
- a lemma `txnPutsW_plain : txnPlain t.toModel → o ∈ txnPutsW t → o.leaseID = 0` (mutual induction), for the
  transaction's lease part under `plainCover`.
All of these take `plainCover` from the auth-on log's shape (`plainEntryOn`), which S3 replaces by the model's
lease table (`kvGrantedL`).

Not glue (Prove): the checks and methods (the probe's three are done), the transaction checks' Löb step.

## 7. What S3 takes from S2

The auth-on server's KV contract (`srvUberOn`, `srv_uberKVL_on`) reads the verdict of `kvOutL` against the
model's `kvGrantedL` (S3's `kvEntryOnL`, probed in `Scratch/AuthLeaseProbeModel.lean`): `authOutLL`'s two
sides are the model's `¬ kvGrantedL` / `kvGrantedL` at the latest state, `leaseOk`'s three disjuncts being
`leasePassedL`'s (auth disabled is in `adminOk`).

**Where `leaseShapedL` comes from (review r1 M3).** `reqShape k []` is `k ≠ []`. The model's `kvDet` covers only a
request's own permissions, and `leaseOk` has no shape condition, so S3 states a KV-state invariant: every key the
state attaches to a lease is non-empty (`∀ k id, leaseItemsOf (stateAfter log) !! ⟨k⟩ = some id → k ≠ []`), in
`kvInvOn` beside the lease table, kept by every put since a leased put's key is a point key of the cache's shape
(`entryShapeOn`/`kvShapeAll`; gRPC refuses an empty key, `v3rpc/key.go:182-185`). It holds of the
start's log (`γk.log0`: the backend's state at the start, empty at a first start; at a restart the recovered
state, whose keys came from puts of the same shape) and is kept by each entry; the simpler form "every key of the
state is non-empty" is as easy and may be what S3 states. The server's `srv_uberKVL_on` derives
`kvShapedL … log rq` from it and the request's `kvDet`.

## 8. Exported statements this changes (for the Freeze)

`apply.kvPostFL` (body), `apply.authApplierV3.{Put,Txn}.specL`, `apply.checkPutAuth.specL`,
`apply.checkTxnPermission.specL`, `apply.CheckTxnAuth.specL`, `apply.applierKVL` (body), `apply.kvOutL` (body), `apply.kvShapedL` (body, new `log` argument), `apply.authApplierV3.DeleteRange.specL` (through `kvPostFL`'s body; its text unchanged, its proof adds the trivial lease class; `Range.specL` posts `rangePostL`, unchanged),
`apply.isAuthStoreL` (body), `Results`' `apply_put_latest`, `apply_txn_latest`, `apply_applier_kv_latest`
("exported": `Results.lean`'s statements; the server has no `etc/api` list, so no `interface/` file shows them); new: `checkLeasePuts.specL`, `checkLeasePutsKeys.specL`,
`authApplierV3.LeaseRevoke.specL`, `apply_lease_revoke_latest`; widened: `uberApplier.{dispatch,Apply}.kvSpecL`, `apply.uberKVC`, `apply.Apply.kvSpecL`; server-side (§6): `authOutL_of_kvOutL`, `authTie_of_kvOutL`, `kvShapedL_of_log` (premises), `srv_uberKVL{,_on}`, `uberKitM` and `server_new_auth_on`'s tuple. No trusted text, no axiom.

## 9. The spec plan and the two tracks

`SpecPlan/` gives one spec per function (`checksOut` over opaque predicates). The real tree already has two
triples for the auth layer's checks (the class track, `kvPost`, for the off server and the auth-off chain
results; the latest track, `kvPostFL`, for the auth-on apply thread, E2s 2026-10-26); S2 continues that split for
`checkLeasePuts`, `checkLeasePutsKeys`, `checkPutAuth` and `LeaseRevoke` rather than merging them, since
merging changes the class track's frozen Part A statements (lease-keys plan). Convergence toward the plan's single
spec is a later cleanup, recorded here.

## 10. Review

Round 1 (fresh `spec-reviewer`, 2026-11-14, `/shared/tmp/auth-lease/s2-review-r1.md`): the probed checks true
and exact; majors M1 (the dispatch triple), M2 (`kvShapedL`), M3 (the source of `leaseShapedL`) and the minors
(unbound `I`, the revocation's floor, `DeleteRange.specL` through `kvPostFL`, `authOutL` as an abbrev, `putsW`'s
namespace, the two tracks) are addressed above. `isAuthStoreL`'s new clause kept as a separate clause (the
reviewer's alternative, in `IsAdminPermitted`'s post, would change that triple's 13 users the same way).

Round 2 (fresh `spec-reviewer`, `/shared/tmp/auth-lease/s2-review-r2.md`): F1 (`rqOk E.lm`), F2 (widen the four
layer triples instead of a parallel revocation triple; the lease class not carried past the methods), F3 (the
server-side repairs, §6), F4 (the revocation's floor `[]`), §7's initial state, and the nits (`authOutL` as an
abbrev gets an `authOutL_iff` law; `isAuthStoreL`'s ~13 `icases` patterns gain a `-`; the probe model's `putsW`
becomes `apply.txnPutsW` when it moves) are addressed above.

Round 3 (fresh `spec-reviewer`, `/shared/tmp/auth-lease/s2-review-r3.md`): **no first-tier finding**; the round-2
fixes verified provable against the code. Its second-tier items (the widened posts' exact resources and `A`
variants, the `HLt` call site and `rqOk_kv`, `txnPutsW_plain`, `uberKitM`/`server_new_auth_on`, `authOutL` kept a
`def` with `authOutL_iff`, `Range.specL` and `kv_entry_pre_on` unchanged) are applied above. Unprobed, no obstacle
seen by any round: `LeaseRevoke.specL`, the transaction checks' Löb step, the methods' lease-class lemmas.
