# Track AP of the `origin/lean` → `mvcc-api` merge: `etcdserver/apply` (2026-11-06)

Scope: the 38 conflicted files of `{Proof,Spec}/go_etcd_io/etcd/server/v3/etcdserver/apply/` and the
non-conflicted ones there that needed adapting. All resolved and `git add`ed; no `lake build` run.
Rule applied: mvcc-facing pieces ours (the API restatement: `threadTok`, `kvLogLb`, `E.Nx`,
`mPre`/`mPreW`/`mPostW`/`kvOwnPre`/`bkRTOf`, `wSt`, `mvccLeases E.γ`, the deleter), everything else
`lean`'s (lease-grant 2.x, lease-expiry X6/X7/E3/S2–S4, revoke-open, the `lm` mode, F2's `1 ≤ rev`).

## Vocabulary decisions (`apply/Chain.lean`, `Contracts.lean`, `WriteLemmas.lean`)

- **New `apply.rdHeld E := ∃ rd, lease.rdOwn (mvccLeases E.γ) rd ∗ mvccDeleter rd E.γ`** (Chain.lean,
  after `kvBk`): `lean`'s `lease.rdAt E.γ.leases E.s`. Used by `revokeRes`, `revokeOwn`,
  `revokeResAfter`. `Contracts.revokeClause` keeps ours' inline `∃ rd, …` (Contracts is below Chain).
  If track LA restates `lease.rdAt` over the API instead, `rdHeld` becomes that.
- `leasesLive (E : AEnv GF)` (lean's signature, with `ltHalf E L`) over `mvccLeases E.γ`; every
  `leasesLive E.γ …` in apply (Chain, WriteLemmas) → `leasesLive E …`.
- `everOwn`, `grantFresh`, `grantAnswer`, `grantPermRq`, `grantPre`, `grantPost`: `E.γ.leases` →
  `mvccLeases E.γ`.
- **`grantPre`**: lean's, with `mPreW` in place of `mvcc.storeWT E.γ ∗ mPre` (the grant's component
  writes the backend). **`grantPost`**: `mPostW` in place of `mPost` (reader token back). The chain's
  grant triple and the four `LeaseGrant` specs take and give `threadTok`.
- **`grantHdr`**: `E.Nx log` in place of `mvcc.idxCert E.γ.idx log ∗ mvcc.certOk E.γ log` (the server's
  `srvRevLbA` is derivable from `kvNx`; `kvLogLb` is not available at `newHeader`).
- `revokeRes E T rs` / `revokeResAfter E rq T rs resp err o` / `revokeOwn`: lean's shapes over
  `rdHeld E` and `lease.lessorRevocable (mvccLeases E.γ)`.
- **`revokePre`**: lean's `T`, ours' extra conjunct `(mvcc.stateAfter log).length ≤ 2 ^ 62`, no
  `storeWT`. The revocation triple and specs: `threadTok` in and out.
- `rqOk lm log rq`: lean's arms, ours' `txn.TxnPreA`. `cmpAdmitRev log rev := 1 ≤ rev ∧ rev < |log|`
  (ours; lean's `kbCmpM` gone, its F2 `1 ≤ rev` is already ours').
- `reqFacts`/`respMethods`: lean's (no `LeaseGrant`).
- `Contracts.revokeClause`: ours + `lease.lessorRevocable (mvccLeases γ)` in the pre.
  `isApplyLessor`: ours' signature (`γ Pk f BT RO RW`); its `Grant` clause is lean's exact clause
  (`RO rs`, `leaseEver`, `grantIdsOk`, `restGrantT`, `leaseReqIs`, `lsF ttl`) over ours' tokens
  (`csContractA (Pk B)`, `bkWT B ∗ bkRT B ∗ BT B` in, `bkRT B ∗ BT B` out); no `RW` (lean's).
  `Checkpoint` ours (`RW` in and out). MERGE-TODO(lessorBackend) on the Grant clause.
- **New `WriteLemmas.kvOwnPre_mPreW`** (`kvOwnPre true ∗ chainRes ⊢ mPreW`), for dispatch's grant arm.
- `WriteLemmas.mPreRest_lend` keeps `ltHalf` inside its way back.

## Spec changes (client statements, old → new)

- `applierV3{backend,Capped,Corrupt}.LeaseGrant.spec`, `quotaApplierV3.LeaseGrant.spec`: ours had
  `reqFacts`-style `(∃ g, leaseGrantIs ∗ leaseGranted (mvccLeases E.γ)) ∗ E.RW ∗ threadTok ∗ mPreW …`
  → `mPostW ∗ applyErrIs`; lean's `grantPre … → ∃ o, grantPost …`; now `threadTok ∗ grantPre …` →
  `threadTok ∗ ∃ o, grantPost …` (grantPre/Post as above).
- `*.LeaseRevoke.spec` (backend, Corrupt, auth): lean's (`T`, the post's `fun o => revokeOutcomeIs ∗
  revokeResAfter`) with ours' `threadTok` in and out.
- `applierV3backend.newHeader.spec`: ours' pre (`threadTok ∗ wSt E.γs log c`), post ours' plus lean's
  2.11a (`hdrFields h ∗ Revision ↦ log.length - 1 ∗ E.Nx log ∗ ⌜2 ≤ |log| ∧ |log|+3 ≤ 2^63⌝`;
  `E.Nx log` for lean's `certOk`).
- `uberApplier.{Apply,dispatch}.spec`, `Apply.specRec` (ApplyRec), `ApplyKVL`/`ApplyFnKVL`/
  `DispatchKVL`/`ApplyFnAdminL` variants: ours' `kvOwnPre`/`kvLogLb`/`threadTok`/`bkRTOf` with lean's
  `rqOk E.lm` (`.none` in the KV-only variants), `grantPermRq`, `ltHalf T`, `everOwn U`,
  `grantFresh`, `revokeOwn`, and lean's post (`E.RO` inside the existential, grant/revoke answers);
  `cmpAdmit log rq` (no `E.γ.kb`). `ApplyFnAdminL`: lean's `W` moved into the lend
  (`Own γa h ∗ W ⊢ L h ∗ (L h -∗ Own γa h ∗ W)`).
- `AuthDerive.isAuthStore_isAuthEnabled` (new in lean): over ours' `isAuthStore st Pk f BT RD M RW`.
  `AuthStepsX.isAuthStepsX_frameW` (new in lean): `f : GoFunc`.

## Proof bodies (none checked; the next phase repairs)

Per file, the body taken: Compaction, Put, Txn, DeleteRange, LeaseCheckpoint, ApplyKVL, ApplyFnKVL,
DispatchKVL, ApplyFnAdminL: ours (+ `HltL` threaded where `leasesLive` is opened; `newHeader`'s new
post absorbed by `-`). LeaseGrant (backend, Capped, Corrupt, quota), newHeader, LeaseRevoke (backend,
Corrupt, auth), ApplyAdminL, ApplyRec, uberApplier.{Apply,dispatch}, newApplierV3{Backend,Capped,
Corrupt}, newAuthApplierV3, newQuotaApplierV3: combined (lean's structure for the grant/revoke/live-set
steps, ours' API steps: `mPreW_split`, `mPreW_reject`, `mPreW_split_chain`/`mPreW_of_rest`,
`kvOwnPre_mPre`, `kvOwn_of_split`, `mPostW_backend`, `threadTok`).

## MERGE-TODOs

- `MERGE-TODO(proof)`: applierV3backend__LeaseGrant, quotaApplierV3__LeaseGrant,
  applierV3backend__LeaseRevoke, authApplierV3__LeaseRevoke, applierV3backend__newHeader (the
  `Rev` value `v = σ.rev` step), newAuthApplierV3 (promoted grant), uberApplier__dispatch (grant and
  revocation arms): combined bodies not yet checked.
- `MERGE-TODO(revokeSize)` (uberApplier__dispatch, revocation arm, an undefined `hsz`): ours'
  `revokePre` needs `(mvcc.stateAfter log).length ≤ 2 ^ 62`; on `lean` `dispatch` now admits
  revocations (`rqOk`'s `.revocable` arm), but neither `rqOk` nor `dispatch.spec`/`Apply.spec` gives
  the bound. **Spec change needed** (decision): add it to `rqOk`'s revocable arm (`revokeKindOk rq ∧
  putOk log ∧ (stateAfter log).length ≤ 2^62`; the server derives it from `srvApplyKV_small`), or a
  premise of `dispatch.spec`.
- `MERGE-TODO(lessorBackend)`: `Contracts.isApplyLessor`'s Grant clause; `LessorDerive.lean`'s
  `revokeClause_of_lessorInv` and `isApplyLessor_of_lessorInv` (lean's text, statements entirely over
  mvcc internals: `mvcc.StoreNames`, `s`, `lease.rdAt`, `kvWriter`, `storeWT`/`storeRT`, `storeRb`,
  `γ.kb`, `lessorBeOn`): restate to give ours' `revokeClause li γ Pk f BT RO` / `isApplyLessor … γ Pk f
  BT RO RW` once track LA settles `lessorBackend` and the lessor's Grant/Revoke/Checkpoint specs.
- `MERGE-TODO(results)` (`apply/Results.lean`, lean's text, untouched by ours): `chain_put`,
  `chain_deleteRange`, `chain_txn` use the deleted `kvOwn_cert`; `chain_range`, `chain_revoke` and
  those three lack `threadTok` (the chain's triples take it): **statement change needed** (`threadTok`
  in/out, the floor `kvLogLb E.γs F`), a top-level file, not changed here. `#print axioms
  mvcc.store.wp_Rev` is stale (`newHeader` uses `KV.Rev.contract`).

## Will break outside apply (server track; uses of the changed vocabulary)

`apply.leasesLive` (now `E`, with `ltHalf`), `rdHeld`, `revokePre`/`revokeRes` (T, size conjunct),
`grantPre`/`grantPost` (`mPreW`/`mPostW`), `grantHdr` (`E.Nx`), `cmpAdmitRev` (no `kb`),
`isApplyLessor`/`revokeClause`, `newHeader.spec`: ApplyCmpArm, WorkloadDefs, etcdserver/Results,
EtcdServer__applyEntryNormal, NewServer, KVApply, EtcdServer__LeaseRevoke (`grantHdr`'s `Hcert Hcok`
→ `E.Nx`, to `srvRevLbA`), EtcdServer__LeaseGrant (same), SnapApplyOpts(Lemmas), SnapApplyNames,
InvRead, InvApplier, EtcdServer__Txn, SnapRO, SnapApplyWalk, SnapApplyKV, RestorePre(M), ReadOn,
KVStoreApi, InvStart, InvRest, InvMonitors, InvBuild, EtcdServer__Compact, ApplyNormalOn,
`lease/lessor__Renew` spec (`git grep` of `apply.(revokeRes|revokePre|leasesLive|rqOk|cmpAdmitRev|
grantPre|grantHdr|isApplyLessor|revokeClause|newHeader.spec)`).

Pre-existing red in apply, not from this merge: `M2ApplyDraft.lean`, `CompactArm.lean` (old drafts
over mvcc internals, identical on both sides).

## API weakness

None found: the apply chain needs of mvcc only `isMvcc`, `mvccBackend`/`hookIs`, `mvccDeleter`,
`mvccLeases`, the update shapes and `KV.Rev.contract`. The one gap is the client's (the revocation's
state-size premise above), not the API's.
