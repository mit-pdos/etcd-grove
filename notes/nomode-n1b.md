# nomode N1b: the request model without shape premises

Design X (`notes/nomode-x.md`) made Go's auth verdict a function of the auth state for every request
(`auth.coversX`, X-a3). N1b puts the KV model on it and drops the shape premises (D2, decided by Upamanyu
2026-11-27: no proof-only premise; the model correct for every request Go accepts). Staged
(`~/coordinator-notes/plans/nomode-packet.md`, "Staging plan v2"): N1b-1 (this file: the verdict, `kvDet`,
`kvShapeAll`/`reqShape` out of every proved statement), N1b-2 (`kvModel`/`kvLeases`/`kvRevLbZ` over the fold),
N1b-3 (the cache's `prefixRangeEnd`), N1b-4 (`noZeroEnds`). Ledger: `notes/specs-only/ledger.md`, 2026-11-28,
"the auth-on KV model's verdict".

## N1b-1: the model's verdict is Go's

**Trusted-visible definitions: before / after** (the vocabulary of `kvInvOn`, `writeGrantG`/`writeAuD` and the
`*On_dist` axioms).

- `kvGranted st rq` (`KVAuthModelDefs.lean`). Before: `∀ x ∈ reqPerms rq, st.enabled = false ∨ (ai.rev ≠ 0 ∧
  st.revision ≤ ai.rev ∧ ∃ u, st.users !! ai.user = some u ∧ (auth.isRoot u ∨ auth.covers st u x.2.2 x.1 x.2.1))`
  (`ai := auth.authInfoM (apply.principalOf rq)`). After: the last disjunct `auth.coversX st u x.2.2 x.1 x.2.1 = true`.
- `leaseOk st a I id` (`KVAuthModelDefs.lean`). Before: `st.enabled = false ∨ auth.adminOk st (some ai) ∨ ∀ k,
  I.lookup ⟨k⟩ = some id → (ai.rev ≠ 0 ∧ st.revision ≤ ai.rev ∧ ∃ u, st.users !! ai.user = some u ∧ (auth.isRoot u ∨
  auth.covers st u .write k []))`. After: the last disjunct `auth.coversX st u .write k [] = true`.
- `kvDet st rq` (`st.enabled = true → ∀ x ∈ reqPerms rq, auth.reqShape x.1 x.2.1`): deleted.
- `entryDetOn c₀ s m` (`KVAuthModel.lean`, in `detLogOn`, in `kvInvOn`). Before: `m.typ = W32 0 → m.data ≠ [] → ∀ rq,
  irrDecode m.data = some rq → (uint.Z c₀ < uint.Z m.index → needAdminPermission rq = true → authDet rq s.1) ∧
  (authKVKind (dispatchKind rq) = true → kvDet s.1 rq)`. After: the first conjunct alone
  (`… → uint.Z c₀ < uint.Z m.index → needAdminPermission rq = true → authDet rq s.1`).
- `plainEntryOn lm m` (`KVAuthModel.lean`, in `plainLogOn`, in `kvInvOn`). Before: its first case `plainReqL lm rq ∧
  noZeroEnds rq ∧ kvShapeAll rq`. After: `plainReqL lm rq ∧ noZeroEnds rq` (`noZeroEnds` is N1b-4's).
- `kvShapeAll`, `auth.reqShape`: definitions kept, used only by the etcd_safe lead's `KV_DeleteOn_dist` and
  `Txn_CommitOn_dist` axioms (and the authwork example's dist calls that discharge them); their removal is N5.

**Untrusted vocabulary changed with them.** `apply.granted1` (`AuthLatest.lean`): `covers` → `coversX … = true`,
so `kvGranted`/`granted1` and `leaseOk`/`leasePassedL` stay definitionally equal (`KVAuthBridge.lean`,
`KVOutcomeOn.lean` unchanged). `auth.permVerdictL_granted` (`Latest.lean`) loses its `reqShape` premise (from
`permVerdictL_iff`). Deleted: `apply.shapedL`, `shapedL_append`, `leaseShapedL`, `leaseShapedL_of_none`, `shapedMay`
(+`_one`, `_mono`), `kvShapedL`, `reqShape_authEndOf`, `shapedL_one_of`, `kvShapedL_of_log(L)`,
`leaseShapedL_of_keysNE`, `kvShapedL_revoke`, `kvDet_of_shapeAll`, `kvShapeAll_withHeader`, `reqShape_of_watch`,
`ServerKVOn.kvReqShape`, and the keys' invariant that only the lease checks' shape used (`keysNonEmpty`, `neSt`,
`reqKeysNE`, `entryKeysNE`, `opKeysNE`, `keysNonEmpty_kvRaftOfOn` and their lemmas). New (`PermTree.lean`):
`coversX_point_iff` (a point: `coversX` is `coversPoint`, every key), `coversX_covers` (a passing `coversX` covers
every key of `[k, e)`, every request), `granted_covers`.

**Statements that lost premises** (strengthenings).
- Apply thread: `apply.authApplierV3.{Range,DeleteRange,Put,Txn,LeaseRevoke}.specL`, `apply.checkLeasePutsKeys.specL`,
  `apply.checkLeasePuts.specL`, `apply.checkPutAuth.specL`, `apply.checkTxnPermission.specL`,
  `apply.CheckTxnAuth.specL`, `apply.checkTxnReqs_latest`, `apply.applierKVL`'s triples,
  `apply.uberApplier.dispatch.kvSpecL`, `apply.uberApplier.Apply.kvSpecL`, `apply.Apply.kvSpecL`, `apply.uberKVC`,
  `Apply_kvSpecL_win` (`EtcdServer__applyEntryNormal.lean`): the shape premise (`shapedL`, `leaseShapedL`,
  `shapedMay`, `kvShapedL`). `auth.permVerdictL_granted`, `apply.verdictL_one`: the shape premise.
- Proposers: `reqPropOkOn` (both write cases), `reqPropOkM_true_write(L)`, `reqPropOkM_true_nowrite`,
  `commitOkOn_plain`, `commitOkOn_L`, `plainOrCmpG_of_entryOn`: `kvShapeAll`. `putPermitOn` (in
  `EtcdServer.Put.spec`): `op.key ≠ []`. `deletePermitOn` (in `EtcdServer.DeleteRange.spec`): `auth.reqShape`.
  `txnPermitOn`, `txnPermitM` (in `EtcdServer.Txn.spec`): `kvShapeAll`.
- Server rows: `v3rpc.kvDepPreOn`, `kvDepPreM`, `kvDepPreML` (in `srvKVAnsM`, `v3rpc` `Results.lean`'s
  `*_end_to_endM(L)`, client `Results.lean`): `kvReqShape`. `putPermitM_of_dep`: `putReqOk`; `txnPermitM_of_dep`: `hsh`.
- Client: `etcdDeleteSpecOnW`, `etcdTxnSpecOnW`, `etcdDeleteSpecMW`, `etcdTxnSpecMW` (the shape conjunct);
  `client_delete_on` (`key ≠ []`), `client_txn_on` (`hsh`), `etcdDeleteSpecV_M` (`hsh`), the authwork example's
  `client_Delete_on`, `work_delete` (`hk`), `work_commit` (`hsh`) and their laws.
- Watch: `v3rpc.watchAuthed` (its `reqShape` conjunct; derived, so the registration states less and
  `watchAuthed_elim`/`watchAuthed_on` give less), `watch_permitted_covers` (`hs`); `ctrlWatcher_authorized`
  unchanged in text.
- Narrowed conclusion: `apply_kv_entry_pre_on` (`etcdserver/Results.lean`, restating `kv_entry_pre_on`) no
  longer concludes `kvShapeAll rq` (the log no longer keeps it).

**Kept for N5.** `Spec/.../dist/KVDeleteOnDist.lean`, `TxnCommitOnDist.lean` (the etcd_safe lead's axioms) still take
`reqShape`/`kvShapeAll`; `WorkCallsDist`'s `work_deleteD`/`work_commitD` and `AuthLeaseTxn`'s `leaseTxnD_shape`
discharge them. `KVDeleteOnDist`'s docstring still says `client_delete_on` takes `key ≠ []` (no longer true).
