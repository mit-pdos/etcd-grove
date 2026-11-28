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

## N1b-2: one KV model, the fold from `srvAuthSt0`

Decided by the user: no auth modes; one `kvModel`, one `kvRevLb`. The start auth state is fixed at
`srvAuthSt0` (no new `KVNames` field: every start today is a fresh boot).

### Trusted-visible definitions: before / after

`kvRevLbZ`/`kvRevLb` (`InvRequest.lean`) are named by the specs `kv.Put`, `kv.Compact`, `txn.Commit`
(`Spec/go_etcd_io/etcd/client/v3/`), `EtcdServer.Compact` and the client `_dist` contracts. Their text
is unchanged:

```lean
def kvRevLbZ (γk : KVNames) (n : Int) : IProp GF :=
  iprop(∃ L₀ : List EntryModel, monoListLbOwn γk.rlog L₀ ∗ ⌜n < (kvModel γk L₀).length⌝)
```

What changes is `kvModel` (and `kvLeases`), which they are written in:

**Before:**

```lean
def kvModel (γk : KVNames) (L : List EntryModel) : mvcc.Log := kvRaftOf γk.c0 γk.ch0 γk.log0 L
def kvLeases (γk : KVNames) (L : List EntryModel) : LeaseTable := kvTableOf γk.c0 γk.ch0 [] L
```

**After:**

```lean
def kvFold (γk : KVNames) (L : List EntryModel) : OnState :=
  kvRaftOfOn γk.c0 γk.ch0 (srvAuthSt0, γk.log0, []) L
def kvModel (γk : KVNames) (L : List EntryModel) : mvcc.Log := (kvFold γk L).2.1
def kvAuth (γk : KVNames) (L : List EntryModel) : auth.AuthState := (kvFold γk L).1
def kvLeases (γk : KVNames) (L : List EntryModel) : LeaseTable := (kvFold γk L).2.2
```

`srvAuthSt0 := auth.bump auth.bootState` (disabled, revision 1, no user or role) moved, unchanged, from
`KVModelM.lean` to `KVAuthModelDefs.lean`, which `InvRequest.lean` now imports (defs → defs).

**Why the meaning is unchanged where it was used.** `kvFold_off` (from the porting lemma
`kvRaftOfOn_disabled`, `notes/nomode-n1.md` step 4): along a log with no `AuthEnable` above `c0`
(`noAuthEnable γk.c0 L`) the fold's auth state stays disabled, and its log and table are
`kvRaftOf γk.c0 γk.ch0 γk.log0 L` and `kvTableOf γk.c0 γk.ch0 [] L`. Every log the auth-off invariant
`kvInv` holds is `plainLogM`, whose entries are of a proposer's kind (`putgetKind`), a compaction, a
grant or a revocation, never `AuthEnable` (`noAuthEnable_of_plainLogM`). `kvRevLbZ`'s `L₀` is a prefix
of the requested log, which is that log. So under auth off `kvRevLbZ γk n` holds of the same `n` as
before. Under auth on, the fold is `kvModelOn γk srvAuthSt0` (`kvModelOn_srv`, `rfl`): the auth-aware
model the `*On` invariants already use, so `kvRevLb` now names the model those clients follow (the merge
of the twins, N2/N5, can use it).

### What else moved

- `appliedTable` (the lessor's table, the off twin of `appliedTableM true`) and `bkRestAtL` (the off
  leased rest image) keep their value: they are now written `kvTableOf γr.kv.c0 γr.kv.ch0 [] (γr.raft.pre
  ++ A)` (`kvTableOf γk.c0 γk.ch0 [] L`), which is what `kvLeases` was. They merge into the fold with
  their twins in N2. Neither is named by a trusted statement.
- New lemmas: `kvFold_off`, `kvModel_off(M)`, `kvLeases_off(M)`, `kvLeases_ne0_of`, `kvModel_extends`,
  `kvModel_prefix`, `kvModel_length_le`, `kvFold_snoc`, `kvFold_congr` (`InvRequest`);
  `kvEntryOn_snd_nonwrite`, `kvEntryOn_snd_disabled`, `noAuthEnable_of_plainLogM`, `noAuthEnable_sub`,
  `srvAuthSt0_enabled` (`KVAuthModelDefs`, with `kvRaftOfOn_length_le` moved there from `KVApplyOn`);
  `kvFold_boot`, `kvModel_bootE` (`InvBuild`); `kvModelOn_srv`, `kvLeasesOn_srv`, `kvStOn_srv`
  (`KVAuthModel`). The requested-entries lemmas `kvOpOn`, `kvEntryOn_above/_filler/_emptyV2`,
  `kvRaftOfOn_ops` moved from `KVAuthModel` to `KVLemmas` (for `kvModel_eqv`).
- The R declarations: `kvModel_ne_nil`, `kvModel_snoc_nonwrite`, `kvModel_eqv`, `kv_cert_floor`,
  `kvModel_boot` are re-proved over the fold with no new premise; `kvModel_snoc_state` takes
  `noAuthEnable γk.c0 L` (its two callers pass it from `plainLogM`); `kv_applied_step`, `snapRecv_image`,
  `snapRecv_imageR`, `NewServer.wp_proofRG` rewrite with `kvModel_offM` from the `kv_log_plain` they
  already had.
- No top-level statement, axiom or premise changes.

## N1b-3: the cache's "prefix not all `0xff`" premise

The cache's results over etcd's client took `prefixRangeEnd pfx ≠ [W8 0]`: the prefix is not made
only of `0xff` bytes, where `clientv3.GetPrefixRangeEnd` returns `"\x00"` (the from-key marker,
`getPrefix` in `client/v3/op.go`).

**Why it was not needed.** For a non-empty `p` all `0xff`, `¬ (k < p) ↔ p <+: k` in Go's byte order
(no byte exceeds `0xff`, so a key not below `p` agrees with `p` on its first `|p|` bytes, and is not
shorter); `concurrency.inRange_prefix` already proved `inRange p (prefixRangeEnd p) k ↔ p <+: k` for
every non-empty `p`, the from-key case included (`ff_not_lt_iff`). Go treats the end `"\x00"` as
from-key where the cache's watch is served: the watch server's `recvLoop` turns `RangeEnd ==
"\x00"` into `[]byte{}` (`v3rpc.createRangeOk`'s `some []`), and `inRange` (the KV model's ranges)
reads `[0]` as from-key. The only use of the premise was a proof-internal range: `pfxRange pfx`
(`KMWatchDefs.lean`) registered `some (prefixRangeEnd pfx)`, i.e. a literal end `[0]`, which covers
no key; it now registers `[]` for that case, as the watch server does, and `pfxRange_covers` holds
for every non-empty prefix. `WatchCompl.covers_prefix` (unused) dropped it too, through
`rangeExact_of_ne`. The empty prefix is still excluded by the separate premise `pfx ≠ []` (not this
stage's).

Go divergence found on the way (not used by any proof): the cache's own `validateRange` compares the
literal `"\x00"`, so a cache on an all-`0xff` prefix rejects every request
(`nonissues/etcd-cache-all-ff-prefix-rejects-keys.md`); `Cache.validateRange.spec` states that
behaviour, so the results stay true (such requests return `ErrKeyRangeInvalid`).

**Top-level statements** (`Proof/go_etcd_io/etcd/cache/v3/Results.lean`, roots of
`etc/tcb-collections/cache-client.txt`). Before:

```lean
theorem cache_end_to_end_client (cl w api : Loc) (γ : client.KMNames) (dup : Bool)
    (pfx : GoString) (hp : pfx ≠ []) (hff : prefixRangeEnd pfx ≠ [W8 0])
    (hpl : pfx.length ≤ 2 ^ 28) (sl : GoSlice) (gs : List (Config → Config)) : {{ … }} … {{ … }}

theorem cache_end_to_end_new … (hst : kvSame γr.kv γ.kv) (hrb : receiptBound GF ≤ 2 ^ 62)
    (hff : prefixRangeEnd V.pfx ≠ [W8 0]) (hpl : V.pfx.length ≤ 2 ^ 28) (sl : GoSlice) … 
```

After (the triples unchanged):

```lean
theorem cache_end_to_end_client (cl w api : Loc) (γ : client.KMNames) (dup : Bool)
    (pfx : GoString) (hp : pfx ≠ [])
    (hpl : pfx.length ≤ 2 ^ 28) (sl : GoSlice) (gs : List (Config → Config)) : {{ … }} … {{ … }}

theorem cache_end_to_end_new … (hst : kvSame γr.kv γ.kv) (hrb : receiptBound GF ≤ 2 ^ 62)
    (hpl : V.pfx.length ≤ 2 ^ 28) (sl : GoSlice) …
```

Intermediate statements that lost it: `client.pfxRange_covers`, `pfxRange_cov`, `rangeEvents_take`,
`watchRespOk_of_km`, `etcdWatchElem_of_km` (`KMWatchDefs.lean`), `isEtcdWatcher_of_km`
(`KMWatch.lean`), `isEtcdClient_of_km` (`KMClient.lean`), `covers_prefix` (`WatchCompl.lean`),
`isEtcdClient_of_dist` (`dist/client/CacheWorkDefs.lean`), `isEtcdWatcher_of_kmW`
(`dist/client/WatchWorkDefs.lean`); their callers (`examples/etcd/cache/Main`, `dist/client/RunCache`,
`RunWatch`, `partition/MainWatch`) no longer prove it by `decide`. Strengthening; no axiom or premise
added.
