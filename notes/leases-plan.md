# Leases in the KV model (unit T3)

**Status:** active (2026-10-24, branch `leases-t3`, worktree `/shared/etcd-grove-t3`); L0 done
(this plan); L1 done (the model's table and steps; the server's state keeps an empty table until
L3).

The design sketch is `notes/decisions.md`, "Unit T3: leases (the plan; not implemented)". This
file stages it against the proofs as they stand on `lean` at `f9ba6b6d6e`.

## Goal

`kvLeasedPutTodo` (`client/v3/ServerKVPut.lean`) and `kvLeasedCommitTodo`
(`client/v3/ServerKVTxn.lean`) become theorems and leave `kvWritesOk`. Today they are premises
of every result that takes `kvWritesOk`: the recipes' (`experimental/recipes/{Results,Vertical,
KVOfServer}.lean`). A server whose workload admits lease requests (`LeaseGrant`, `LeaseRevoke`,
puts and transactions with a lease) is then verified in the KV model, with the leases-off
`putgetWorkload` one instance of it.

## Where leases are excluded today

| layer | what keeps leases out | file |
|---|---|---|
| KV model | `KVState` is `⟨kvs, rev⟩`, a function of the mvcc log (`kvStateOf`); no lease table, no `KVOp` for grant or revoke | `etcdserver/KVModelDefs.lean` |
| admission | `plainCover`: a put's `leaseID = 0`, a transaction `txnPlain`; no `LeaseGrant`/`LeaseRevoke` kind | `KVModelDefs.lean` |
| workload | `SrvWorkload.grant`, `noGrant`; `putgetWorkload.grant _ := False` | `KVModelDefs.lean` |
| lessor at the apply thread | `isApplyLessor`'s `Revoke` clause is `⌜False⌝` (D14h); `leasesKnown L s` only says the state's leases are live (`⊆`) | `apply/Contracts.lean`, `txn/InvTxn.lean` |
| the lessor | `lessor.Revoke` translated, not specified; `Grant`, `Attach`, `Detach`, `Lookup`, `Checkpoint` proved | `lease/` |
| the bucket right | the server's `AEnv.RW` (lease bucket) not lent by the apply thread (no lease request admitted, D22) | `apply/Contracts.lean` |
| expiry | `lessorOk`'s `⌜W.noGrant⌝`: `run`'s receive from `expiredLeaseC` is dead; `EtcdServer.revokeExpiredLeases` names-only; the lessor's `runLoop`/`revokeExpiredLeases`/`findExpiredLeases` not translated; `NewLessor` an axiom | `InvApplier.lean`, `EtcdServer__run.lean` |
| server entry points | `EtcdServer.LeaseGrant`/`LeaseRevoke` translated, unproved; `LeaseRenew`/`LeaseTimeToLive` not translated | `etcdserver` |
| already verified | apply: `applierV3backend.LeaseGrant`/`LeaseRevoke`/`LeaseCheckpoint`, the quota/auth/capped/corrupt wrappers, `checkLeasePuts`; v3rpc: `LeaseServer.LeaseGrant`/`LeaseRevoke`, `quotaLeaseServer.LeaseGrant`; client: `lessor.Grant`/`Revoke`/`KeepAlive` and its loops; `txn.checkLease` | |

## Stages

**L1. The model.** `KVState` gains the lease table, `leases : List (w64 × w64)` (id, granted TTL;
the decision's `σ.leases`), not a function of the mvcc log: `kvInv`'s ghost variable holds
`⟨stateAfter (kvModel γk L), …, leaseTableOf L⟩`, `leaseTableOf` the fold of the committed log's
`LeaseGrant`/`LeaseRevoke` requests. `KVOp` gains `leaseGrant id ttl` and `leaseRevoke id`;
`kvOpStep`: a put or transaction naming a lease not in the table is the identity (rejected,
`ErrLeaseNotFound`), else attaches; a revoke deletes every key attached to `id` at one revision
(the lessor's sorted order) and removes `id`; a grant of an existing id is the identity
(`ErrLeaseExists`). With `leaseID = 0` every existing step is unchanged, so the existing lemmas
about `kvOpStep` keep their statements (the lease-free ones gain no premise).

*Done (2026-10-24).* `KVState.leases : LeaseTable` (default `[]`), `KVOp.leaseGrant`/`leaseRevoke`,
`kvOpStep`'s lease checks (`KVState.leaseMissing`; a transaction's path `txn.PathsLeaseOk`, true of a
plain path, `txn.pathsLeaseOk_plain`), `revokeChanges`. `kvStateOf` keeps an empty table, so
`kvStateOf_backendLog` (and `kvModel_snoc_state`) take `reqLeaseFree rq` (`plainCover_leaseFree`
gives it); L3 replaces it by the table. Three lemmas that said a step keeps the state or makes a
revision (linkvtxn's `kvOpStep_cases`, `revOwn_step`, the k8s store's `kvNext_step` and its
`k8sAu1_kvAu1`/`k8sAuRW_kvAu1`/`k8sAusRW_kvAu1`) are now of a key-value operation (`KVOp.isKV`):
a grant changes the table at the same revision. No result's statement changed otherwise; trust
base unchanged (696 axioms, 4 sorries). `KVState` is in 64
files (353 uses), mostly through `σ.kvs`/`σ.rev`; the literal constructions (`kvStateOf`,
`KVState.commit`, the countable instance) change. Fingerprint check: no closed theorem's text
changes but through `KVState`'s definition.

**L2. `lessor.Revoke`.** Its spec and proof: the lessor's invariant records the store's range
deleter (set by `SetRangeDeleter`), `Revoke` deletes the lease's item set through it in one
transaction, then the lease bucket's entry (`schema.MustUnsafeDeleteLease`: the bucket right
`RW`). The range deleter: mvcc sets it twice (`NewStore`: the store's `Write`;
`newWatchableStore`: the watchable store's, so revocations notify watchers), so the lessor's lock
records the current `rd` against a ghost record whose other half travels with the store's
construction (`NewStore` → `newWatchableStore` → the server's apply thread, in `AEnv`), with the
deleter's spec over the store's writer (`rd()` a `TxnDelete` whose `DeleteRange`/`End` are the
KV writer's delete and commit, the watchable store's notifying). The record is created with the
lessor, so `NewLessor`'s axiom changes statement (its count does not). The lessor's item set stays `{k | σ.kvs[k].lease = id}` by `Attach`/`Detach` (already in
`Attach`'s and `Detach`'s specs). `isApplyLessor`'s `Revoke` clause stops being `⌜False⌝` and is
derived in `isApplyLessor_of_lessorInv`.

*What a closer reading found (2026-10-24), the sub-stages:*
- **L2a, the deleter's field.** `Revoke` reads `le.rd` after releasing `le.mu` (no race in etcd:
  only construction writes it), so the lock cannot hold all of `rd`'s points-to. Split it: the
  lock `lF "rd" ↦{q/2}`, the other half a token `rdOwn lp rd` with the apply thread, and a
  persistent `rdIs rd kv` (calling `rd()` is calling `kv.Write(traceutil.TODO())`).
  `SetRangeDeleter` takes the token and `rdIs`; `NewLessor`'s axiom returns `rdOwn lp nil` (its
  statement changes, not the count); `NewStore`/`newWatchableStore` thread it, ending at the
  watchable store's KV; the server's apply thread holds it. No ghost variable needed.
  *Done (2026-10-24)*, but for `rdIs` (with L2d, where `Revoke` needs it): `lessorMu`'s `rd` at
  `q/2`, `lease.rdOwn γl rd`, `SetRangeDeleter` by the owner, mvcc's `isLessor` clause, `NewStore`
  / `newWatchableStore` / `New` and the backend wrappers (`NewStore_backend`,
  `mvcc_NewStore_backend`, `server_kv_backend`, `server_kv_backend_hooks`,
  `server_kv_watchable`) take `rdOwn γl rd0` and return it; `NewLessor`'s axiom gives
  `rdOwn γl func.nil`; `NewServer` passes it to `mvcc.New` and drops what comes back (until L3).
- **L2b, the item sets.** Nothing yet relates a lease's `itemSet` to the store's state: the store
  calls `Attach`/`Detach` but `leasesKnown` only says a key's lease is live. `Revoke` deletes
  `l.Keys()`, so the model's `revokeChanges` needs `itemSet(id) = {k | σ.kvs[k].lease = id}`, an
  invariant over the store's state and the lessor's per-lease sets, kept by the put and delete
  paths (`Attach` on a put with a lease, `Detach` of the previous lease). This is the largest piece
  of L2 and touches mvcc's write path proofs.
  *Done (2026-10-25).* **The design:** the lease owner's resource carries the item map,
  `lease.leaseOwn γl L I` (`lessorUser γl L I`): the owner holds half of `le.itemMap` (at `I`) and
  half of each live lease's `itemSet` (`leaseItemsOwn`, in its `closerAt`), the locks the other
  halves (`lessorMu` at `q/2`, `leaseItems` at `q/2`), with each lease's set what `I` attaches to
  it (`itemsFor`) and every lease of `I` live. So `GetLease` (with the owner's resource) returns
  `I`'s entry, `Attach`/`Detach` change `I` (`insertAll`/`deleteAll`; preconditions: the items on
  no other lease / on the lease detached), and (for `Revoke`, next) `Keys()` under the lease's read
  lock alone will return the owner's set. **Who keeps `I` the state's:** the store's caller, not
  the store's invariants (`store.Restore`, D22, rebuilds those): mvcc's `put`/`delete`/
  `deleteRange` (and `Put`/`DeleteRange`, metrics') take the owner's resource at the pending
  state's item map (`mvcc.pendItems ilog pend`, `LeaseItems.lean`: `leaseItemsOf s`, each key of
  `s` with a lease to it) and return it at the new pending state's (`pendItems_put`,
  `pendItems_del`; the put's `GetLease` is called only for a key the index finds,
  `pendItems_absent`); the txn package threads it (`txn.put`, `deleteRange`, `executeTxn`,
  `txn`, `Txn`, `Put`, `DeleteRange`, the sole writer's corollaries: at `stateAfter log`), the
  apply chain's `leasesLive` holds it at the state's (`lessorUser γ L (leaseItemsOf s)`), and
  `NewLessor`'s axiom gives `leaseOwn γl [] ∅` (its statement, not its count, changes: the empty
  item map's other half). `txn.Put` and `txn.DeleteRange` meet their log only at the call
  (`Pinned`): they take, as for `leaseOk`, that `I` is every pinned log's state's;
  `writeView.Put`/`DeleteRange` (unused exported results) likewise every certified log's
  (satisfiable by a store without leases). `Grant`'s and `isApplyLessor`'s `Grant` keep `I` (the new
  lease's set empty, `closers_grant`).
- **L2c, `revokec`.** `Revoke` closes `l.revokec` (read-only field today). The close right
  (`ownBroadcastChan`, as the store's `stopCloser`) is exclusive, so it cannot sit in `le.mu`'s
  invariant, which is fractional for the readers (`lessorMu lp γl q`; `NewLessor`'s axiom asserts
  its splitting law). So it goes with the lease owner: a ghost map `γcl` (lease id to `*Lease`),
  its authority at `q` in `le.mu` at the lease map `M`, its exclusive elements with each lease's
  close right in the owner's resource beside `leaseOwn`; `Grant` inserts (the channel from
  `NewLease`, whose spec then returns its ownership), `Revoke` deletes at its second critical
  section and closes after. `γcl` is pinned with the lessor (`lessorPinG`'s tuple), another change
  to `NewLessor`'s statement.
  *Done (2026-10-24).* `revokeCloser c` (the channel's `isChan` and `ownChan … .Idle`: not
  `ownBroadcastChan`, which needs `HeapGS HasLC.hasLC` where the lease package's definitions are
  generic; `Revoke` makes the broadcast channel when it closes it), `NewLease` returns it;
  `lessorPinG γl lp γga γcl`; `lessorAuth γl q lp L M` with `ghostMapAuth γcl q M`;
  `leaseClosers γl L`, now part of `leaseOwn`; `closers_grant` (with `lessorAuth_pin`) in
  `Grant`.
- **L2d, the rest of `Revoke`.** `l.Keys()` (translated, unproved), `sort.StringSlice.Sort`,
  the deletes through `rd()`'s `TxnDelete` (the KV writer's `DeleteRange`/`End`),
  `schema.UnsafeDeleteLease` with the bucket right while the KV write transaction holds the batch
  lock (as `Grant`'s `persistTo`), the `leaseRevoked` counter. Two callees have no model:
  `sort.StringSlice`'s methods are not in Perennial's `sort` (its type only; `sort.Strings` is
  proved over `slices.Sort`), and `schema.UnsafeDeleteLease` is names-only here (as
  `MustUnsafePutLease`, an axiom). Each needs a trust-boundary spec here (+2 axioms) or a
  translation (Perennial's `sort` for the first: a Perennial change, `notes/perennial-changes.md`;
  etcd's goose configuration for the second).
  *Boundary specs added (2026-10-25, the user's choice):* `Spec/sort/StringSlice__Sort.lean`,
  `Spec/.../schema/UnsafeDeleteLease.lean` (unreached until `Revoke` is linked).
  *The batch lock, found 2026-10-25:* `Revoke` deletes the `Lease` bucket's record through
  `le.b.BatchTx()` **without taking the batch lock**: the KV write transaction it opened with
  `rd()` holds it (etcd relies on this: "lease deletion needs to be in the same backend
  transaction with the kv deletion"). Today no contract allows that write: mvcc's
  `batchTxSpecG` allows, under its lock token `Locked`, puts and deletes in `Key` and the
  compaction keys in `Meta` only, and the lessor's `leaseBatchTx` (an assumed contract, from
  `NewLessor`) allows `UnsafePut` into `Lease` only under its own `LockInsideApply` token. So L2d
  needs (i) a `batchTxSpecG` clause: `UnsafeDelete(schema.Lease, k)` under `Locked` keeps the
  token, with the lease bucket's write right (the apply thread's `AEnv.RW`), proved of the real
  backend in `BackendBridge.lean` (as the `Meta` put is); (ii) the store's write transaction
  exposing it while open (`storeTxnWriteIs` holds `Locked`); (iii) `rdIs` giving it with the
  transaction `rd()` returns; and (iv) the lessor's `le.b.BatchTx()` being the store's batch
  transaction (the same backend: `lessorBeOn`, `kb = some d`).
  *(i) and (ii) done (2026-10-25):* `batchTxSpecG`'s last clause (`InvStore.lean`):
  `UnsafeDelete(schema.Lease, k)` under `Locked l`, with `Rb r` (the right to write the tracked
  buckets, a new parameter, default `True`; the store's `storeRb`: the real backend's `rbOwn`
  with `leaseParams`, the table naming `lease`, tracked, no hook keys), gives `Rb (rbDel r
  "lease" k)` and **a token only `Unlock` takes** (`unlockAt`), not `Locked l` again: the
  backend counts pending operations (`pend < 2^58`), so a token kept after a delete would allow
  unboundedly many, which the bridge cannot bound from `l`; `Revoke` makes one delete, then
  `End`. Proved of the real backend (`BackendBridge.lean`: `bt_leaseDel`, the token
  `bkLockedD`, its `Unlock`s `bt_unlockD`, a delete from a hook bucket leaving the readers' view,
  `sData_del_HB`); the bridge takes the backend's `UnsafeDelete` spec (threaded up to
  `NewServer`, hypothesis `h94`). The write transaction carries a flag `ld` (`storeTxnWriteIs`,
  `storeTxnWriteCore`, `isTxnWrite(Core)`, `isWatchTxnWrite`, default `false`; the lock token
  `lockedIs`), `Changes`, `Rev` and the three `End`s take either, and
  `isWatchTxnWrite_leaseDel` (through `isTxnWrite_leaseDel`, `storeTxnWriteIs_leaseDel`) is the
  delete under an open transaction. To get the bucket, schema's `Lease` and `leaseBucketName` are
  now translated (`schema.toml`; two untranslated initializers fewer in `opaqueInitsOk`) and
  `schemaInit` has the `Lease` bucket (`gen-init.py`). Trust base: 696 axioms, 4 sorries, as
  before; the server's collection and the seven built on it now reach `bbolt.Bucket.Delete_kv`
  (bbolt's assumed delete, which the backend's `UnsafeDelete` is proved over, as `UnsafePut`
  over `Put_kv`). The boundary spec of `UnsafeDeleteLease` now names the key (the id's
  big-endian bytes). Left: (iii) and (iv); the holder of `Rb` at `Revoke` (the apply thread's
  `rbOwn`, `srvRestOwn`, with `leaseParams` from the boot facts) is L3's.
  *(iii) and (iv) done (2026-10-25):* (iv) `isKeyBackendG` and `isBatchTxG` take `Bt` (default
  `True`): the batch transactions `BatchTx()` returns satisfy it; the store's `storeBt` (`kbBt`)
  is, over the real backend at `d.be`, `bkBt d.be bt` (`BatchTx()` of that backend returns `bt`,
  proved in `BackendBridge.lean`: the backend's `batchTx` field is read-only), nothing over
  mvcc's assumed backend; the write transaction records it (`storeTxnWriteIs`,
  `storeTxnWriteCore`: `HbtB`) and the three `_leaseDel` lemmas return it with the delete, so
  `Revoke` (holding `lessorBeOn lp d.be`, the user's half of `le.b`) knows its `le.b.BatchTx()`
  is the transaction it deletes under. (iii) `mvcc.rdIs rd s st γ` (`InvWatchStore.lean`): the
  deleter, called by the store's sole writer with what `watchableStore.Write` takes, returns a
  watchable write transaction (`isWatchTxnWrite … L [] 0 0 0`) as a `lease.TxnDelete`;
  `newWatchableStore` proves it of its closure (its proof now takes `watchableStore.Write`'s and
  `traceutil.TODO`'s specs) and returns `∃ rd, rdOwn γl rd ∗ rdIs rd s st γ`, as do `New`,
  `server_kv_watchable(_of)`. Left in L2d: `Lease.Keys` and `Revoke`, whose spec waits for L2b (the
  keys `Revoke` deletes are the item set's, which L2b gives a meaning).
  *`Lease.Keys` and `Revoke` done (2026-10-25, after L2b).* `Keys()` (read lock, a map range,
  `append`): the keys the owner's item map puts on the lease, a fresh slice, no key twice (the
  owner's half of the item set and a reader slot of the lease's lock, kept in its `closerAt`).
  `Revoke` (`lessor__Revoke.lean`), at the watchable store's sole writer (as `watchableStore.Write`
  takes it), over the real backend `d` (`lessorBeOn`, `γw.st.kb = some d`), with the tracked
  buckets' right `storeRb γw.st r` and the store's package initialized: `id` not live,
  `ErrLeaseNotFound` and nothing changed; live, the keys sorted (`sort.StringSlice.Sort`'s premise:
  the state has at most `2^62` keys) deleted at one revision through `rd()`'s transaction
  (`DeleteRange(key, nil)` deletes the one key, `filter_key_sorted`), the lease's record deleted
  under the same batch lock (`schema.UnsafeDeleteLease`, its triple from `isWatchTxnWrite_leaseDel`),
  `End` (the watchers notified), `id` out of the live set, `revokec` closed (`wp_revokec_close`).
  Three changes it needed: **`leaseRevokers γl L`**, the owner's per-lease close rights and the other
  half of the closers' map's element, apart from `leaseOwn` (which the deletes take whole and give
  back behind fresh existentials): `Revoke` keeps it, and its half agrees, after the deletes, that
  the lessor's map still has the lease it looked up; `lessorUser` holds both, `Grant` takes both,
  `NewLessor`'s axiom gives `leaseRevokers γl []`. **`bkBt be bt`** now carries the backend's
  read-only `batchTx` field (`bF "batchTx" be ↦□ t`): two calls of `BatchTx()` agree by it (a
  triple alone did not say so). **`rdIs`** says the deleter is not `nil`. Linked
  (`lease.lessor.wp_Revoke`, `lease.Lease.wp_Keys`), not yet reached from the server: the apply
  thread's `Revoke` clause is still vacuous (L3), which will also lend `storeRb` and give the size
  bound.

**L3. The apply thread with leases.** Staged (2026-10-26, after lean's D45: there is no workload
parameter any more, `plainReq` is `plainCover` at the proposers' kinds, so admitting a lease request
is widening `plainCover`):

- *L3a. The model's table.* The committed log's model folds the lease table beside the mvcc log:
  `backendLog`, `chainLog`, `dispatchLog`, `kvEntry` take the table (a leased put or transaction is
  rejected iff its lease is not in it, a revocation deletes the lease's keys), and `backendTable`,
  ..., `kvTable` step it (a grant adds a new id, a revocation removes a live one; independent of the
  log). `kvRaftOf` folds both from the start table `[]` (the lessor `NewLessor` gives is empty);
  `kvLeases γk L` is the committed log's table and `kvInv`'s state `kvModelSt γk L` (`kvStateOf` with
  that table). `kvStateOf_backendLog` holds of every request (no `reqLeaseFree`). The model's grant
  also refuses id `0` and a TTL above `MaxLeaseTTL` (`lessor.Grant`'s two other errors). `plainCover`
  is unchanged (nothing new admitted yet), so the table stays empty on every server.
- *L3b. Leased puts and transactions.* `plainCover` admits a put with any lease and any transaction
  without `IgnoreLease` (the txn's lease checks are `checkLease`/`checkLeasePuts`, proved). The apply
  layer's state carries the table (`ApplyKV.leases`), `backendStep` is exact on a leased write
  (rejected iff its lease is not live), and `kvOwn` ties the lessor's live set to it
  (`leasesLive`: `L = lt.ids`). The auth mode `on` keeps lease-free requests (`plainEntryOn`).
- *L3c. Grant and revoke through the apply thread.* `plainCover` admits `LeaseGrant`/`LeaseRevoke`;
  `rqOk` gives their premises; `isApplyLessor`'s `Revoke` clause from `lessor.Revoke` (the apply
  environment gets `rdIs` from `NewServer`), `Grant`'s exact (`L' = L ++ [id]`); the apply thread
  lends `storeRb`/`RW`; the rest model (`RestModel.lean`) gains the lease bucket's effects (the
  user's choice, 2026-10-26: extend the rest model, an opaque encoding of a lease's record made
  precise in the lessor's backend contract).
- *L3d.* The server's results restated; notes.

**L4. The server's entry points.** `EtcdServer.LeaseGrant` (the id from `reqIDGen` when `0`,
then `raftRequestOnce`) and `EtcdServer.LeaseRevoke` (`raftRequestOnce`, the response) proved
over the request path's contract, with the client's update `kvOpAu (.leaseGrant …)` /
`(.leaseRevoke id)`; linked under v3rpc's `LeaseServer` (already verified over a contract).

**L5. Expiry.** Leases expire on wall-clock time, which the model does not track, so a client
holding `etcdKV` must accept a revocation at any time: the server's construction takes
`□ ∀ id, kvOpAu (.leaseRevoke id) True` (`kvAnyAu` gives it), which `revokeExpiredLeases`
deposits with its proposals. Needs `EtcdServer.revokeExpiredLeases` translated and proved, and
`lessorOk` without `⌜W.noGrant⌝` (`ExpiredLeasesC` carries granted ids). The lessor's own expiry
loop stays outside (its `runLoop`, `findExpiredLeases`: not translated; `NewLessor` stays an
axiom). **Open question Q1** below.

**L6. The client.** `kvLeasedPutTodo` and `kvLeasedCommitTodo` proved from the server's put and
txn specs with leases (`etcdPutSpec`'s `⌜leaseID = 0⌝` dropped), out of `kvWritesOk`; the recipes'
results re-checked without them. The client's `lessor.Grant`/`Revoke` stated in the clients'
model (their gRPC contracts at the server's `LeaseGrant`/`LeaseRevoke` specs).

Order: L1, L2 (independent of L1), L3, L4, L6, then L5 (L6 needs only grants and revocations a
client asks for if the clients' model has no spontaneous revocations; see Q1).

## Open questions

- **Q1. Expiry in scope?** Decided (the user, 2026-10-24): (b) first, (a) last, as recommended. (a) In scope (L5): spontaneous revocations in the model; every client
  result over a lease-admitting server allows them; `revokeExpiredLeases` translated and proved.
  (b) Out of scope for now: the lease-admitting workload keeps a premise that no lease expires
  (`lessorOk`'s `⌜W.noGrant⌝` replaced by a premise of the lease-enabled instance, recorded as a
  trust-boundary assumption), as crashes are. Recommendation: (a) last, after L6 is done under
  (b), since L1-L4 and L6 do not depend on it.
- **Q2. The TTL in the table.** The decision keeps the granted TTL (`LeaseGrant`'s response
  carries it, raised to the minimum). Only `LeaseGrant`'s reply reads it; `LeaseTimeToLive` (not
  translated) would need the remaining TTL, which is not in the model. Keep it as planned.
