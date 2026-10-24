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

**L3. The apply thread with leases.** `leasesKnown` becomes an equality: the lessor's live set
(`leaseOwn γ.leases L`) is the model's table's ids. `plainCover` admits `LeaseGrant`,
`LeaseRevoke` and leased puts and transactions; `SrvWorkload` gains `writes` for the lease ops;
the apply chain's dispatch of the two lease kinds (the backend applier's proofs exist) steps the
model; the apply thread lends the lease bucket's right `RW` to a grant or revoke. The txn path's
`checkLease`/`checkLeasePuts` rejections are the model's identity steps.

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
