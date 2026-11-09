# Requirements on `go.etcd.io/etcd/server/v3/lease` (3c)


## from 2c

What the request path (2c) needs of the lessor (3c) and `lease/leasehttp`:

1. **`Lookup(id)`, `Leases()`**: leases of the member's applied state (each id in W0's `granted`),
   their keys attached at the member's applied revision, `Remaining()`/`TTL()` any; `Demoted()`.
2. **`Renew(id)`**: a TTL, `ErrLeaseNotFound` or `ErrNotPrimary` (any time: W0's keep-alive step
   says nothing of liveness).
3. **`leasehttp.RenewHTTP`, `TimeToLiveHTTP`** (the forwarding to the leader): the leader's answer,
   one W0's step allows at every later state, `ErrLeaseNotFound`, or other errors (retried).

## from 2d

1. **`ExpiredLeasesC()`** (`run`'s expiry arm): a receive gives a `[]*Lease` (`expiredLeases sl ids`,
   provisional in `ApiApply.lean`), and only when the environment lets leases expire
   (`γ.cfg.leaseExpiry = true`; with `false`, the deployment premise that no lease expires during the
   run, the channel never delivers). Used by: `run.spec`, `revokeExpiredLeases.spec`.
2. **`Promote(d)`, `Demote()`** (`applyEntryNormal`'s empty entry at a leader, the ready handler's
   `updateLeadership`): no effect on the model; no panic.
3. **`Recover(newbe, rd)`** (`applySnapshot`): over a snapshot's image, before mvcc's `Restore`.

## from 2e

1. `EtcdServer.leaseBootRes cfg ecfg` (provisional slot of `NewServer`): the lessor's configuration
   against W0's `EnvCfg.leaseExpiry`. **With `leaseExpiry = false`** the server cannot fire a lease
   expiry, so the lessor's slot must carry the deployment premise that no lease expires during the
   run (time-based: 3c to state it, or the user decides to drop the mode: open question Q6 of
   `batch-2e.md`).
2. `lessor.Stop` once (`Cleanup`, through `srvClosers`).

## from 2d (round 1)

4. **The read slot**: the lessor's reads (`Lookup`, `Leases`, `TimeToLive`'s) over 2d's `srvReadAt`
   (your `lessorAt γ n ls` at the member's applied point looks like the right realization).
5. **`expiredCh γ c ch`** (your name): each receive carries `⌜leaseExpiry = true⌝` of the environment
   (2d's `revokeExpiredLeases.spec` takes it; with `false` the channel never delivers: a trusted
   statement about time, say so in your header).

## from 3b

What txn (3b) uses of the lessor (`Spec/go_etcd_io/etcd/server/v3/lease/Api.lean`), as its specs now
cite it: `Lease.isLessor leL γl c`, `Lease.lessorState γl n ls` (the apply thread's writer token, which
`Put`, `DeleteRange` and a writing `Txn` take and return with `Txn.sameLeases ls ls'`), `LessorState.table`
(W0's lease table, for `PutReq.check`), `Lease.lessorIface leL` (the `lease.Lessor` value txn gets).

1. **`Lookup(id)` through the interface value** `Lease.lessorIface leL` (`checkLease`, `put.go:316`): a
   dispatch to `lessor.Lookup.spec`; at the writer's `lessorLb γl n` (from its token) it answers from
   `ls` itself (`lessorState_le`, `lessorAt_agree`). Used by: `checkLease.spec`.
2. **Lease `0` is never live**: `lessorState γl n ls ⊢ ⌜ls.leases 0 = none⌝` (`Grant` refuses `0`,
   the bucket never holds it); txn's `attached` states it, and `put` relies on it (a put with lease `0`
   attaches nothing). Used by: `Put.spec`, `put.spec`.
3. The attachment invariant of "from 3c" is stated as `Txn.attached s ls` (txn's `Api.lean`): the
   store `s`'s keys' leases are live and are `itemMap`, each live object's item set is its keys. If 3c
   or 3e states it, txn will use theirs.


## from 3a

The apply layer (3a) owns the lessor's state on the apply thread (`Apply.lessorSt le lt s`: live
leases `lt`, attached to the keys of the store `s` that name them; `Apply.lessorOk le mc`: the
minimum TTL `mc.minLeaseTTL`), and the request path reads it concurrently (`Apply.lessorRead le`).
Needed:
1. **`Grant(id, ttl)`**: `ErrLeaseNotFound` for `id = 0`, `ErrLeaseTTLTooLarge` above `MaxLeaseTTL`,
   `ErrLeaseExists` for a live id, else the lease live with TTL `max ttl minLeaseTTL` (W0's
   `leaseStep` success).
2. **`Revoke(id)`**: `ErrLeaseNotFound`, or the lease gone and its keys deleted at one revision
   (through the range deleter, 3e's store: W0's `State.revoke`).
3. **`Checkpoint(id, remaining)`**: always `nil`; the model state unchanged.
4. **`Lookup(id)`, `Lease.Keys()`** (the auth applier's `checkLeasePuts`): at the apply thread, the
   live lease and its attached keys at `lessorSt`; concurrently (`CheckTxnAuth`), any answer.
5. The variance between members (`Grant` at another minimum): only the TTLs differ (3a's `ttlEq`).
Used by: `applierV3backend.{LeaseGrant,LeaseRevoke,LeaseCheckpoint}.spec`, `checkLeasePuts.spec`,
`checkLeasePutsKeys.spec`, `opStep_ttl.spec`.
```go
l, err := a.options.Lessor.Grant(lease.LeaseID(lc.ID), lc.TTL)               // backend.go:84
```

## from 2c (round 1)

`lease`'s sentinels (`ErrLeaseNotFound`, `ErrLeaseExists`, `ErrLeaseTTLTooLarge`) hold `srvErrVal e`
(`errors/Api.lean`; a law of the package's initialization): the gRPC handler's
`errors.Is(err, lease.ErrLeaseNotFound)` depends on it. `ErrNotPrimary` is unmapped
(`srvErrNotMapped`, a message).

## from 3e

mvcc (`Spec/go_etcd_io/etcd/server/v3/storage/mvcc/Api.lean`) now threads 3c's writer token, as 3c
asked (`req/..._storage_mvcc.md`, "from 3c"): `KV.Put`/`Txn.Put` take `Lease.lessorState γl n ls` with
`⌜lid = 0 ∨ ls.leases lid ≠ none⌝` and give it back at `putLs ls pres k lid`; `KV.DeleteRange`/
`Txn.DeleteRange` at `delsLs ls ds`; `KV.Restore` and `NewStore` at `RestoreLs ls s ls'` (any order of
the re-attachments; `NewStore` first `{ls with rd := rd}` by `SetRangeDeleter`); the range deleter's
contract is `Mvcc.mvccDeleter_rdOk.spec` (a law giving `Lease.rdOk γl rd n ls P D Q` for mvcc's `P`,
`D`, `Q`). What mvcc needs of 3c in return:

1. **`isLessor le γ c` gives `le ≠ null`** (mvcc's `delete` calls `s.le.GetLease` unconditionally and
   `restore` panics on a `nil` lessor with a leased key): a law `isLessor_ne_null`, or say it is in the
   definition.
2. **`rdOk`'s method calls** are written `td @!! TxnDelete.ty @!! "DeleteRange"` (a call through the
   `TxnDelete` interface type); mvcc's transaction contracts are at `methods ty "DeleteRange" v` for
   `td = interface.mkOk ty v` (the dynamic type's method, `Mvcc.shapes`). mvcc's `mvccDeleter_rdOk`
   proof bridges them; if Perennial has a lemma relating the two forms, 3c may use either.
3. **`rdOk`'s `D` lends `beTxHeld ls.be`**: mvcc lends `Mvcc.kbHeld B` (`mvccTxn_held.spec`) for
   `ls.be = GoInterface.ok (storageVal B)`: the integration identifies `beTxHeld` (3c's provisional) with
   `kbHeld` (4a proves both are "the batch lock is held").
4. **`GetLease` at the writer's own state**: mvcc's sketches use `lessor.GetLease.spec` with
   `lessorLb γ n` from the writer's token (`lessorState_at`) and `lessorState_le` to get `j = n`.
Used by: `KV.Put`, `KV.DeleteRange`, `KV.Restore`, `Txn.Put`, `Txn.DeleteRange` contracts, `NewStore.spec`,
`storeTxnWrite.put/delete.spec`, `store.restore.spec`, `mvccDeleter_rdOk.spec`; snippets
`examples/specreq/mvcc/lease.go`.

## from 2e, round 1

`leaseBootRes_intro` (provisional): at `ecfg.leaseExpiry = true`, with no premise; the no-expiry mode
needs your deployment premise (`batch-2e.md` Q6).

## from 4b

The schema's lease functions are stated over the transaction contracts (`Schema.txRd`, `txWr` of the
batch transaction, lock held, at the caller's view family `R` and scope with `lease` whole) and the
bucket's encoding `Schema.leaseBktIs m L` (`L : w64 → Option LeaseRec`: id ↦ (id, TTL, remaining)):
`UnsafeCreateLeaseBucket.spec`, `MustUnsafeGetAllLeases.spec` (fresh `leaseAt p r`, in id order),
`MustUnsafePutLease.spec` (any `leaseEnc` of the struct's fields under `beU64 id`),
`UnsafeDeleteLease.spec`. Your provisional `beLeases be B` is then your realization: `∃ m L, R V`
with `V .lease = some m ∧ leaseBktIs m L ∧ B = (TTL of L)` for 4a's part (`req/..._storage_backend.md`,
"from 4b"). `semver`: `Semver.Version.LessThan.spec` computes `SemVer.ltb` of the two models
(`api/version.LessThan` of two `Version` values is 3h's, over `Semver.verOf`).
