# Plan: the lease rows' key checks (spec-first; branch `lease-keys`)

Status (2026-10-31): **Scope**, for the user's decisions (Q1-Q3 below). Nothing drafted. Started at
the user's request: the first of the three items that would let the repository answer
etcd-io/etcd#22595 ("Plan to revert Auth to Beta"), whose requirement "an audit to verify that RBAC
covers all etcd operations" `notes/auth-matrix.md` answers for every row but the lease keys.

## The gap

The matrix's rows that check **the keys a lease holds** are checked in Go but not stated:

| row | Go check | layer | translated |
|---|---|---|---|
| `Put` with a lease (also inside `Txn`) | `checkPutAuth` → `checkLeasePuts` → `checkLeasePutsKeys`: admin, or `IsPutPermitted` of every key of the lease | apply | yes, proved; `putClass` omits the lease's keys |
| `LeaseRevoke` | `authApplierV3.LeaseRevoke` → `checkLeasePuts` | apply | yes, proved; post states no class |
| `LeaseKeepAlive` | `EtcdServer.checkLeaseRenew`: admin, or `IsPutPermitted` of every key; then `ErrAuthOldRevision` if the auth revision moved | API | no (names only) |
| `LeaseTimeToLive` (`Keys = true`) | `checkLeaseTimeToLive`: admin, or `IsRangePermitted(k, "")` of every key; revision re-checked after the lookup | API | no |
| `LeaseLeases` | `checkLeaseLeases`: admin, or `IsRangePermitted(k, "")` of every key of every lease; revision re-checked | API | no |

GHSA-x35m-3gp4-4fh5 (a lease's keys not checked for a `Put` inside a transaction) is in this gap:
today's statements would not exclude it.

## What exists

- **The lessor has a key model, proved** (unit T3, L2b): `lease.Lease.Keys.spec` returns exactly
  the keys the item map `I` attaches to the lease (`k ∈ ks ↔ I.lookup ⟨k⟩ = some id`, no
  duplicates), for the holder of the lease owner's half `leaseItemsOwn l I id`, which
  `lease.leaseOwn γl L I` carries for every live lease.
- **At the apply thread the item map is the KV state's**: the contract's `Revoke` clause holds
  `lease.leaseOwn γ.leases L (mvcc.leaseItemsOf (mvcc.stateAfter log))`. So an apply-layer
  statement over `I` is a statement over the keys the KV state attaches to the lease.
- **The apply package does not use it**: `apply.isApplyLessor`'s `Lookup` clause returns
  `leaseIs l id`, whose `Keys()` returns *some* keys (only their length bounded), and that clause is
  a premise of `isApplyLessor_of_lessorInv` (not proved of the real lessor). `checkLeasePutsKeys`
  takes no owner resource, so it cannot know which keys it checked.
- **No lease request is in the model**: `apply.rqOk`'s `leaseGrant` (and the other lease kinds) is
  `False`, and the contract's `Revoke` clause is vacuous. The matrix's statements are per method (a
  triple of the handler), so this does not block them; it means no closed theorem exercises them.

## Two parts

**Part A: the apply layer** (`Put` with a lease, `Txn`'s puts, `LeaseRevoke`).
1. `apply.leaseKeysClass M info I id`: auth off at a recorded state, or the principal admin at one,
   or for every key `k` with `I.lookup ⟨k⟩ = some id`, `classRes M info [(k, "", .write)]`
   (the shape `putClass` already uses).
2. The `Lookup` clause of `isApplyLessor` returns a lease whose `Keys()` meets `lease.Lease.Keys.spec`
   for the owner (`leaseOwnIs l id`: `isLeaseObj l` and the lease's `ID`), and is proved of the real
   lessor (`lease.lessor.Lookup.spec` is proved): one premise of `isApplyLessor_of_lessorInv` goes.
3. `checkLeasePutsKeys`, `checkLeasePuts`, `checkPutAuth` take the owner's `leaseOwn γ.leases L I`
   (framed back) and, on `nil`, give `leaseKeysClass` for the request's lease; `putClass` gains it
   (`TxnOp`'s puts too, which needs the lease in `TxnOp`); `authApplierV3.LeaseRevoke` states
   `leaseKeysClass` on success.
4. **Ripple: small (checked).** The auth layer already holds the owner's resource: every KV
   method's precondition has `mPre`'s `kvOwn E log`, whose `leasesLive` is `lease.lessorUser
   γ.leases L (mvcc.leaseItemsOf (mvcc.stateAfter log))`, the owner's half at the KV state's item
   map. So `authApplierV3.Put`/`Txn`/`LeaseRevoke` lend it to the checks and take it back; no
   precondition of the chain changes. What changes is the class: `putClass` (and through it
   `reqClass`/`chainClass`) names the lease's keys, so it takes the log (`kvPost` has it), and the
   chain's layers above the auth applier pass the class through unchanged. These are definitions
   in `apply/AuthClass.lean` and `Chain.lean`'s `kvPost`, which the auth-mode merge
   (`notes/auth-mode-merge-plan.md`) may also touch: a merge to coordinate, not a dependency.

**Part B: the API layer** (`LeaseKeepAlive`, `LeaseTimeToLive`, `LeaseLeases`).
1. Translate `EtcdServer.checkLeaseRenew`, `checkLeaseTimeToLive`, `checkLeaseLeases` and the
   entry points `LeaseTimeToLive`, `LeaseLeases` (and `LeaseRenew`'s check call; `leaseTimeToLive`'s
   forwarding to the leader over `leasehttp` stays names-only, a contract).
2. These run on gRPC goroutines, not the lease owner: `Keys()` from a reader. The lessor needs a
   reader-side key model: the item set's history of each lease (or of the item map), so that a
   reader's `Keys()` returns the keys at some recorded point, and `Lookup`/`Leases` from a reader
   give live leases at some recorded point. A change to the lease package's invariant
   (`leaseItems`: today the owner's half and the lock's half of one set).
3. The class at recorded states, as the other API rows (`authPubLb`-style lower bounds): a
   successful check means each key, of a lease item set recorded no earlier than the check's start,
   was permitted at an auth state recorded no earlier than the check's start. The revision
   re-check (`ErrAuthOldRevision`) is what keeps the auth states' window to one revision; it
   becomes a clause of the spec.
4. Things to look at while drafting (possible findings): `LeaseTimeToLive` on a follower checks
   the follower's own lessor's keys, then asks the leader (`leaseTimeToLive` forwards over HTTP),
   so the keys checked and the keys returned come from different lessors; `checkLeaseTimeToLive`
   returns `0` with its error (unused by the caller).

## Questions for the user

- **Q1, scope.** (a) Part A only (the apply layer: the GHSA-x35m class; small, its ripple internal
  to the auth applier and the class definitions); (b) A then B (B is larger: a translation, the
  reader-side lessor history, three specs); (c) B first (the API layer and the lease package
  only). Recommended: (b), A first.
- **Q2, the key set.** The class over the lessor's item map `I` (what Go checks), which at the apply
  thread is the KV state's `leaseItemsOf` (so both readings agree there); at the API layer only the
  lessor's recorded item sets are available. Recommended: over `I`, with the apply-layer corollary
  over `leaseItemsOf`.
- **Q3, Part B's freshness.** As the other API rows: states recorded no earlier than the call's
  start (lower bounds), not the latest state. Recommended.
