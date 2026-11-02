# The closed lease-grant example (2026-11-02; branch `lease-grant`)

The stage after `notes/lease-ex-plan.md`: a Go program that grants a lease through etcd's client and
then lists the leases, with a closed theorem that it does not panic. Lean-first (no Rocq
counterpart). It is `notes/leases-plan.md`'s L3c (grant half) and L4 (`EtcdServer.LeaseGrant`),
cut to what the example needs.

## Scope (2026-11-02; the user's choice: "Grant, then Leases")

`examples/leasegrant`'s `Main` starts one member, serves it, connects a client,
`cli.Grant(ctx, 600)` (returns on an error: a server-chosen id can collide, `ErrLeaseExists`, and a
call can time out), then `cli.Leases(ctx)`, and panics unless the granted ID is listed. Auth off.
Revocations stay out of the server's workload (`rqOk .leaseRevoke = False`, as on `lean`); expiry
stays out (`notes/leases-plan.md` Q1(b), the user's choice of 2026-10-24).

## What is missing (the survey, 2026-11-02)

The grant is closed at five places on `lean`:

1. **No guard.** The server's grant guard `srvGrantGuard` (`InvApplier.lean:473`) is `False`:
   `NewLessor`'s `GA`, which every grant needs (`leaseGranted`). `lessorOk`'s `ExpiredLeasesC`, the
   dead expiry arms of `run` and `UberOn`'s `lookupNil` rely on it being `False`: expiry and the
   guard must be separated (a trust-boundary contract, `lessorOk`; the `NewLessor` axiom).
2. **No proposal.** `reqPropOkW` (`InvRequest.lean:567`) takes `plainReq`; `plainCover`
   (`KVModelDefs.lean:72`) has no grant.
3. **No apply.** `rqOk .leaseGrant = False` (`apply/Chain.lean:264`); the dispatch arms close by
   absurdity; `isApplyLessor`'s Grant clause (`apply/Contracts.lean:360`) is not exact (no
   `id' = id`, no `L ++ [id]`); `applierV3backend.LeaseGrant.spec`'s post says nothing of the live
   set; the apply thread does not lend `AEnv.RW` (the lease bucket's write).
4. **Nothing reaches the caller.** A request's reply (`appliedOk`, `InvProposer.lean:505`) carries
   no lease state.
5. **No lower bound on reads.** `lessor.Grant.spec` (exact: `L ++ [id]`, errors iff `id = 0`,
   `ttl > MaxLeaseTTL` or `id ∈ L`) returns no fact of the lessor's history; `lessorRdBody` does not
   say that a live id stays live; `kv_lease_served` fixes `lessorLb γl 0` once; the client's
   `etcdLeaseLeasesSpec` says only `Nodup`, `etcdLeaseGrantSpec` only `id ≠ 0`.

Also on the path: `EtcdServer.LeaseGrant` (`v3_server.go:434-456` at the pin: `r.ID = Next() &
(2^63-1)` until nonzero, `requireAuthInfo`, `raftRequest`, the response's type assertion), unproved;
the snapshot walk's empty-lease-bucket premise `hlease` (`SnapApplyWalk.lean:67`), false once a
grant is applied (a single member is never sent a snapshot, but `run`'s proof is generic);
`kv_lease_served` without the Grant method.

`notes/leases-plan.md`'s own L3b/L3c tie the model's lease table to the lessor's live set
(`leasesLive`: `L = lt.ids`, `ApplyKV` carrying the table) and move the server's results to
`kvModelSt γk Lq`; the example does not need that tie (below, S1).

## Scope questions (for the user)

- **S1. How far the apply side goes.** (a) *Narrow* (recommended): the grant admitted through the
  request path and the apply thread, its fact taken from the lessor's history (a persistent
  "`id` live from index `i`", `leaseLiveFrom`), handed to the caller through the reply; the KV
  model's table stays untied to the lessor (L3b's tie, leased puts and the results at
  `kvModelSt γk Lq` later). (b) *Full L3b/L3c*: the table tied to the lessor, leased puts and
  transactions admitted, the server's results restated at the table; the example on top.
- **S2. Expiry.** A lease the example grants must not expire before `Leases` runs (TTL 600 s; the
  run takes seconds). (a) *A named deployment premise* (recommended): `opaque leasesNoExpiry : Prop`,
  as `leasePeersOk`, a hypothesis of `leasegrant_safe`, under which `lessorOk`'s `ExpiredLeasesC`
  carries nothing (a restated trust-boundary contract). (b) The same as an unconditional trusted
  change to `lessorOk` (no premise in the result).

**Decided (the user, 2026-11-02):** S1 (a), narrow; S2 (a), the named premise `leasesNoExpiry`.

## Stages

Draft → Review (an independent spec reviewer) → Test (the Go test) → the `axiom` skill on every new
or restated trusted statement → Probe → Freeze (the user) → Prove.
