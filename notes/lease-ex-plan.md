# The closed lease client example (2026-11-02; branch `lease-ex`)

The stage after `notes/lease-src-plan.md`: a Go program using etcd's client lease API against a
member started in-process, with a closed theorem (as `watchkv`'s `watch_safe`) that it does not
panic. Lean-first (no Rocq counterpart).

## Scope (2026-11-02; the user's choices)

- **Reads on an empty lessor.** The server grants no lease (`srvGrantGuard` is `False`: no verified
  proposer sends a `LeaseGrant`), so `Main` starts a member, serves it, connects a client and
  checks `cli.Leases(ctx)` has no lease and `cli.TimeToLive(ctx, id)` answers `TTL == -1` (the
  handler's own `ErrLeaseNotFound` reply); it panics otherwise. Grants are a later stage.
- **F4 in grpc's model** (the lease-src review): `grpcHandlerOk` (and its `Md`/`Own` variants) carry
  the run goroutine's `threadTok` (Perennial's `wp_fork` gives it one) in their pre and post, for
  every handler: the served lease reads need it (`raftLeaseRead`'s `S := E.RD ∗ threadTok`).
  This repository's grpc model, not Perennial.
- **Auth off**, as `watchkv`.

## What is missing (the survey)

Server side:
1. The wire models of the two reads: `pbLeaseTimeToLiveRequest`/`Response`,
   `pbLeaseLeasesRequest`/`Response` (as the client's `pbLeaseGrantRequest`, `InvLease.lean`).
2. The served specs a client may assume (`GrpcSpec`s), and the handler meets
   (`grpcHandlerOk` of `*quotaLeaseServer`'s promoted `LeaseTimeToLive`/`LeaseLeases`), from
   `LeaseServer.LeaseTimeToLive`/`LeaseLeases`' specs and `raftLeaseRead_server`.
3. F4: the token in `grpcHandlerOk`; `etcdRunSlot`'s users.
4. `examples/common`'s `Serve`: the lease methods' registrations into `isGrpcRpcs` (`v3rpc.Server`'s
   `leaseRegs`, from lease-src).

Client side:
5. Translation: `lessor.TimeToLive`, `lessor.Leases`, `toLeaseTimeToLiveRequest`,
   `retryLeaseClient.LeaseTimeToLive`/`LeaseLeases` (`client/v3/lease.go:246-272`,
   `retry.go:142-148`; not in `Code/go_etcd_io/etcd/client/v3.toml`), and their specs (as
   `lessor.Grant.spec`'s: over `isGrpcRpcs addr "/etcdserverpb.Lease/LeaseTimeToLive" Spec`).

The example:
6. `examples/leasekv` (Go, a test), its Goose project, `Init.lean`, `Main`'s proof, the adequacy
   theorem.

## Stages

Draft → Review (an independent spec reviewer) → Test (the Go test) → Probe → Freeze (the user) →
Prove.
