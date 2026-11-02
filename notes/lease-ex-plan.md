# The closed lease client example (2026-11-02; branch `lease-ex`)

The stage after `notes/lease-src-plan.md`: a Go program using etcd's client lease API against a
member started in-process, with a closed theorem (as `watchkv`'s `watch_safe`) that it does not
panic. Lean-first (no Rocq counterpart).

## Scope (2026-11-02; the user's choices)

- **State-independent reads** (revised from "reads on an empty lessor", which needs a new
  invariant that the lessor's history stays empty). `Main` starts a member, serves it, connects a
  client and checks what holds whatever the lessor holds: `cli.Leases(ctx)` lists no lease twice
  (`leaseIdsAt`'s `Nodup`), and `cli.TimeToLive(ctx, id)` answers about `id` (the reply's `ID`);
  it panics otherwise. The second check needs `leaseTTLOut`'s found arm to state the ID (today
  only the not-found arm does), down to the trust-boundary `leaseTimeToLive` (the follower path
  returns the leader's HTTP answer, which `leasehttp.TimeToLiveHTTP` does not check against the
  asked ID, unlike `RenewHTTP`): a trusted change for Freeze. Grants are a later stage.
- **F4 in grpc's model** (the lease-src review): a run of a served method holds its goroutine's
  `threadTok` (Perennial's `wp_fork` gives it one). Done as a restatement of the axiom
  `grpc.serve` (`InvGrpc.lean`): the method meets are at `S ∗ threadTok`, and `grpcServes` carries
  `S ∗ threadTok`; `grpc_serve_rpcs` keeps its statement (`grpcMethodsOkMd_frame`), so its callers
  are unchanged; `grpc_serve_rpcs_tok` is the form the lease reads use. This repository's grpc
  model, not Perennial. A trusted change for Freeze.
- **Auth off**, as `watchkv`.

## What is missing (the survey)

Server side:
1. The wire models of the two reads: `pbLeaseTimeToLiveRequest`/`Response`,
   `pbLeaseLeasesRequest`/`Response` (as the client's `pbLeaseGrantRequest`, `InvLease.lean`).
2. The served specs a client may assume (`GrpcSpec`s), and the handler meets
   (`grpcHandlerOk` of `*quotaLeaseServer`'s promoted `LeaseTimeToLive`/`LeaseLeases`), from
   `LeaseServer.LeaseTimeToLive`/`LeaseLeases`' specs and `raftLeaseRead_server`.
3. F4: done (D1, the `grpc.serve` restatement).
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
