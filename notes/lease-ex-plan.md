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
  only the not-found arm does), down to the trust-boundary `leaseTimeToLive`: a trusted change for
  Freeze. It is true on every path (D3: the follower's `leasehttp.TimeToLiveHTTP` checks the
  leader's reply against the asked ID), so the check needs no assumption about the cluster. Grants are a later stage.
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

## Draft (2026-11-02)

**D1. F4** (`InvGrpc.lean`): the axiom `grpc.serve` restated, a run's slot `S ∗ threadTok`
(`grpc_serve_rpcs_tok`; `grpc_serve_rpcs` keeps its statement through `grpcMethodsOkMd_frame`).

**D2. The wire** (`client/v3/InvLeaseRead.lean`): `pbLeaseTimeToLiveRequest` (`(ID, Keys)`; the
server's decoded copy read-only as a whole, which `LeaseServer.LeaseTimeToLive` takes),
`pbLeaseTimeToLiveResponse` (`LeaseTTLRespM`: header, `ID`, `TTL`, `GrantedTTL`; the `Keys` slice a
field, its contents not modelled), `pbLeaseLeasesRequest` (nothing), `pbLeaseLeasesResponse`
(`LeaseLeasesRespM`: header, the IDs in order); etcd's specs `etcdLeaseTTLSpec` (the reply's ID is the
asked one) and `etcdLeaseLeasesSpec` (no ID twice); the options (`leaseOptSpec`, `leaseOptsAt`,
`leaseKeysFold`, as the KV's `optSpec`).

**D3. The server's answer about the asked lease** (trusted and frozen statements): `⌜w.ID' = v.ID'⌝`
added to the success arms of the trust-boundary `EtcdServer.leaseTimeToLive.spec` (the leader's
literal has `ID: r.ID`; a follower's `leasehttp.TimeToLiveHTTP` returns only a reply whose ID is the
asked one, `lease: TTL id mismatch` otherwise, `http.go:274`), `EtcdServer.LeaseTimeToLive.spec`,
`ttlAns` and `leaseTTLOut` (proofs updated).

**D4. Served** (`client/v3/LeaseReadServed.lean`, `examples/common/ServedLease.lean`): the
handler meets (`etcd_leaseTTLHandlerOk`, `etcd_leaseLeasesHandlerOk`, at the contract's slot with
the lower bounds), the generated handlers' (`etcd_leaseTTLMethodOk`, ...), the promotions through
`quotaLeaseServer` (`QuotaLeaseLemmas.lean`), `etcdLeaseReadAt addr`, and `common.kv_lease_served`
(`kv_served` with the lease reads, under `threadBound GF ≤ 2 ^ 30 - 1`). The examples' `memberBuilt`
and `memberUp` carry `srvLeaseRd s E` (`NewServer`'s `srvLessorRd`, `lessorRdPool`), `grpcUp` the
Lease service `v3rpc.Server` registered (`grpcLeaseUp`).

**D5. The client** (translated: `lessor.TimeToLive`, `lessor.Leases`, `LeaseOp.applyOpts`,
`toLeaseTimeToLiveRequest`, the retry lease client's and the stub's two reads, the getters): specs
as `lessor.Grant`'s; `lessor.TimeToLive` over the options' `Keys` (`leaseKeysFold gs false`);
`lessor.Leases`' result a fresh `[]LeaseStatus` of the reply's IDs. Linked in the client's `Link`.

**D6. The example**: project `leasekv` (`etc/goose.py`, `etc/gen-init.py`), `Main` returns nothing
(as putget's; each read in a context with the request timeout), `leasekv.Main.spec` (putget's
premises at leasekv's addresses), `leasekv_Main`, `leasekv_safe` (`Adequacy.lean`, as putget's).

**Left `sorry` for Prove**: the handler and method meets, `kv_lease_served`, the client's
`applyOpts`, `toLeaseTimeToLiveRequest`, `lessor.TimeToLive`, `lessor.Leases`, `Main`.

**Bounds** (for Freeze): `etc/bounds-check.py`'s stock count in `examples/common` goes 23 → 29, all
six from `kv_lease_served`'s statement repeating `kv_served`'s slot premises (the same stocks,
counted twice). Prove should factor `kv_lease_served` through a `kv_served` generalized over extra
methods, with the slots in one definition, which brings the count back; else the baseline moves.
