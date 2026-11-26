# Review: `Client_LeaseLeases_dist` (N9b draft) — sound with a fix

2026-11-25, `axiom` skill, an independent review requested by #50's coordinator-E (comment
2026-11-25T15:22:46Z, item 6) before the draft becomes a per-function interim axiom. Branch
`etcd-safe-n9b` (reviewed at `b0076abbbe`).

**Reviewed:** `etcd_dist.Client_LeaseLeases_dist.spec`
(`Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/ClientLeaseLeasesDist.lean`), as used by
`dist/client`'s `leaseList`/`leaseReadCheck` (`examples/etcd/dist/client/lease.go`). Go at the etcd
pin `e94f33b50` (`etc/goose.py`, project `etcd`), toolchain go1.27.3. The companion
`Client_LeaseTimeToLive_dist`: [n9b-lease-ttl](n9b-lease-ttl.md) (shares §3 and §4).

## Verdict

**Sound with a fix.** No program refutes it. One fix applied (commit `9b147c4c0e`): the triple now lends and
returns the caller's `levelTok 0` (§3). Two docstring obligations remain for when it becomes an
axiom (§4).

## 1. The claims

With `isNewClient cl [ep] V`, `clientNoProxy cl`, `clientF cl "Lease" ↦□ lp` (a `*lessor`),
`etcdAddrAt ep γE mid` and a client context (`ctxOk`, `ctxErrClient`), `lp.Leases(ctx)`:
1. does not panic or get stuck;
2. returns `(resp, nil)` with `resp.Leases ↦□ sl`, `sl ↦* ids.map LeaseStatus.mk` (owned), `ids.Nodup`;
3. or returns `(nil, err)` with `err ≠ nil`.
Nothing of the member's view (`envAt`) or its lessor's state is read or claimed.

## 2. The Go code

- Client, `client/v3/lease.go:262-272`: `l.remote.LeaseLeases(ctx, …)`; on `err == nil` a fresh
  `make([]LeaseStatus, len(resp.Leases))` filled with `LeaseStatus{ID: LeaseID(resp.Leases[i].ID)}`
  (`LeaseStatus` has the one field `ID`), returned in a fresh `LeaseLeasesResponse`; else
  `nil, ContextError(ctx, err)`. `ContextError` (`client.go:610-630`) returns `nil` only for
  `err == nil`; it can replace `err` by `ctx.Err()` only when that is non-nil. No panic path.
- Server, `server/etcdserver/v3_server.go:738-750`: `s.lessor.Leases()` (`server/lease/lessor.go:464-478`:
  one entry per value of `leaseMap`, keyed by the lease's own ID, sorted by expiry), the auth check,
  then one `LeaseStatus` per lease. `v3rpc/lease.go:78-91` passes it on. So every successful listing
  of a real member names each ID at most once, at any of its lessor's states: leader or follower,
  lagging or not, with leases granted, revoked or expiring concurrently. The listing is the member's
  local lessor, not a linearizable read, and the spec claims nothing about which leases it lists.

## 3. Finding (fixed): the triple took no thread token

The proved in-process `lessor.Leases.spec` (`Spec/go_etcd_io/etcd/client/v3/lessor__Leases.lean`)
takes `levelTok 0` and gives it back: the retry interceptor's backoff (`waitRetryBackoff` →
`roundRobinQuorumBackoff`) reads `c.Endpoints()` under `epMu.RLock()`, a reader slot the
repository pays with the caller's level-0 token (`backoffOkT`, `InvRetry.lean`, decision of
2026-11-24 "prove-ps2-clientrdlock"; CLAUDE.md, "Bounds"). The draft took none. `threadBound` is any
number above 1 (`ThreadGS`), so the draft claimed "no panic, no stuck thread" with any number of
concurrent callers, while Go's `RWMutex` supports at most `2^30` readers (`rwmutexMaxReaders`);
and S2's proof of the statement over the grpc model (its intended retirement) could not discharge the
interceptor's `backoffOkT` without a token. Not runnable as a counterexample (it needs `2^30` live
goroutines), so recorded as a bounds gap, not a refutation.

**Fix (applied):** `levelTok 0 ∗` in the pre and `levelTok 0 ∗ (…)` in the post, as
`lessor.Leases.spec`. Callers: `leaseList.spec` takes and returns it too; `leaseList`'s and
`leaseReadCheck`'s proofs thread it (`RunLeaseRead`/`leaseReadCheck` already held it). Elaboration
check: see the commit message / handoff in `notes/etcd-dist-n9b.md` §9.

The same gap is in the reviewed `Client_Get_dist`/`Client_Put_dist` (their in-process
`client_Get_own` takes `levelTok 0`, the dist axioms do not): not in this review's scope; reported to
the coordinator.

## 4. Obligations when it becomes an axiom (docstrings, low)

- `etcdSvc`'s docstring (`S2Interim.lean`) gives the intended entries: "`grpcNoCall` for the methods no
  client of the theorem calls". With this axiom, `/etcdserverpb.Lease/LeaseLeases` is called; its
  entry must be `etcdLeaseLeasesSpecAny` (heap-free, view-free, `InvLeaseRead.lean`), which a member's
  handler meets in one process (`LeaseReadServed.lean`).
- `Serve_dist`'s docstring (review F4) says each connection to `a` carries the calls of
  `Client_Put_dist`/`Client_Get_dist` and "a unary call of etcd's KV table": add the lease reads.
The draft's docstring now states both.

## 5. Attacks tried, and why each failed

| attack | why it fails |
|---|---|
| Errors and timeouts (deadline, cancel, member down, `SIGSTOP`, killed leader) | every error path returns `nil, err` with `err ≠ nil` (`ContextError`); the spec allows any error |
| Duplicate IDs in a listing (concurrent grant/revoke/expiry, leader change, a lagging member) | the listing is the values of one map keyed by ID (`unsafeLeases`); tested below |
| A stale or partial listing from a lagging member (serializable vs linearizable) | not claimed: the post is about no ID twice, nothing about which leases |
| Redirect `cli.Lease` to another `*lessor` (e.g. `NewLeaseFromLeaseClient` over a fake `LeaseClient`) so the call reaches a non-etcd server | `isNewClient` already holds `clientF cl "Lease" ↦□ lp'` with `lessorAt lp' [ep]`; `↦□` agreement forces `lp = lp'`, and a persistent field cannot be written in the logic |
| A non-etcd server at `ep` (bridge, proxy, a fake gRPC server) | as for `Client_Get_dist`: `clientNoProxy` (F1), `bridge.New` consumes `netAddrLeft` (review 4), `etcdSvc` has no law so no grpc `Serve` serves it (s2-interface); and unlike Get's, this post holds of any real etcd member, so a relay to another etcd breaks nothing |
| Aliasing of the returned slice / response | fresh `make` and a fresh struct; the library keeps no reference |
| Concurrent calls on one client, calls after `Close` | no shared mutable state in `lessor.Leases`; after `Close` the conn is closed and grpc returns an error |
| Auth enabled / learner member | an error (`checkLeaseLeases`, the learner interceptor) |
| Cross-world entailment | none: a triple whose pure post is about values made in this run |

**Test against a real cluster** (the etcd binary built from `e94f33b50`, `go build ./server`): 3
members on loopback; 4 goroutines grant leases of TTL 1–3 s and revoke half; 9 reader goroutines (3
per member, each with a client of its one member, as `newClient([]string{addr})`) call
`Leases` and check no ID twice, then `TimeToLive` (§ of the TTL review); after 8 s a follower is
`SIGSTOP`ped for 6 s, then the leader is `kill -9`ed and restarted 6 s later; 40 s in all. Result:
`Leases calls 176609 (errors 27); TimeToLive calls 176609 (errors 39, TTL -1: 172577); no violation`.
Program and harness: `n9b-lease-check.go.txt` (in `tests/` of an `e94f33b50` checkout),
`n9b-lease-check-run.sh.txt`.

**Not tried:** `2^30` concurrent callers (§3); TLS/auth deployments (not `etcd_safe`'s); a member of a
mixed-version cluster.
