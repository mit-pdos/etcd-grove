# Review: `Client_LeaseTimeToLive_dist` (N9b draft) — sound with a fix

2026-11-25, `axiom` skill, an independent review requested by #50's coordinator-E (comment
2026-11-25T15:22:46Z, item 6). Branch `etcd-safe-n9b` (reviewed at `b0076abbbe`). Shares the token
finding, the docstring obligations and the real-cluster test with
[n9b-lease-leases](n9b-lease-leases.md) (§3–§5 there).

**Reviewed:** `etcd_dist.Client_LeaseTimeToLive_dist.spec`
(`Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/ClientLeaseTTLDist.lean`), as used by
`leaseReadCheck` (`cli.Lease.TimeToLive(tctx, leaseReadID)`, no options). Go at the etcd pin
`e94f33b50`, go1.27.3.

## Verdict

**Sound with a fix.** No program refutes it. The fix is the one applied to the Leases draft: the caller's
`levelTok 0` is lent and returned, as in the proved `lessor.TimeToLive.spec` (commit `9b147c4c0e`). The
same `etcdSvc`/`Serve_dist` docstring obligations apply (entry `etcdLeaseTTLSpec` for
`/etcdserverpb.Lease/LeaseTimeToLive`).

## 1. The claims

Same preconditions as the Leases draft, `lp.TimeToLive(ctx, id, nil)`: no panic; `(resp, nil)` with
`resp.ID ↦□ id` (the lease asked), or `(nil, err)` with `err ≠ nil`. Nothing about TTL, granted TTL or
keys, and nothing about whether the lease exists.

## 2. The Go code: every successful answer is about the lease asked

- Client, `client/v3/lease.go:246-260`: `ID: LeaseID(resp.ID)` from the server's reply; on error
  `nil, ContextError(ctx, err)` (non-nil). With no options, `Keys` is false.
- Leader, `v3_server.go:637-670`: `Lookup(r.ID)`; found: `ID: r.ID`; not found: `ErrLeaseNotFound`,
  which `v3rpc/lease.go:62-76` turns into a success with `ID: rr.ID, TTL: -1`. A lease revoked or
  expired between the request and the lookup is either found (`ID: r.ID`) or not (`ID: rr.ID`); a
  demoted lessor gives `ErrLeaderChanged` (an error).
- Follower, `v3_server.go:672-697`: forwards to the leader's `LeaseInternal` handler over the peer
  HTTP; `leasehttp.TimeToLiveHTTP` (`server/lease/leasehttp/http.go:223-276`) maps 404 to
  `ErrLeaseNotFound` (then `ID: rr.ID` as above) and **rejects** a reply whose ID is not the one asked
  (`"lease: renew id mismatch"`, an error). Timeout or no leader: `ErrTimeout`/`ErrCanceled`.
- `TTL == -1` for an unknown lease (asked about): the spec claims nothing of `TTL`, so the `-1` (and a
  `0`/negative remaining TTL of an expiring lease) is allowed.

## 3. Attacks tried, and why each failed

| attack | why it fails |
|---|---|
| Unknown lease (`TTL -1`), lease `0`, random 63-bit IDs | the not-found path echoes `rr.ID` (tested: 172577 `TTL -1` replies, all with the asked ID) |
| Lease revoked/expiring concurrently | found → `ID: r.ID`, not found → `ID: rr.ID`; never another lease's ID |
| A follower's forwarded answer from a leader that changed meanwhile | `TimeToLiveHTTP` checks the ID; a demoted leader errors |
| A lagging member (`SIGSTOP`ped follower), linearizable vs serializable | the ID does not depend on the member's state; the TTL, which does, is not claimed |
| Errors, timeouts, killed leader | `(nil, err ≠ nil)`; allowed |
| Redirecting `cli.Lease`, a non-etcd server at `ep`, aliasing, concurrent calls | as in the Leases review, §5 |
| Options (`WithAttachedKeys`) | out of the draft's domain (`slice.nil` only); with keys the server's auth check may error, still the asked ID |

Real-cluster test: the Leases review's, whose readers call `TimeToLive` after each `Leases` on an ID drawn
from `7` (the workload's `leaseReadID`, never granted), a granted lease (often revoked or expired), or a
random one, and panic if `resp.ID` differs: 176609 calls, 39 errors, no violation.

**Not tried:** as in the Leases review.
