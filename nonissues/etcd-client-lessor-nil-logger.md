---
upstream: none
checked: 2026-11-09
links: []
blocks-proof: no
---

# clientv3: a lessor built with `NewLeaseFromLeaseClient(remote, nil, ttl)` panics on a keep-alive stream error

`NewLeaseFromLeaseClient` sets the lessor's logger only from its client argument (`if c != nil {
l.lg = c.GetLogger() ... }`, `client/v3/lease.go`); with a `nil` client `l.lg` stays `nil`. The
keep-alive loops log through it without a check: `recvKeepAliveLoop` calls `l.lg.Warn` when
`resetRecv` fails, `sendKeepAliveLoop` when a `Send` fails. zap's `(*Logger).Warn` reads the
receiver's fields (`log.check` reads `log.core`), so with a `nil` logger the goroutine panics, which
crashes the program. `recvKeepAlive` guards its own `Warn` with `if l.lg != nil`; the loops do not.

**Why not an issue:** found by code reading (batch 1c of the specs-only branch, 2026-11-09); no test.
Every in-tree caller passes a client (`NewLease`, `v3client.New`); the API documents nothing about a
`nil` client. A test could promote it: `NewLeaseFromLeaseClient` over a `LeaseClient` stub whose
`LeaseKeepAlive` returns an error, a `nil` client, then `KeepAlive`.

## Proof

no: `NewLeaseFromLeaseClient.spec` takes a client (`clientOpts c`, its logger an `isLogger`), which
every caller in scope passes.
