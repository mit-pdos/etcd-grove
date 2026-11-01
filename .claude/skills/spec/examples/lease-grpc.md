# The gRPC lease reads (item 6, 2026-11-01)

`v3rpc/lease.go`'s `LeaseServer.LeaseTimeToLive` and `LeaseServer.LeaseLeases`: call the server's
method of the same name, map `ErrLeaseNotFound` to the handler's own response, and `fill` the
response's header. The full design is `notes/lease-grpc-plan.md`.

## The first version

No contract: the handlers took the server's proved `EtcdServer.LeaseTimeToLive.spec` and
`EtcdServer.LeaseLeases.spec` as callee specs, and their answers restated the server's.

## The review and what it changed

1. **The server's header ids leaked** (reviewer): `LeaseLeases`' header is `newHeader()`'s, at the
   server's ids (`srvHeaderFacts s cs ms`), and the spec tied them to the `*LeaseServer`'s
   (`leaseServerAt p s A cid mid`); no caller can show them equal, and `fill` overwrites them.
2. **The bounds leaked**: the handlers' specs inherited the server's `threadBound`/`receiptBound`
   premises (+3 on the bounds gate).
3. **Redesign**: a persistent contract `raftLeaseRead s E γl S R` (the two entry points at per-call
   resources `S` and the revision reader `R`), whose answers (`ttlAns`, `leasesAns`) quantify the
   server's ids inside; `raftLeaseRead_of_server` discharges it, taking the bounds premises.
4. **`errors.Is` twice**: Go tests `errors.Is(err, ErrLeaseNotFound)` twice; Perennial's spec let the
   two calls disagree, so a proof reached `fill(resp.Header)` at `resp = nil`. The user chose a
   general Perennial change (`errors.Is` as a deterministic walk over exact method relations), not a
   local axiom; `applyErrIs` now carries an exact tree.
5. **Trusted statements strengthened in place** (S1, S2): the response's header owned, because `fill`
   writes it. A margin stated, not closed: the `ErrLeaseNotFound` answer carries no authentication,
   though Go authenticates first.

## Approved

The user approved all five at Freeze without further critique: S1, S2, the margin, the exact
`applyErrIs` tree and `leasesRespIs`'s split. The specs: `Spec/.../v3rpc/LeaseServer__LeaseTimeToLive.lean`,
`LeaseServer__LeaseLeases.lean`, over `Proof/.../v3rpc/InvLeaseRead.lean`.
