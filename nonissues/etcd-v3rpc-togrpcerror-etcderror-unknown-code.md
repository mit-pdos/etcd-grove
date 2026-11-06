---
upstream: none
checked: 2026-11-06
links: []
blocks-proof: no
---

# v3rpc: "too many requests" and "not enough started members" reach clients as `codes.Unknown`

`toGRPCErrorMap` (`server/etcdserver/api/v3rpc/util.go:35-97`) maps every server error to a gRPC
status error (`rpctypes.ErrGRPC*`) except two, which it maps to the client-side `EtcdError`s:
`errors.ErrNotEnoughStartedMembers: rpctypes.ErrMemberNotEnoughStarted` (`util.go:42`) and
`errors.ErrTooManyRequests: rpctypes.ErrTooManyRequests` (`util.go:48`). An `EtcdError`
(`api/v3rpc/rpctypes/error.go:241-254`) has no `GRPCStatus()`, so grpc's `processRPC`
(`server.go:1461-1467`, grpc-go v1.84.0) finds no status in it and sends `codes.Unknown` with the
description as message, where `ErrGRPCMemberNotEnoughStarted` (`FailedPrecondition`) and
`ErrGRPCRequestTooManyRequests` (`ResourceExhausted`) were meant. The server returns
`ErrTooManyRequests` when the applied index lags the committed one too far
(`processInternalRaftRequestOnce`), so the request path reaches it.

etcd's Go client is unaffected: `rpctypes.Error` looks the description up in `errStringToError` and
rebuilds the `EtcdError` with the right code, and the retry interceptor retries neither code. What
sees `Unknown` is everything that reads the wire code: non-Go clients, the gRPC gateway's HTTP status
(500 instead of 429), and the `grpc_code` label of the server's prometheus metrics.

**Why not an issue:** the test (`notes/axiom-review/hs6/code_test.go.txt`, `TestWireCode`) returns
the two values from a plain grpc handler rather than through etcd's `togRPCError`; upstream not
searched (no GitHub access from the review's session).

## Proof

no: a status code on the wire; the proofs' specs of `togRPCError` and the handlers say nothing of
codes, and `statusErrOk` holds of an `EtcdError` (a leaf whose `Error()` returns).

## Notes

Found by the HS-6 axiom review (`notes/axiom-review/hs6.md`, statement 3). The fix is to map the two
keys to `rpctypes.ErrGRPCMemberNotEnoughStarted` and `rpctypes.ErrGRPCRequestTooManyRequests`. Test
output:

```
server returns rpctypes.EtcdError "etcdserver: too many requests" (Code() Unknown): client sees code Unknown desc "etcdserver: too many requests"
server returns rpctypes.EtcdError "etcdserver: re-configuration failed due to not enough started members" (Code() Unknown): client sees code Unknown desc "etcdserver: re-configuration failed due to not enough started members"
server returns *status.Error "rpc error: code = ResourceExhausted desc = etcdserver: too many requests" (Code() ResourceExhausted): client sees code ResourceExhausted desc "etcdserver: too many requests"
```
