---
upstream: none
checked: 2026-11-02
links: []
blocks-proof: no
---

# auth: `AuthInfoFromCtx` panics on a token key with no value in the incoming metadata

`authStore.AuthInfoFromCtx` looks up `md["token"]` (then `md["authorization"]`) and indexes
`ts[0]` without checking that the list is non-empty, so a context built with
`metadata.NewIncomingContext(ctx, metadata.MD{"token": {}})` panics (index out of range) on an
auth-enabled store.

**Why not an issue:** a precondition etcd meets: gRPC's transports never put a key with no value
in a request's metadata; only an in-process caller building its own context can.

## Proof

no: the axiom of `metadata.FromIncomingContext`
(`Spec/google_golang_org/grpc/metadata/FromIncomingContext.lean`) states that every value list is
non-empty, true of gRPC's transports.

## Notes

The test,
[`nonissues/etcd-auth-token-md-empty/authinfo_ctx_empty_token_test.go`](etcd-auth-token-md-empty/authinfo_ctx_empty_token_test.go)
(`server/auth`), fails at etcd-io/etcd@1573d5941 (go1.27.3): `index out of range [0] with
length 0`. The 2026-10-23 review's plan: skip for now. A fix would be `if !ok || len(ts) == 0`.
