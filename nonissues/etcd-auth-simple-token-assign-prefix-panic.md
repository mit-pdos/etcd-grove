---
upstream: none
checked: 2026-11-02
links:
  - etcd-io/etcd#13682 pr merged: related, not this bug (oss-fuzz 44478): made the `AuthenticateParamIndex` assertion in `tokenSimple.assign` checked, leaving the `AuthenticateParamSimpleTokenPrefix` one on the next line unchecked
blocks-proof: no
---

# auth: the simple token provider's `assign` panics on a context with the index but no token prefix

With the simple token provider and auth enabled, `AuthStore.Authenticate` on a context that carries
`AuthenticateParamIndex` but not `AuthenticateParamSimpleTokenPrefix` panics (`interface
conversion: interface {} is nil, not string`) in `tokenSimple.assign`, whose index assertion is
checked (an error when absent) but whose prefix assertion on the next line is not.

**Why not an issue:** a precondition etcd meets: its two callers of `Authenticate` (the apply
layer, `apply/backend.go`, and `WithRoot`) always set both values; no test, found by code reading.

## Proof

no: the token provider is a contract (`tokenProviderOk`,
`Proof/go_etcd_io/etcd/server/v3/auth/InvAuth.lean`); a proof of the simple provider would take
the two context values as a premise, which etcd's callers meet.

## Notes

A test (in `server/auth`: `setupAuthStore`, then `Authenticate` on such a context) would show the
panic, but by calling `Authenticate` in a way no etcd caller does. The fix would be the checked
form, as #13682 did for the index.
