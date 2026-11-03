---
upstream: none
checked: 2026-10-20
links: []
blocks-proof: no
---

# auth: `NewAuthStore` with a nil token provider panics on a backend where auth is enabled

`NewAuthStore(lg, be, nil, cost)` reads the backend's auth-enabled flag and, when it is set, calls
the token provider's `enable()`: a nil-pointer panic. Its API does not say the provider must be
non-nil.

**Why not an issue:** a precondition etcd meets: `NewServer` passes `NewTokenProvider`'s result,
never nil on success; only tests pass nil, on fresh backends.

## Proof

no: `auth.NewAuthStore`'s contract takes the token provider's contract (`tokenProviderOk tp`,
which implies `tp ≠ nil`) as a premise, which `NewServer` meets.

## Notes

The test,
[`nonissues/etcd-auth-newauthstore-nil-tp/newauthstore_nil_tp_test.go`](etcd-auth-newauthstore-nil-tp/newauthstore_nil_tp_test.go)
(`server/auth`), fails at etcd-io/etcd@1573d5941 (go1.27.3): `NewAuthStore(nil tp) on an
auth-enabled backend panicked: runtime error: invalid memory address or nil pointer dereference`.
The 2026-10-23 review's plan: non-issue.
