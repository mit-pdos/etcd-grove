---
upstream: none
checked: 2026-10-18
links: []
blocks-proof: no
---

# auth: `AuthInfoFromTLS` panics for a peer whose credentials are not TLS

`authStore.AuthInfoFromTLS` returns nil for a peer without auth info but asserts any other
`credentials.AuthInfo` to `credentials.TLSInfo` with the one-result form, so a peer with other
credentials (insecure, ALTS, local) panics. The `AuthStore` interface does not say it requires TLS.

**Why not an issue:** a precondition etcd meets: etcd's gRPC servers have TLS transport credentials
or none (then `peer.AuthInfo` is nil), and its HTTP handler transport sets a `credentials.TLSInfo`
only for a TLS request.

## Proof

no: the verified fork carries the checked assertion (`17c88a667`, `etc/goose.py`), and
the axiom `Spec/go_etcd_io/etcd/server/v3/auth/authStore__AuthInfoFromTLS.lean` takes any context;
at upstream's code a premise etcd meets (the peer's auth info is TLS or nil) would serve instead.

## Notes

The test,
[`nonissues/etcd-auth-tls-info-assert/authinfo_tls_test.go`](etcd-auth-tls-info-assert/authinfo_tls_test.go)
(`server/auth`), fails at etcd-io/etcd@1573d5941 (go1.27.3): `interface conversion:
credentials.AuthInfo is insecure.info, not credentials.TLSInfo`. INDEX-reviewed.md's plan:
non-issue.
