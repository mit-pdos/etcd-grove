---
upstream: none
checked: 2026-11-02
links:
  - etcd-io/etcd#21909 pr open: related, not this bug (skips the auth revision check for verify-only JWT providers; does not touch `doSerialize`'s check with auth disabled or the TLS common-name path)
blocks-proof: no
---

# auth: a serializable read can fail with "revision of auth store is old" while auth is disabled

On a server started with `--client-cert-auth` and auth disabled, a client whose certificate has a
common name gets `etcdserver: revision of auth store is old` for a serializable `Range` when an
auth-store write (a `UserAdd`, permitted with auth off) commits during the read. `AuthInfoFromCtx`
falls back to
[`AuthInfoFromTLS`](https://github.com/etcd-io/etcd/blob/a2e3642bcd2cca3a802503cdb09f64a3dc15cdf5/server/etcdserver/v3_server.go#L1207-L1217)
whether auth is enabled or not, which records the store's revision
([store.go#L1024-L1027](https://github.com/etcd-io/etcd/blob/a2e3642bcd2cca3a802503cdb09f64a3dc15cdf5/server/auth/store.go#L1024-L1027)),
and [`doSerialize`](https://github.com/etcd-io/etcd/blob/a2e3642bcd2cca3a802503cdb09f64a3dc15cdf5/server/etcdserver/v3_server.go#L1050-L1057)
compares it after the read without checking that auth is enabled (unlike `isOpPermitted`). The
client has no token, so its retry interceptor does not refresh one; the error reaches the caller.

**Why not an issue:** no test; found by code reading (the spec review of F-S2 part 2's design,
2026-10-30). A test could promote it: an integration cluster with client-cert auth and auth
disabled, a serializable `Get` from a client with a CN certificate, and a `UserAdd` committed
during it (a sleep after the read widens the window).

## Proof

no: the verified server has no TLS (`Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/Server.lean`),
etcd's default configuration, so `AuthInfoFromTLS` is never reached; the axiom that no auth refusal
happens with auth off stays true of that model. Stating it as a theorem of etcd would need a
no-client-cert-auth premise (`notes/auth-mode-merge-plan.md`, F-S2 part 2, parked).

## Notes

Fix, if wanted: skip the revision check in `doSerialize` when auth is disabled, or have
`AuthInfoFromTLS` return revision 0 then.
