---
upstream: none
checked: 2026-11-09
links:
  - nonissues/etcd-doserialize-auth-enable-race.md: same family (a check made while auth is disabled, applied after `AuthEnable`)
blocks-proof: no
---

# etcdserver: a write proposed while auth is disabled and applied after AuthEnable is checked as the TLS certificate's user, not the token's

`EtcdServer.AuthInfoFromCtx`
([`server/etcdserver/v3_server.go`](https://github.com/etcd-io/etcd/blob/main/server/etcdserver/v3_server.go))
returns the token's user only while auth is enabled (`auth/store.go`, `AuthInfoFromCtx`: `nil` when
auth is disabled); otherwise, with `--client-cert-auth`, the TLS certificate's common name
(`AuthInfoFromTLS`). `processInternalRaftRequestOnce` writes that user and its auth revision into the
request's header. A request carrying a token of user `A` over a connection whose certificate names
`B`, proposed while auth is disabled, has `B` in its header; if `AuthEnable` (which keeps the auth
revision: `auth/store.go`, `AuthEnable`) commits before the request's entry, the apply's revision
check passes and the request is checked and applied as `B`, not as the token's `A`.

**Why not an issue:** no test, found by code reading (2c's provability review, round 1, F7); it needs a
client presenting a token and a certificate of different users, and `AuthEnable` racing its write.

## Proof

no: the spec states it (`EtcdServer.srvStep p tls`: a write may be stepped as the certificate's
principal `tls`, `ApiReq.lean`); a client whose token and certificate name the same user (or with no
certificate under `--client-cert-auth`: a principal-less write is refused) sees one principal
(W0's `ctxPrin`, `req/go_etcd_io_etcd_api_v3.md`, "from 2c").

## Notes

Fix, if wanted: no TLS fallback in `AuthInfoFromCtx` while a token is present, or record in the header
whether auth was enabled at the check and refuse the entry at the apply when it no longer matches.
