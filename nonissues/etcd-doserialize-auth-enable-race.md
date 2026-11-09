---
upstream: none
checked: 2026-11-09
links:
  - etcd-io/etcd#21909 pr open: related, not this bug (the auth revision check for verify-only JWT providers)
blocks-proof: yes
---

# etcdserver: a read that starts while auth is disabled can return a key written after auth was enabled, to a client with no permission

`EtcdServer.doSerialize` (`Range`, a read-only `Txn`, `RangeStream`) checks the request's
permission, then reads, then re-checks the auth revision only if the request carried one
([`server/etcdserver/v3_server.go`](https://github.com/etcd-io/etcd/blob/main/server/etcdserver/v3_server.go),
`doSerialize`: `if ai.Revision != 0 && ...`). With auth disabled at the check, `AuthInfoFromCtx`
returns no credentials (`server/auth/store.go`, `AuthInfoFromCtx`: `if !as.IsAuthEnabled() { return
nil, nil }`), the check passes and the revision check is skipped. If `AuthEnable` and then a write
of a protected key apply between the check and the read, an unauthenticated client reads that key,
which with auth on it may not read.

**Why not an issue:** no test; found by code reading (the client model's provability review,
2026-11-09); the window (between the permission check and the read, both on the same member) is
narrow, and auth being enabled while clients read is an administrative transition. A test could
promote it: a failpoint (or a sleep injected in `doSerialize` after `chk`), an unauthenticated
`Get` of a key, then `AuthEnable` and a root `Put` of that key during the pause.

## Proof

yes: the client's model (`Spec/go_etcd_io/etcd/api/v3/Model.lean`, `kvStep`'s linearizable range)
checks a read's permission at the state the read answers from, which this interleaving violates;
the cluster contract's K4 is false there. The proof needs a fix on the fork (re-check the
permission, or the auth revision, after the read whenever auth is enabled at the end of it) or a
scope premise (no `AuthEnable` while reads are in flight), recorded in `notes/specs-only/top.md`,
K8.

## Notes

Fix, if wanted: record whether auth was enabled at the check and fail the read with
`ErrAuthOldRevision` when `s.authStore.Revision()` changed during it, whether or not the request
carried credentials.
