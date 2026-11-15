---
upstream: none
checked: 2026-11-09
links:
  - etcd-io/etcd#21909 pr open: related, not this bug (the auth revision check for verify-only JWT providers)
blocks-proof: no
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

no: the client's model covers it (round 4 of the specs-only W0 batch): a linearizable read's
permission is checked at some auth state the cluster had from the call's start on
(`SpecPlan/Spec/go_etcd_io/etcd/api/v3/Model.lean`, `State.permittedSince`, `State.deniedSince`, `Step`'s
`lo`; round 6 widened it to any auth state since the call's start, which also covers an auth change
whose revision is bumped before readers see it), so a read whose check saw auth off is answered whatever the auth state at the answer, as
etcd does. Clients see it: an unauthenticated read that started before `AuthEnable` may succeed.

## Notes

Fix, if wanted: re-check the permission after the read whenever auth is enabled by then (with the
request's credentials as they are, failing with the permission error or `ErrUserEmpty`). Comparing
the auth revision does not catch it: `AuthEnable` keeps the auth revision (`auth/store.go`,
`AuthEnable`: `setRevision` of the stored one) and a key write does not touch it.
