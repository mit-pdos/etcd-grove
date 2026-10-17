---
upstream: known
checked: 2026-10-17
links:
  - etcd-io/etcd#21595 pr open: the fix (get returns its error, doSerialize returns it before the stale-token check)
  - etcd-io/etcd#10552 pr closed: the same fix, 2019, closed as stale
---

# A serialized read's error is replaced by `ErrAuthOldRevision` when an auth change commits during the read

**Status**: a bug (a wrong error). Not a safety problem: either way the request fails.

**Where**: `server/etcdserver/v3_server.go` at the pinned etcd revision (`09669450f`):
`doSerialize` (line 1035) calls `get()` (line 1050), which has no result, then compares the
token's revision with the auth store's (line 1053). `Range` (line 149), `RangeStream` (line 187)
and the read-only branch of `Txn` (line 365) keep the read's error in a captured variable.

**What happens**: with auth enabled and a token, a read whose fetch fails (`mvcc.ErrCompacted`
for a compacted revision, `mvcc.ErrFutureRev`, a context error from `txn.Txn`) while any auth
change (user, role, permission) commits gets `auth: revision in header is old` instead of the
read's error. The client is told to re-authenticate and retry, and the retry hits the original
error. Reproduction: `notes/pr-verify/etcd-21595/base/doserialize_compacted_test.go` (on the
`pr-verify/etcd-21595` branch), against the pinned revision:
`cp doserialize_compacted_test.go server/etcdserver/ && cd server && go test -run TestDoSerializeCompacted ./etcdserver/`
fails with `doSerialize returned auth: revision in header is old (get's error: mvcc: required
revision has been compacted)`.

**Expected**: the read's error. `doSerialize`'s comment says it returns an error "on
authentication failure"; the read did not fail authentication, its token was valid when checked.

**How the proof handles it**: on `lean`, `EtcdServer.doSerialize.spec`
(`Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__doSerialize.lean`) allows it: its failure
case is any error the gRPC layer can take, after `get` ran or not. `Range`'s and `Txn`'s specs
only say a failure is such an error, so they do not see which one.

**Possible fixes**: etcd-io/etcd#21595 (verified on `pr-verify/etcd-21595`,
`notes/pr-verify/etcd-21595.md`): `get` returns an error, which `doSerialize` returns before the
stale-token check.

**Found**: 2026-10-17, verifying etcd-io/etcd#21595 (its description states the race; the test
above confirms it on the pinned code).
