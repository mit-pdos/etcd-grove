---
upstream: none
checked: 2026-11-01
links:
  - etcd-io/etcd#10907 pr merged: related, not this bug (added RoleAdd's empty-name check, the only name check besides UserAdd's; no length bound)
blocks-proof: yes
---

# auth: adding a user or role with a name longer than 32768 bytes makes every member exit

`etcdctl user add` or `role add` with a name longer than 32768 bytes is committed, and every
member exits while applying it (`failed to write to a bucket ... key too large`). After a restart
every member replays the entry and exits again, so the cluster stays down.

**Expected:** adding a user or role whose name is too long should fail with an error, as an empty
name does, and the members should keep running.

**Impact:** any cluster, default configuration: with auth disabled (the default) any client can
send the request; with auth enabled, only `root`. The whole cluster goes down and cannot restart
without a fixed binary. Reproduced on `main` with binaries (three members, `etcdctl role add` of a
32769-byte name; 32768 bytes succeeds).

**Reproduction:** `TestRoleAddLongName` and `TestUserAddLongName` in
[`issues/etcd-auth-useradd-long-name-fatal/long_name_test.go`](etcd-auth-useradd-long-name-fatal/long_name_test.go),
copied into `tests/common` at etcd-io/etcd@1573d5941 (2026-10-28), go1.27.3 linux/amd64 (the
member's fatal exit takes the test binary down):

```
$ go test -tags integration ./common/ -run '^TestRoleAddLongName$' -count=1 -v
    logger.go:146: 2026-11-01T04:09:38.589Z	FATAL	m0	failed to write to a bucket	{"member": "m0", "bucket-name": "authRoles", "error": "key too large"}
FAIL	go.etcd.io/etcd/tests/v3/common	0.232s
$ go test -tags integration ./common/ -run '^TestUserAddLongName$' -count=1 -v
    logger.go:146: 2026-11-01T04:09:41.113Z	FATAL	m0	failed to write to a bucket	{"member": "m0", "bucket-name": "authUsers", "error": "key too large"}
FAIL	go.etcd.io/etcd/tests/v3/common	0.237s
```

**Cause:** [`UserAdd`](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/server/auth/store.go#L423-L426)
and [`RoleAdd`](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/server/auth/store.go#L764-L767)
check only that the name is not empty, then store it as a bbolt key; bbolt rejects keys over
`MaxKeySize` (32768 bytes), and the backend treats any
[failed write](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/server/storage/backend/batch_tx.go#L183-L189)
as fatal. Nothing on the request path bounds the name below the request size limit (1.5 MiB).

## Proof

yes: the auth store's contract (`Proof/go_etcd_io/etcd/server/v3/etcdserver/apply/Contracts.lean`)
says `UserAdd`/`RoleAdd` return for any request, false here; the proof bounds the names by
`maxKeySize` in the workload clause (`rqOk`, `apply/InvRequest.lean`), a premise on clients that
etcd does not enforce.

## Fix

**Branch**: `fix/etcd-auth-useradd-long-name-fatal` in `~/etcd-fixes/etcd-auth-useradd-long-name-fatal` (upamanyus/etcd, not pushed): 5a3373080 test, 612320b8e fix
**Base**: etcd-io/etcd@3aaab3479b6c4f5fe1b2b8f33437093c2caae88a

**PR draft**:

Title: server/auth: reject user and role names longer than the max key size

[`UserAdd`](https://github.com/etcd-io/etcd/blob/3aaab3479b6c4f5fe1b2b8f33437093c2caae88a/server/auth/store.go#L423-L426) and [`RoleAdd`](https://github.com/etcd-io/etcd/blob/3aaab3479b6c4f5fe1b2b8f33437093c2caae88a/server/auth/store.go#L764-L767) check only that the name is not empty, then store it as a bbolt key. bbolt rejects keys longer than `MaxKeySize` (32768 bytes), and the backend treats any [failed write](https://github.com/etcd-io/etcd/blob/3aaab3479b6c4f5fe1b2b8f33437093c2caae88a/server/storage/backend/batch_tx.go#L183-L189) as fatal, so every member exits applying the request. This PR returns an error for such names next to the empty-name check, which also applies an entry already in the log as an error.

The first commit adds a test of the issue's example, which fails on `main`; the second, the fix, makes it pass.

A reviewer may ask why at apply time and not before proposing: the empty-name check is there, and
only an apply-time check lets a cluster whose log already holds such an entry restart (checked: the
crashed data directories restart healthy with the fixed `etcd`). The new errors are not mapped to
gRPC codes (clients get `Unknown` with `auth: role name is too long`); mapping them like
`ErrUserEmpty` is a few lines more if asked. The branch's tests are cases added to `TestRoleAdd_Error`
and `TestUserAdd_Simple` in `tests/common`.

## Notes

INDEX-reviewed.md's plan: upstream (the fix is easy to audit). Not a security report (clients are
trusted; with auth on only `root` can add users or roles). The same failure for a record grown
past bbolt's value limit by many grants is `nonissues/etcd-auth-record-too-large-fatal.md`.
