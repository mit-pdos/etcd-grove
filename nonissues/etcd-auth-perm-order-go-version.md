---
upstream: none
checked: 2026-11-27
links:
  - etcd-io/etcd#21845 pr open: related (upstream's same-key re-grant, `issues/etcd-auth-grant-permission-same-key.md`), which makes the second outcome below a difference of permission sets, not only of order
blocks-proof: yes
---

# auth: members built with different Go versions store a role's permissions in different orders, and then disagree on the same committed request

`RoleGrantPermission` sorts a role's permissions by key alone with `sort.Sort`, which is not
stable. Go 1.19 replaced `sort.Sort`'s algorithm (pdqsort), so a member built with Go ≤ 1.18 and one
built with Go ≥ 1.19, applying the same grant to the same record, can store the permissions that
share a key in different orders. The range-permission cache's interval tree is built in record
order, and its `Contains` answer for an inverted range (`key > range_end`) depends on the tree's
shape. A write `Txn` that also reads an inverted range can therefore be refused on one member and
applied on the other, and the members' KV stores diverge. With upstream's `RoleGrantPermission`
the members can also end up with different permission *sets*: its duplicate check finds an
existing entry only when it sorts first among its key, and then a plain put to a key is refused on
one member and applied on the other.

**Why not an issue:** no test runs two etcd binaries. The divergence needs members built with Go ≤
1.18 and Go ≥ 1.19 to apply the same `RoleGrantPermission` entries. That happens in a rolling upgrade
across v3.5.7 (binaries compiled with Go 1.17.13) and v3.5.9 (Go 1.19.9), per the pinned tree's
`CHANGELOG/CHANGELOG-3.5.md:465-522`. It also needs a role holding several permissions with the same
start key and different range ends. The measured part covers two steps. First, the sort's output
under the four toolchains (`sortcmp/`, `sorttyped/`: go1.17.13 ≡ go1.18.10, go1.19.9 ≡ go1.27.3, and
the two groups differ on most grant sequences of 13 to 22 grants: 219 of 300 with the fork's grant,
253 of 300 with upstream's). Second, the verdicts of two auth stores whose backends hold the two
records, written directly (`permorder_test.go`, copied into `server/etcdserver/apply` at the fork
pin `8c28a4296`; `range_perm_cache.go`, `apply/auth.go` and `pkg/adt/interval_tree.go` are
identical at upstream `4e090c033abc`), go1.27.3:

```
$ go test ./etcdserver/apply -run TestPermOrder -count=1 -v
    permorder_test.go:83: Txn{range [d,a); put a}: go1.17 member auth: permission denied, go1.19 member <nil>
--- FAIL: TestPermOrderInvertedRangeTxn (0.01s)
    permorder_test.go:98: Txn{put c}: go1.17 member <nil>, go1.19 member auth: permission denied
--- FAIL: TestPermOrderPutUpstream (0.01s)
```

Under one toolchain the stored order is a function of the prior record and the entry. pdqsort's
pattern breaking is a xorshift seeded by the slice's length (`sort/zsortinterface.go:240-244`,
`sort.go:67-80`). Every member starts from the same record: a restart reads it from the backend, and
a snapshot install takes the leader's backend. Nothing else re-sorts a record: `RoleRevokePermission`
keeps the order, and no migration touches roles. So a cluster that has only ever run one Go version
does not diverge. Once a mixed-version window has produced different records, they stay different
after the upgrade, until a member installs a snapshot.

**How:** `RoleGrantPermission` appends and calls `sort.Sort(permSlice(...))`, and `permSlice.Less`
compares `Key` only (`server/auth/store.go:799-845`). `getMergedPerms` inserts the record's
permissions into the tree in record order (`server/auth/range_perm_cache.go:25-70`). For a range,
`checkKeyInterval` asks `IntervalTree.Contains` (`:79-95`, `pkg/adt/interval_tree.go:743-764`), which
folds over the nodes `Visit` reaches. For an inverted query interval those nodes depend on the shape
(`checkTxnPermission`, `checkTxnReqsPermission`, `server/etcdserver/apply/auth.go:128-189`; `checkRangeRequest` does not
refuse `key > range_end`).

## Proof

yes: the permission check of a range is a function of the auth model's state only if the stored
record's order is determined by it. The model keeps a role's permissions up to order (`roleOut`,
`roleGrantPermissionR` in `Proof/go_etcd_io/etcd/server/v3/auth/Steps.lean`), and the mode-`on` log
asks that every KV request be of the shape the cache decides (`kvShapeAll`, `auth.reqShape` in
`Proof/go_etcd_io/etcd/server/v3/auth/Model.lean:175-181`: no inverted range). Retiring that premise
needs a canonical record. The fix: `permSlice.Less` compares `(Key, RangeEnd)`. With the fork's grant,
which keeps one permission per range, the record is then the model's sorted list under every Go
version. The pinned fork does not carry that fix yet.

## Notes

Not searched upstream (no GitHub search in this session); `upstream: none` until it is. Auth-related:
recorded only. With KV corruption checks enabled, the members' hash check would report the
divergence after the fact [inferred, not tested]. Tests in `etcd-auth-perm-order-go-version/`:
`permorder_test.go` (the verdicts), `sortcmp/` (the sort under several toolchains,
`GOTOOLCHAIN=go1.17.13 go run main.go`; the fork's and upstream's grant; seq 4 is the first test's
records) and `sorttyped/` (upstream's grant with types; seq 0 is the second test's records).
