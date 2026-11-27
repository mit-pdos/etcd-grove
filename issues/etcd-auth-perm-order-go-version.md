---
upstream: none
checked: 2026-11-27
links:
  - etcd-io/etcd#21845 pr open: related (upstream's same-key re-grant, `issues/etcd-auth-grant-permission-same-key.md`), which makes the outcome below a difference of permission sets, not only of order
blocks-proof: yes
---

# auth: in a cluster mixing etcd v3.5.7 and v3.5.9, the same role grants leave different permissions on the members, and a put is applied on one member and refused on the other

In a two-member cluster with one v3.5.7 member and one v3.5.9 member, as during a rolling upgrade,
granting the same sequence of key permissions to a role leaves the two members with different
permission lists for that role. A user with the role then sends `put c`: the v3.5.7 member applies
it and the v3.5.9 member refuses it, so the members' key-value stores diverge (revision 3 with `c`
on one, revision 1 without `c` on the other), and a read returns different data depending on the
member that serves it.

**Expected:** every member should reach the same state from the same committed entries: etcd's
replicated state machine applies the same requests in the same order on every member, and
[rolling upgrades](https://etcd.io/docs/v3.5/upgrades/upgrade_3_5/) run mixed-version clusters.

**Impact:** clusters with auth enabled, during a rolling upgrade whose old and new binaries were
built with Go ≤ 1.18 and Go ≥ 1.19 (official binaries: v3.5.0 to v3.5.7 and v3.4.x up to v3.4.24 on
one side, v3.5.9 (Go 1.19.9) and later and v3.4.25 (Go 1.19.8) and later on the other, per
`CHANGELOG/CHANGELOG-3.5.md` and `CHANGELOG-3.4.md`), when a role is granted several permissions
with the same start key and different range ends during the mixed window. The members' records
stay different after the upgrade completes, until a member installs a snapshot; every later write
the differing permissions decide can diverge. Clusters that only ever ran one Go major version are
not affected. Default configuration otherwise (corruption checks are off by default).

**Reproduction:** [`issues/etcd-auth-perm-order-go-version/repro-mixed-binaries.sh`](etcd-auth-perm-order-go-version/repro-mixed-binaries.sh)
with the official release binaries (`etcd-v3.5.7-linux-amd64.tar.gz`, sha256 `a43119af…bc396`;
`etcd-v3.5.9-linux-amd64.tar.gz`, sha256 `d5901704…8b042`; both checked against the releases'
`SHA256SUMS`; `etcd --version`: 3.5.7 Go 1.17.13, 3.5.9 Go 1.19.9), etcdctl v3.5.9, 2026-11-27. It
starts member m1 on v3.5.7 and m2 on v3.5.9, creates `root`, user `u` with role `r`, enables auth,
grants `r` (as root) the 21 permissions `[f,g)RW [b,e)R [a,c)R [b,c)R [c,d)R [d,e)R [f,h)RW [e,f)RW
[a,d)RW [d,f)R [b,e)RW [f,i)RW [b,d)R [b,e)R [c,f)R [a,d)R [a,d)R [f,i)R [b,d)R [a,c)RW [b,e)R`, then
as `u` puts `c` through each member, and compares the members (full output in
[`repro-mixed-binaries.log`](etcd-auth-perm-order-go-version/repro-mixed-binaries.log)):

```
$ etcdctl --endpoints=<m1> --user=root:rootpw role get r     # v3.5.7      (m2, v3.5.9:)
KV Write:                                                     KV Write:
	[a, c)                                                    	[a, c)
	[a, d)                                                    	[e, f) (prefix e)
	[e, f) (prefix e)                                         	[f, g) (prefix f)
	[f, g) (prefix f)                                         	[f, h)
	[f, h)                                                    	[f, i)
	[f, i)
$ etcdctl --endpoints=<m1> --user=u:upw put c via-m1
OK
$ etcdctl --endpoints=<m2> --user=u:upw put c via-m2
Error: etcdserver: permission denied
$ etcdctl --endpoints=<m1>,<m2> --user=root:rootpw endpoint hashkv -w table
| http://127.0.0.1:23791 | 2297620300 |
| http://127.0.0.1:23792 | 1084519789 |
$ etcdctl --endpoints=<m1> --user=root:rootpw get c --consistency=s -w json
{"header":{...,"revision":3,...},"kvs":[{"key":"Yw==","create_revision":2,"mod_revision":3,"version":2,"value":"dmlhLW0y"}],"count":1}
$ etcdctl --endpoints=<m2> --user=root:rootpw get c --consistency=s -w json
{"header":{...,"revision":1,...}}
```

m1 applied both puts (including the one m2 answered with "permission denied"); m2 applied neither.
Linearizable reads (`--consistency=l`) return the same split.

**Cause:** `RoleGrantPermission` looks for an existing permission with `sort.Search` on the key and
updates it only if the first entry with that key has the same range end; otherwise it appends and
calls `sort.Sort(permSlice(...))`, whose `Less` compares `Key` only
([`server/auth/store.go`](https://github.com/etcd-io/etcd/blob/v3.5.9/server/auth/store.go#L777-L825),
the same at v3.5.7 except v3.5.9's range validity check). `sort.Sort` is not stable, and Go 1.19
replaced its algorithm (pdqsort), so binaries built with Go ≤ 1.18 and Go ≥ 1.19 order permissions
that share a key differently. The duplicate check then finds an existing `[a,d)` on one member and
not on the other: m1 ends with three `[a,d)` entries, one of them read-write (the later read-only
re-grants were appended as new entries), m2 with one `[a,d)` entry, read-only (a later re-grant
found the read-write one and overwrote its type). The role's permission *sets* differ: write
access to `[a,d)` on m1, none on m2. Each member checks the put against its own record when it
applies the entry (`authApplierV3.Put`), so the members disagree.

## Proof

yes: the permission check of a range is a function of the auth model's state only if the stored
record's order is determined by it. The model keeps a role's permissions up to order (`roleOut`,
`roleGrantPermissionR` in `Proof/go_etcd_io/etcd/server/v3/auth/Steps.lean`), and the mode-`on` log
asks that every KV request be of the shape the cache decides (`kvShapeAll`, `auth.reqShape` in
`Proof/go_etcd_io/etcd/server/v3/auth/Model.lean:175-181`: no inverted range). Retiring that premise
needs a canonical record. The fix: `permSlice.Less` compares `(Key, RangeEnd)`. With the fork's grant,
which keeps one permission per range, the record is then the model's sorted list under every Go
version. The pinned fork does not carry that fix yet.

## Fix

`permSlice.Less` compares `(Key, RangeEnd)`, so the sorted record is the same under every sort
algorithm, together with a duplicate check that finds an existing `(Key, RangeEnd)` wherever it is
(etcd-io/etcd#21845's direction). Records already written by a mixed window stay different; a fix
cannot repair them without a migration.

## Notes

Auth-related: recorded only, not filed upstream, and not searched upstream (no GitHub search in this
session). With upstream's grant and same-key permissions of one set in different orders (the fork's
grant), the members also disagree on a write `Txn` that reads an inverted range (`key > range_end`):
the range-permission cache's interval tree is built in record order and its `Contains` answer for
an inverted query depends on the tree's shape (`server/auth/range_perm_cache.go:25-95`,
`pkg/adt/interval_tree.go:743-764`, `server/etcdserver/apply/auth.go:128-189`); measured only at the
library level (`permorder_test.go`, `TestPermOrderInvertedRangeTxn`). Under one toolchain the stored
order is a function of the prior record and the entry (pdqsort's pattern breaking is seeded by the
slice's length), and every member starts from the same record, so a single-Go-version cluster does
not diverge. With corruption checks enabled, the hash check would report the divergence after the
fact [inferred, not tested; `endpoint hashkv` above shows different hashes].

Other files in `etcd-auth-perm-order-go-version/`: `permorder_test.go` (two auth stores whose
backends hold the two records, copied into `server/etcdserver/apply` at the fork pin `8c28a4296`;
`range_perm_cache.go`, `apply/auth.go` and `pkg/adt/interval_tree.go` are identical at upstream
`4e090c033abc`; go1.27.3: both tests fail, the members disagree), `sortcmp/` (the sort under
go1.17.13, go1.18.10, go1.19.9, go1.27.3 with the fork's grant: go1.17 ≡ go1.18, go1.19 ≡ go1.27, the
groups differ on 219 of 300 sequences of 13 to 22 grants) and `sorttyped/` (upstream's grant with
types: 253 of 300; seq 0 is the reproduction's sequence, whose records the script's `role get`
outputs match).
