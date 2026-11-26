---
upstream: none
checked: 2026-11-26
links:
  - etcd-io/etcd#12385 issue closed: related, not this bug (a watch stream refused once its token expired)
blocks-proof: no
---

# auth: a member that has not yet applied AuthEnable accepts an unauthenticated watch, which then streams keys written after auth was enabled

A member that is behind the cluster (cut off by a partition, or restarting) when auth is enabled
keeps accepting watches from clients without credentials until it applies the `AuthEnable`. Such a
watch is not canceled when the member catches up: it goes on to deliver every key written after auth
was enabled, including keys only root may read, to the unauthenticated client.

**Expected:** once auth is enabled, a client without credentials should not receive keys written
after the enable, as a `Get` or a new `Watch` through an up-to-date member refuses it
(`etcdserver: user name is empty`); a watch the member accepted before it applied the enable should
be canceled when it applies it, or its events checked.

**Impact:** clusters that enable auth while running (`etcdctl auth enable`), with a member that is
partitioned, slow or restarting at that moment, and a client able to reach that member without
credentials. The window is from the enable until that member applies it; the watch it accepts stays
open afterwards. Reproduced on `main` with the integration framework (three members, one partitioned).
Measured also without a partition (`notes/axiom-review/watchon-dist/`, a follower stopped across
`AuthEnable` and restarted, caught up by a snapshot): 2 of 13,556 anonymous watch creates sent
around its restart were accepted, and one delivered 61 events, 60 of them written after the enable.

**Reproduction:** `TestWatchAuthLaggingMember` in
[`issues/etcd-watch-auth-lagging-member/watch_auth_lagging_member_test.go`](etcd-watch-auth-lagging-member/watch_auth_lagging_member_test.go),
run against `tests/framework/integration` at etcd-io/etcd@4e090c033 (`main`, 2026-11-24; a module
requiring `go.etcd.io/etcd/{api,client/pkg,client,pkg,server,tests}/v3` at that commit; the file is
`package integration` and can be copied into `tests/integration`), go1.27.3 linux/amd64; it fails on
every run (5 of 5):

```
$ go test -run '^TestWatchAuthLaggingMember$' -count=1 -v .
    watch_auth_lagging_member_test.go:85: at the leader: anonymous watch refused: rpc error: code = InvalidArgument desc = etcdserver: user name is empty
    watch_auth_lagging_member_test.go:99: at the cut-off follower: anonymous watch accepted, first response 1 event(s)
    watch_auth_lagging_member_test.go:118: a watch without credentials received 10 keys written after AuthEnable: [c/after0 c/after1 c/after2 c/after3 c/after4 c/after5 c/after6 c/after7 c/after8 c/after9]
--- FAIL: TestWatchAuthLaggingMember (0.28s)
```

**Cause:** the watch server checks a create request once, against the receiving member's own auth
store ([`isWatchPermitted`](https://github.com/etcd-io/etcd/blob/4e090c033abc29636df2f844fbdd363adffcd90b/server/etcdserver/api/v3rpc/watch.go#L237-L247),
called at [`watch.go:287`](https://github.com/etcd-io/etcd/blob/4e090c033abc29636df2f844fbdd363adffcd90b/server/etcdserver/api/v3rpc/watch.go#L287)),
where [`isOpPermitted`](https://github.com/etcd-io/etcd/blob/4e090c033abc29636df2f844fbdd363adffcd90b/server/auth/store.go#L859-L863) passes
every request while that store has auth disabled. The watcher is then registered with mvcc
([`watch.go:340`](https://github.com/etcd-io/etcd/blob/4e090c033abc29636df2f844fbdd363adffcd90b/server/etcdserver/api/v3rpc/watch.go#L340)),
and nothing rechecks it or cancels it when the member later applies `AuthEnable` (or a revocation),
so it receives every later event of its range.

## Proof

no: the cross-machine watch contract with auth on (`WatchOn_dist`,
`Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/WatchOnDist.lean`) requires a floor at every
endpoint's serving member (`watchFloorsD`: the member has applied the auth set-up), which the auth
workload's per-member barriers give (`examples/etcd/dist/client/auth.go`, `barriers`) before any
principal watches; so no create the workload sends is checked at a pre-enable state.

## Fix

No branch. Either cancel (or recheck) a stream's watchers when the member's auth store changes
(`AuthEnable`, and the revocations, which have the same shape for a watch accepted before them), or
filter events per watcher against the current auth state.

## Notes

Not filed upstream: Upamanyu decides. A related shape, from reading the same code and not tested
here: a watch accepted on an up-to-date member while auth was still off would also keep streaming
after `AuthEnable`. This file's case differs: the create is sent after `AuthEnable` has committed.
