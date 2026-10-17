---
upstream: unchecked
---

# `Client.Dial` reads the client's endpoints without `epMu`

**Status**: a bug (a data race), found while reviewing `clientv3.newClient` for etcd-io/etcd#21714.

**Where**: `client/v3/client.go` at the pinned revision (fork `goose-lean` 09669450f): `dial`
builds its target from `authority(c.endpoints[0])` (line 327) without holding `c.epMu`;
`SetEndpoints` (177-182) writes `c.endpoints` under `c.epMu`. `dial` is reached from the exported
`Client.Dial(ep)` (277) at any time, while `SetEndpoints` is exported and also called by `autoSync`'s
`Sync` in the client's own goroutine (`AutoSyncInterval`). (`newClient`'s own `dialWithBalancer`
runs before `autoSync` starts and before the client is returned, so it does not race.)

**What happens**: `go test -race` reports a race between `SetEndpoints` (write, client.go:180)
and `dial` (read, client.go:327): `notes/pr-verify/etcd-21714/review_dial_race_test.go` (package
`clientv3`, 100 `Dial`s against 100 `SetEndpoints`), log `review_dial_race_test.log`, at the PR
head 73e843991:

```
cp notes/pr-verify/etcd-21714/review_dial_race_test.go <etcd>/client/v3/
cd <etcd>/client/v3 && go test -race -run TestReviewDialSetEndpointsRace -v .
```

**Expected**: `endpoints` is documented by its lock (`epMu` protects it: `Endpoints()` reads it
under `RLock`); `dial` should read it the same way (`c.Endpoints()[0]`, or pass the endpoint in).

**How the proof handles it**: `newClient.spec` (branch `pr-verify/etcd-21714`) gives the
`endpoints` field away to `SetEndpoints` (the field is the mutex's from then on, not modeled), and
the dial's contract (`Client.dialWithBalancer`, an axiom) does not take it; `Client.Dial` is not
specified.

**Possible fixes**: in `dial`, take the endpoint from `c.Endpoints()` (which copies under the read
lock), or have callers pass the target endpoint.

**Found**: 2026-10-17, by the reviewer of the etcd-io/etcd#21714 verification.
