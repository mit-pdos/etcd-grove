# etcd#22261: the files the report relies on

The report is `notes/pr-verify/etcd-22261.md`. Revisions: the PR head is `4f47eb361` (etcd-io/etcd
`pull/22261/head`); the fork branch is `mit-pdos/etcd-grove` branch `pr-etcd-22261-goose-lean`
(commit `22be0af01`: the PR, tests included, onto `goose-lean` `09669450f`); the old peer is
etcd-io/etcd `release-3.7`.

| File | What it shows | Runs against | Command |
|---|---|---|---|
| `peer_version_downgrade_test.go` | Finding 1: with a `v`-prefixed `Version`, after a peer is downgraded from 3.8 to 3.7 the member keeps its cached 3.8.0, keeps sending `v3.8.0`, and every stream dial and pipeline post to the peer fails (EOF); a member without the cached version reaches the same peer. The fake peer panics on a leading `v` exactly where release-3.7's handlers do (`checkClusterCompatibilityFromHeader` → `serverVersion` = `semver.Must(semver.NewVersion(...))` of coreos/go-semver). The test fails by design (`t.Errorf("BUG: ...")`). | the PR head (or the fork branch) | `cp peer_version_downgrade_test.go <checkout>/server/etcdserver/api/rafthttp/ && cd <checkout>/server && go test -run TestPeerVersionCacheStaleAfterDowngrade -v ./etcdserver/api/rafthttp/` |
| `peer_version_downgrade_test.log` | That test's output at the PR head (stack traces of the recovered handler panics removed). | the PR head | as above |
| `stale_cache_direction_test.go` (the reviewer's) | Which direction the stale cache of finding 1 breaks: `TestStaleCacheWhichDirectionBreaks` shows that our `streamHandler` answers a v3.7 peer's stream dial with the stripped version (it reads the request's header, not the cache), so the streams the peer dials into us keep working, while the cache stays at 3.8.0 and our own dials, pipeline posts and snapshots still send `"v3.8.0"`; `TestPrereleasePeer` prints `VersionForPeer`'s answer with `Version = "v3.8.0-rc.0"` for pre-release and neighbouring peer versions (pre-releases of 3.8.0 sort below v3.8: stripped). Both pass (they log, they do not assert the bug). | the PR head | `cp stale_cache_direction_test.go <checkout>/server/etcdserver/api/rafthttp/ && cd <checkout>/server && go test -run 'TestStaleCacheWhichDirectionBreaks|TestPrereleasePeer' -v ./etcdserver/api/rafthttp/` |
| `stale_cache_direction_test.log` | Its output at the PR head. | the PR head | as above |
| `coreosprobe/` (`main.go`, `go.mod`, `go.sum`, `output.log`) | coreos/go-semver v0.3.1 (release-3.7's `server/go.mod`): `NewVersion("v3.8.0")` fails and `Must` panics; `NewVersion("3.8.0")` succeeds. What the PR's premise and the fake peer above rest on. | coreos/go-semver v0.3.1 | `cd coreosprobe && go run .` |
| `astdiff/` (`main.go`, `go.mod`) | The scratch `go/ast` comparison that lists the changed functions and types (step 3 of the report). | the fork branch, `HEAD~1` vs `HEAD` | `cd astdiff && go build -o astdiff .`, then `astdiff <old.go> <new.go>` per changed file |
