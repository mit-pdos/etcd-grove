# etcd#20915: the files the report relies on

The report is `notes/pr-verify/etcd-20915.md`. Revisions:
- the PR head is `b7e2d97fc` (etcd-io/etcd `pull/20915/head`);
- its base is `b1d3e04be` (etcd-io/etcd `main`);
- the fork branch is `mit-pdos/etcd-grove` branch `pr-etcd-20915-goose-lean`, commit `e249b47ed`:
  `pr-etcd-22261-goose-lean` (`22be0af01`) plus the PR's other three commits.

The tests and probes of etcd#22261's verification (`notes/pr-verify/etcd-22261/`, on this branch
too) apply unchanged: #20915's last commit is #22261's, with the same patch-id.

| File | What it shows | Runs against | Command |
|---|---|---|---|
| `build-without-tags.sh` | Finding A. It builds etcd with the PR's `scripts/build.sh` in two checkouts and starts it: a source tarball (`git archive`, no `.git`) and a shallow clone without tags. `VERSION` falls back to `GitNotFound` in the first and to the 14-digit commit hash in the second, and `-X ...version.Version` injects it. Run against the base, the same tarball build keeps `3.8.0-alpha.0` and serves. | the PR head (branch `pr-etcd-20915` in a clone of etcd-io/etcd); the base for the contrast run | `build-without-tags.sh ~/etcd pr-etcd-20915 <outdir>` (`GOTOOLCHAIN=go1.27.1`) |
| `build-without-tags.log` | The output: both PR-head builds print the bad version and exit 2 within seconds of starting, with `panic: invalid semantic version` in `semver.MustParse(version.Version)` (`etcdserver/version/monitor.go:159`). The base tarball build is still serving after 20 s. | PR head and base | as above |
| `peer_version_downgrade_test.log` | etcd#22261's `peer_version_downgrade_test.go` (in `../etcd-22261/`), run at #20915's head. The test sets `Version = "v3.8.0"` itself. It fails by design, as at #22261's head: the stale cache. | the PR head | `cp ../etcd-22261/peer_version_downgrade_test.go <checkout>/server/etcdserver/api/rafthttp/ && cd <checkout>/server && go test -run TestPeerVersionCacheStaleAfterDowngrade ./etcdserver/api/rafthttp/` |
