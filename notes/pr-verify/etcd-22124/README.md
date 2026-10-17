# Files for `notes/pr-verify/etcd-22124.md`

The regression probe `election_resign_lost_proclaim_test.go` is `notes/pr-verify/etcd-22211/`'s, unchanged (it is on this branch too).

| File | What it shows | Runs against | Command |
|---|---|---|---|
| `election_resign_test.go` | The PR's own test, `TestElectionResignCanRetryAfterError`, verbatim from the PR head `ad7fe73e5`. | `09669450f` (fails), `mit-pdos/etcd-grove` branch `pr-etcd-22124-goose-lean` `41a1acbcf` (passes) | `cp election_resign_test.go <checkout>/tests/integration/clientv3/concurrency/ && cd <checkout>/tests && go test ./integration/clientv3/concurrency -run 'TestElectionResignCanRetryAfterError$' -count=1 -v` |
| `retry.pinned.log` | That test failing at the pinned code: `Key()` is `""` after the failed `Resign`. | `09669450f` | as above |
| `retry.fork-pr.log` | That test passing with the PR. | `pr-etcd-22124-goose-lean` `41a1acbcf` | as above |
| `fork-pr-integration.log`, `prhead-integration.log` | The whole `tests/integration/clientv3/concurrency` package passing, with the PR's test, on the fork branch and at the upstream PR head. | `41a1acbcf`; PR head `ad7fe73e5` | `cd tests && go test ./integration/clientv3/concurrency -count=1` |
| `lost_proclaim.fork-pr.log`, `lost_proclaim.prhead.log` | The regression of #22211 is in #22124 too: after `Proclaim` returns `ErrElectionNotLeader`, every `Resign` fails with "etcdserver: key is not provided". (It passes at `09669450f`: `notes/pr-verify/etcd-22211/lost_proclaim.pinned.log`.) | `41a1acbcf`; PR head `ad7fe73e5` | `cp ../etcd-22211/election_resign_lost_proclaim_test.go <checkout>/tests/integration/clientv3/concurrency/ && cd <checkout>/tests && go test ./integration/clientv3/concurrency -run 'TestElectionResignAfterLostProclaim$' -count=1 -v` |
| `axioms.txt` | The repository axioms under `#print axioms` of `election_Resign` and `election_Campaign`: identical to #22211's and `lean`'s; no `sorryAx`. | this branch | `lake env lean ax.lean` (imports `Proof.go_etcd_io.etcd.client.v3.concurrency.Results`, then `#print axioms Perennial.EtcdGrove.concurrency.election_Resign` and `...election_Campaign`) |
