# Files of the etcd-io/raft#239 verification

The report is `../raft-239.md`. Revisions:
- PR head: `d96366fd4d69691369a5e334284f265972631a6f`; upstream base: `d155efc81`.
- Fork: branch `pr-raft-239-goose-lean`, commit `0a099f0cc`, which is `raft37-goose-lean`
  `509271dac` plus the PR.

| File | What it shows | Runs against | Command |
|---|---|---|---|
| `readindex_singleton_test.go.diff` | The one divergence from the PR, test only: the fork's own `TestReadIndexSingletonRemovedLeaderStale` now checks that the removed leader stepped down, its old scenario being unreachable | applies to `509271dac` + the PR (it is the diff `0a099f0cc~1..0a099f0cc`, which includes it) | `git -C <fork checkout at 509271dac + PR> apply readindex_singleton_test.go.diff` |
| `readindex_singleton_test.unmodified.out` | Without that change the test fails with the PR applied (`node 2 stepped down`): the PR removes that execution | `509271dac` with the PR's `raft.go` and `rafttest` changes, test file as at `509271dac` | `git checkout 0a099f0cc~1 -- readindex_singleton_test.go` (in a fork checkout at `0a099f0cc`) then `GOTOOLCHAIN=go1.27.1 go test -run TestReadIndexSingletonRemovedLeaderStale -v .` |
| `readindex_singleton_test.out` | With the change both `TestReadIndexSingleton*` tests pass | `0a099f0cc` | `GOTOOLCHAIN=go1.27.1 go test -run TestReadIndexSingleton -v .` (in a fork checkout at `0a099f0cc`) |
| `tcb-check.txt` | The full trust base equals `etc/tcb-baseline.txt`; the `pr-raft-239` collection has the same baseline on this branch and on `lean` | this branch after a full `lake build`; `lean` (main checkout) | `LAKE_ARTIFACT_CACHE=true LAKE_RESTORE_ARTIFACTS=true etc/tcb-report.py --check`, and `--collection etc/tcb-collections/pr-raft-239.txt --check` |
| `edit_phys.py`, `edit_sdrf.py` | The mechanical edits that removed `sdr` from `InvRaftPhys.lean` and the `sdrOk`/`Hsdrf` threading from the `RawNode` proofs, before the hand fixes; kept as a record, already applied | the `lean` tree at `d606c9cac` | `python3 edit_phys.py Proof/go_etcd_io/raft/v3/InvRaftPhys.lean`; `python3 edit_sdrf.py <files>` |
