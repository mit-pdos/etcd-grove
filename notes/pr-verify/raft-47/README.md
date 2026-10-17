# Files for the verification of etcd-io/raft#47

The report is `notes/pr-verify/raft-47.md`. Revisions:

- the PR applied to the Goose fork: branch `pr-raft-47-goose-lean` of `~/etcd` (`upamanyus/etcd`
  clone), commit `59be9c1e4`, worktree `~/etcd-pr/raft-47` (not pushed);
- the base: the pinned raft revision of `etc/goose.py`, `509271dac` (branch `raft37-goose-lean`).

| File | What it shows | Runs against | Command |
|---|---|---|---|
| `raft47_probe_test.go` | Two probes of the states the PR's checks catch. `TestProbeRaft47InconsistentStorage`: a single voter restarted from a `MemoryStorage` whose `HardState.Term` (1) is below its last entry's term (3) wins term 2 through the public `RawNode` API; with the PR `becomeLeader`'s `appendEntry` panics, without it the leader's log terms are `[1 2 3 2]` (`issues/raft-storage-hardstate-term-below-log.md`). `TestProbeRaft47SnapshotHigherTerm`: `restore` of a snapshot at term 11 by a follower at term 2; with the PR it is refused and the node steps down to term 11, without it the snapshot is restored at term 2. | both (the file is in package `raft`, protobuf-go v2 messages: not the PR's own head, which is gogoproto) | `cp raft47_probe_test.go <checkout>/ && GOTOOLCHAIN=go1.27.1 go test -run TestProbeRaft47 -v .` |
| `probe-pr-59be9c1e4.log` | The probes pass with the PR. | `59be9c1e4` | as above |
| `probe-base-509271dac.log` | The probes fail without it: `no panic: state StateLeader at term 2, log terms [1 2 3 2]`; `restored at term 2, log last term 11`. | `509271dac` | as above |
| `review47_msgapp_test.go` | The reviewer's probe: a follower at term 2 accepts a `MsgApp` of term 2 whose entry has term 5 (`handleAppendEntries` does not check entry terms against the message's); at its next won election (term 3) the PR's `appendEntry` panics, `appending out-of-order term: 3 < 5`; without the PR the leader's log terms are `[5 3]`. A message no correct leader sends (the model's `isMessage` excludes it). | both | `cp review47_msgapp_test.go <checkout>/ && GOTOOLCHAIN=go1.27.1 go test -run TestReview47 -v .` |
| `review-pr-59be9c1e4.log`, `review-base-509271dac.log` | Its output on each revision (the test only logs; it passes on both). | as named | as above |
