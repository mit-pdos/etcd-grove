# The witness implementation here vs etcd-io/raft#168

etcd-io/raft#168 ("Extend Raft algorithm to support share witness", head `43f19c68`, Feb 2024,
draft) is the implementation of etcd-io/raft#133. This repository's implementation is the fork
branch `raft-witness-goose-lean` of `upamanyus/etcd` (`notes/raft-witness.md`): #168 rebased onto
the pinned raft v3.7 (`c8217eb9`, protobuf-go v2) as one commit, with the fixes below on top. Each
row is a defect of #168, how it shows, and what the fork does instead; the tests are in the fork
(`witness_test.go`, `confchange/witness_restore_test.go`, `quorum/witness_olq_test.go`). Rows 1-4
and 7 were found by `pr-verify/raft-168` (`notes/pr-verify/raft-168.md`, on that branch), rows 5, 6,
8, 13 and 14 by this work (0 by the W2 proof design, 13 and 14 by W3a's specs).

| # | defect in #168 | effect | here | test |
|---|---|---|---|---|
| 0 | **(safety)** the witness proxy answers a `MsgHeartbeat` from its *cached* state when the cached term is the heartbeat's (`processNoUpdate`) | a leader cut off from the other voters but not from the witness's storage keeps getting heartbeat acknowledgements after another node was elected in a newer term with the witness's vote and committed writes: it **confirms read-index requests at an index missing a committed write** (a non-linearizable read), and keeps the witness `RecentActive` (check-quorum never steps it down) | a heartbeat is answered only after the storage is read: a stale term gets the newer-term answer and the leader steps down (fork `edd87c489`); found by the W2 proof design | `TestWitnessStaleReadIndex` (fails on #168's proxy: the read is answered at index 3 without the write) |
| 1 | `confchange.Restore` of a joint config whose witness is in both halves (`(1 2 3 4)&&(1 2 3)`, witness 3): `remove(3)` keeps 3's Progress (outgoing voter), so `makeWitness(3)` returns early without re-adding 3 to the incoming config | `newRaft`/`raft.restore` panic in `assertConfStatesEquivalent`: a node restarting, or installing a snapshot, in such a config crashes | `makeWitness` re-adds a tracked witness to the incoming voters and sets `Witnesses[0]`, as `makeVoter` does | `TestWitnessRestoreJoint`, `TestWitnessRestartInJointConfig` |
| 2 | `raftLog.lastEntry()` reads `entries(lastIndex)`, `ErrCompacted` when the log ends at a snapshot, and panics | a candidate that just installed a snapshot crashes when it asks the witness for its vote | `raftLog.subterm(i)` reports "not available"; the candidate sends the snapshot's term and subterm 0 (a lower subterm only makes the witness refuse: safe) | `TestWitnessCandidateAfterSnapshot` |
| 3 | `maybeCommit` calls `raftLog.entry(wci)`, which panics when the quorum−1 index is below `firstIndex()` (a follower just sent a snapshot) | the leader crashes | the compacted index is skipped (`raftLog.subterm`) | `TestWitnessLeaderMaybeCommitCompacted` |
| 4 | `MajorityConfig.OneLessThanQuorum` on a one-voter config reads `srt[1]` of a one-slot slice | out-of-range panic (raft itself does not reach it; the function is exported) | returns 0 ("quorum − 1 = no voter") | `TestOneLessThanQuorumSingleVoter`; spec `quorum/MajorityConfig__OneLessThanQuorum` (no premise) |
| 5 | `stepCandidate` asks the witness for its vote on **every** vote response while the election is pending, including the witness's own rejection | a request loop (each request a witness storage access); an in-process cluster never settles | a candidate asks each witness at most once per campaign (`witnessVoteAsked`, cleared by `reset`) | `TestWitnessClusterCommitAndSafety` (hangs on #168's logic) |
| 6 | `witness.handleAppend`'s acknowledgement after a write that raised the witness's term carries the witness's **old** term | the leader drops the ack as stale and must retry (liveness) | the ack carries the new term | `TestWitnessAppendNewerTermResponse` |
| 7 | `witness.processMessageWithOlderTerm` answers a stale leader with a `MsgAppResp` without `Term`/`From` | raft drops it (a local message from node 0): the stale leader is never told of the newer term | the answer carries the witness's term and id | `TestWitnessOlderTermResponse` |
| 8 | the witness cache (`w.state`) is not updated after a successful write | the next request reloads the storage once (a read, no write) before the cache answers: one extra storage access per write (efficiency only) | the cache is the written state after a successful CAS | `TestWitnessClusterCommitAndSafety` (no storage write for entries after the first of a subterm) |
| 13 | `Process` answers a heartbeat of a newer term, after raising the state being written to it, with `handleHeartbeat`'s term of the state read *before* the raise (`w.state`), the pattern of row 6 | the leader drops the answer as stale: one heartbeat round lost under check-quorum (liveness) | `handleHeartbeat(m, term)` takes the term: the stored state's on the early path, the raised state's on the newer-term path (fork `9ed005d46`); found writing `handleHeartbeat`'s spec (W3a, `issues/raft-witness-heartbeat-stale-term.md`) | `TestWitnessHeartbeatNewerTermResponse` |
| 14 | `cloneState` reads `w.state.ReplicationSet` directly, while every other read of the state goes through the nil-safe getters; `WitnessState.GetState` does not say it is never nil | a storage that hands out a nil state for "nothing stored yet" makes the first request not answered from the cache (a vote request, say) panic | `cloneState` reads through `GetReplicationSet()`/`GetReplicationSetOutgoing()`: a nil state is the zero state (fork `9ed005d46`); found writing `cloneState`'s spec (W3a, `issues/raft-witness-getstate-nil.md`) | `TestWitnessNilStoredState` |

Behaviour changes of #168 for clusters **without** a witness, reverted here (so that such a
cluster behaves exactly as v3.7 and the existing proof carries over):

| # | #168 | effect | here |
|---|---|---|---|
| 9 | the leader starts a new subterm, appending an empty entry, on **every** conf change it applies | every witness-free log changes; 22 datadriven test files rewritten | only when the old or new configuration involves a witness; v3.7's testdata pass unchanged |
| 10 | `ApplyConfChange` returns `(nil, error)` instead of panicking (`Node`, `RawNode`) | incompatible public API change; `Bootstrap` drops the error; a caller ignoring it proceeds with a nil `ConfState` | v3.7's signature (panics on an invalid change) |
| 11 | new log lines on every election (`It needs [1 0] votes to win`, `resets replication set`, `starts new subterm`) | log output of witness-free clusters changes | only with a witness |
| 12 | `DescribeConfState` always prints `Witness:0 WitnessOutgoing:0` | output changes | printed only when set |

Not changed, a limitation of both: **lease-based reads (`ReadOnlyLeaseBased`) are not safe with a
witness.** A leader marks a peer `RecentActive` on any `MsgAppResp`, and the witness's
acknowledgements of appends of the leader's subterm come from the proxy's cache (shortcut
replication, which is what makes the witness cheap): a stale leader keeps counting the witness as
active, so its lease outlives a newer leader. Read-index (`ReadOnlySafe`) is safe after row 0's
fix, and is what the proof covers; a cluster with a witness must not use lease-based reads.

Not changed, recorded: `ChangeReplicationSet` picks the voter to exclude in map order
(nondeterministic, no safety impact); `ReplicationSet.Clone` drops `NonWitnessVoters` (unused).

Open, for both: a witness in a joint configuration or across reconfiguration. #168 allows a
witness in each half and checks the vote responders against the incoming half's replication set
only; the safety argument of `notes/raft-witness.md` is for a fixed configuration, and so will be
the proof (stage W2) until reconfiguration is argued.

The paper's TLA+ spec (`algo/extended-raft.tla` of joshuazh-x/extended-raft-paper) is a draft that
does not type-check (`witnessSubterm` never initialised; `InitLeaderVars` assigns scalars to
per-server variables; `HandleAppendEntriesResponse` never updates `witnessSubterm`, so shortcut
replication never happens in it), so the issue's "checked with the TLC model checker" cannot be of
that file.
