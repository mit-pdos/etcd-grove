# raft: with the initial `ConfState` in an index-0 snapshot, a node added later replays conf changes onto an empty configuration and can win alone

- **Status**: open (undocumented precondition; not reported upstream).
- **Where** (etcd-io/raft at `40f8be730b18`):
  - `storage.go:211-219` (`MemoryStorage.ApplySnapshot`) accepts an index-0 snapshot that
    carries only the initial `ConfState` ("During bootstrap, applications (e.g., etcd) may
    initialize only the ConfState in the snapshot. In this case, both the snapshot index and
    term are 0."). The log then starts at index 1 with no conf entry for the initial
    configuration.
  - `bootstrap.go:25-29` (`RawNode.Bootstrap`) recommends a storage "that has a first index
    > 1 and which stores the desired ConfState as its InitialState": only then must a new node
    be caught up by snapshot. Nothing says what happens with first index 1.
  - A node added later starts with empty storage (`newRaft`, `raft.go:469-477`: an empty
    `ConfState`); the leader, whose first index is 1, sends it entries from index 1 by
    `MsgApp` (`sendAppend`), never a snapshot; the application applies their conf changes
    (`ApplyConfChange`, `confchange.Changer`) to the node's empty configuration.
  - After its own `add` it is a voter of a configuration made of the changes alone (`{4}`
    below): `promotable` (`raft.go:1934-1937`) holds, `hasUnappliedConfChanges` is false, and
    `TallyVotes` over that configuration counts its own vote as a quorum.
- **What happens**: `C0 = {1,2,3}` bootstrapped on nodes 1-3 by an index-0 `ConfState`
  snapshot; node 4 starts empty. Node 1 leads term 1 and commits `add 4` (index 2); node 4
  catches up by `MsgApp` and applies it: its configuration is `voters=(4)` while node 1's is
  `voters=(1 2 3 4)`. Node 4 is cut off; node 1 commits `x` at index 3 with `{1,2,3}`; node 4
  campaigns, wins term 2 on its own vote and commits its empty entry at index 3. Every
  application applies conf changes before `Advance` (faithful).
  Reproduction: `raft-conf-lag-model/joiner_empty_confstate_test.go`, which passes by
  asserting the violation:

      cp issues/raft-conf-lag-model/joiner_empty_confstate_test.go <etcd-raft checkout>/
      cd <etcd-raft checkout> && go test -run TestJoinerWithoutBootstrapConfState -v .
      ...
      node 1 config voters=(1 2 3 4); node 4 config voters=(4) (caught up by MsgApp from index 1)
      SAFETY VIOLATION reproduced: index 3 committed as "x" (term 1) on node 1 and as "" (term 2) on node 4

- **Expected**: the documentation states the precondition: a node added to a cluster whose
  initial configuration is not in the log must start from that configuration (its storage
  seeded with the same `ConfState`), or the bootstrap must use a first index > 1 so that new
  nodes are caught up by snapshot (`Bootstrap`'s recommendation, which as written reads as a
  matter of taste). Alternatively raft could refuse to send entries from index 1 to a node
  whose match is 0 when the log's initial configuration is only in a snapshot.
- **etcd**: unaffected as far as checked: a new etcd cluster bootstraps with `StartNode`
  and peers (`server/etcdserver/bootstrap.go:581-583`), so the initial configuration is in
  the log as conf entries, which a joiner (`RestartNode`, empty storage) replays.
- **In this repository**: `raft-conf-lag-model/leaderlag_test.go` sets node 4 up exactly this
  way (index-0 `ConfState` on nodes 1-3, node 4 empty). Its violation is unaffected (node 3,
  whose configuration is right, wins with node 4's vote), but its control claim ("with node 1
  applying before `Advance` the violation does not occur") holds only because node 4 never
  campaigns there: node 4's configuration in that harness is `{4}` too.
- **How the proof handles it**: the reconfiguration paper proof assumes every node starts from
  `c0` (`notes/reconfiguration-safety.md` section 0), but also says a node added later starts
  with an empty configuration and is unpromotable until it has applied a snapshot or the
  bootstrap prefix (sections 0 and 4.12); the second claim is false for this bootstrap. The
  scope must say how `c0` is set up: either `c0` is the fold of the log's first entries from
  the empty configuration (`Bootstrap`), or every node, including one added later, starts with
  `c0` as its `ConfState`, or new nodes are caught up only by snapshot.
- **Related**: the restart analogue, `Config.Applied` (`raft.go:145-149`): raft restores the
  configuration from `InitialState`'s `ConfState` and sets `applied` from `Config.Applied`
  without re-applying the conf entries in between; `MemoryStorage.InitialState` returns the
  snapshot's `ConfState`. An application that restarts with `Applied` past a conf entry newer
  than its stored `ConfState` gets a configuration behind `applied`: the window of
  [raft-advance-before-applyconfchange](raft-advance-before-applyconfchange.md), at restart.
  Not reproduced (restarts are outside the proof's scope).
- **Found**: 2026-10-14, adversarial review of the reconfiguration paper proof
  (`notes/reconfiguration-safety-review.md`, scope), reproduced by the test above.
