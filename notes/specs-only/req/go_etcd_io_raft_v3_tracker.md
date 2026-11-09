# Requirements on `go.etcd.io/raft/v3/tracker` (batch R4)

## from R2

The raft core (`Spec/go_etcd_io/raft/v3/ApiCore.lean`) keeps the tracker inside `raftCore`; its
proof sketches need:
- `ProgressTracker` ownership with its configuration as R1's `Membership` (the model shared with
  `confchange`), the progress map's keys exactly the configuration's ids (`raftCore_peek` exposes the
  map `r.trk.Progress` as `ownMap mp _ ρ.prs`: R2 states `ρ.prs : GMap w64 Loc`, the `*Progress` of
  each id);
- `Visit` (sorted ids; the callback may mutate the visited `Progress`), `VoterNodes`, `Voters.IDs()`
  (the voters of both halves), `IsSingleton`, `QuorumActive`, `Committed()` (the quorum's match
  index under the joint configuration: what `maybeCommit` counts), `RecordVote`, `TallyVotes`
  (`VoteWon` only with a quorum of granted votes in both halves), `ResetVotes`, `ConfState()`
  (lists the configuration), `MakeProgressTracker`, `Config.Clone` (fresh maps);
- `Progress`: `IsPaused`, `MaybeUpdate`, `MaybeDecrTo`, `BecomeProbe`/`Replicate`/`Snapshot`,
  `SentEntries`, `SentCommit`, `CanBumpCommit`, `Inflights.Full`/`FreeLE`/`Clone`: no panic under
  the leader's use (indices within the leader's log); none of them is safety-relevant except
  `Match` (an acknowledged index, from a `msgSent` response or the leader's own durable append).
- `getProgressCopy`'s fresh copies: R2 states them as a provisional `progressCopyOwn mp`; please
  give the predicate (R1's `statusOwn` is built from it and `Config.Clone`'s).
