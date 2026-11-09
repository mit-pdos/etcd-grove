# Requirements on `go.etcd.io/raft/v3/quorum` (batch R4)

## from R2

`stepLeader`'s commit and read confirmation, `stepCandidate`'s election: `JointConfig.CommittedIndex`
(an index acknowledged by a majority of each half), `VoteResult` (`VoteWon` only with a majority of
granted votes in each half), and the intersection law the cluster invariant rests on: two majorities
of the same `JointConfig`, or of two configurations one change apart (`confchange`'s joint
transitions), intersect. Used by `raft.maybeCommit.spec`'s and `stepCandidate.spec`'s sketches.
