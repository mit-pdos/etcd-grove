---
upstream: none
checked: 2026-11-15
links:
blocks-proof: no
---
# raft: with PreVote and CheckQuorum off, a learner that adopts a removed voter's higher term never catches up again

A voter that is removed from the configuration but never applies its removal keeps campaigning in
its old configuration. Without PreVote, each campaign raises its term and sends `MsgVote` to the
members of that old configuration. A learner of the current configuration that is among them takes
the higher term (any message of a higher term makes a node a follower at that term). Then, without
CheckQuorum or PreVote, raft ignores the leader's `MsgApp` and `MsgHeartbeat` at the lower term
without answering
([`raft.Step`, `m.Term < r.Term`](https://github.com/etcd-io/raft/blob/v3.7.0/raft.go#L1133-L1134)).
The leader never learns of the higher term, and a learner never campaigns
([`promotable`](https://github.com/etcd-io/raft/blob/v3.7.0/raft.go#L980)), so the learner stays
behind for good. Raft's own comment there assumes the stuck node is a voter: "if checkQuorum is
false, this will be handled by incrementing term numbers in response to MsgVote with a higher term"
holds only for a node that campaigns.

Seen in `examples/raft/kvraft`'s test (2026-11-15, raft at the fork's `565c2bd`, options PreVote and
CheckQuorum off): voters {2, 7} and learner 8 at term 147, leader 2 at index 405; replica 6, removed
at its applied index 346 where it is still a voter of {3, 6, 8}, campaigning at term 2232; learner 8
at term 2232, no leader, applied 371, forever.

**Why not an issue:** liveness only, and only with both PreVote and CheckQuorum off. etcd enables
both by default (`--pre-vote` since 3.4, CheckQuorum always), and with either one on the learner
answers the leader's `MsgApp` with its term (CheckQuorum, PreVote) or never adopts the removed
node's term (PreVote: a pre-vote raises no term). No test against raft's own harness yet.

## Proof

no: liveness; no adequacy result claims the cluster converges.

## Notes

`examples/raft/kvraft`'s convergence check tolerates such a stranded learner in that option combination
(`driver.agree`). A fix would be for a follower that is not promotable to answer a lower-term
`MsgApp`/`MsgHeartbeat` with its term, as the CheckQuorum/PreVote branch does, so the leader steps
down and a new election catches the term up. Upstream searched 2026-11-15 (etcd-io/raft: "learner",
"learner higher term", "removed node", "learner stuck term"; etcd-io/etcd: "learner term", "disruptive
removed member"): nothing on this.
