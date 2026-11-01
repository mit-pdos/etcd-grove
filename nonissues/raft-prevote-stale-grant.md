---
upstream: known
checked: 2026-10-20
links:
  - etcd-io/etcd#8288 pr merged: same bug, raised in review and left unfixed (bdarnell, 2017-07-20: "We could accept a MsgPreVoteResp for term T as a valid pre-vote in term T+1"; accepted as "(rare) false positives" leading to a full election); no comment in the code records it
  - etcd-io/etcd#8243 issue closed: related, not this bug: the PreVote stall #8288 fixed by answering with the request's term, which is what lets the stale grant through
blocks-proof: no
---
# raft: a pre-candidate counts a pre-vote granted in an earlier pre-campaign

A delayed `MsgPreVoteResp` from an earlier pre-campaign is tallied for the current one: nothing ties
a response to the round that asked (it carries only the requested term). A node can then start a
real election, raising its term past the leader's and deposing it, on pre-votes its peers did not
grant for this round: the disruption pre-vote exists to prevent. It needs a response delayed past
a leader election and an election timeout.

**Why not an issue:** not a guarantee raft makes: discussed upstream in 2017 (etcd-io/etcd#8288)
and accepted as a rare false positive that costs one election, not safety; INDEX-reviewed.md's
Plan: "non-issue, based on the prior discussion; would want to see problems demonstrated to revisit".

`TestPreVoteStaleGrantFromEarlierRound` and `TestPreVoteStaleGrantSameTerm` in
[`nonissues/raft-prevote-stale-grant/prevote_stale_grant_test.go`](raft-prevote-stale-grant/prevote_stale_grant_test.go)
(direct `Step` on a `raft`, pre-vote and check-quorum on) fail at etcd-io/raft@c51f010c851e,
go1.27.3: `stale grant counted: node 1 campaigns at term 3 on a pre-vote granted for term 2` and
`... campaigns at term 2 on a grant from an earlier round`.

## Proof

no: not a safety question: the model admits any pre-vote response and the real election still
needs real votes; the pre-vote stage's term budget must cover the term rise
(`notes/status-history.md`, "Raft: CheckQuorum and PreVote on").

## Notes

Fix sketch: at a pre-candidate count only grants with `Term == r.Term + 1` (shape 1); shape 2
(same term) needs a per-round nonce in the response.
