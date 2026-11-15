---
upstream: none
checked: 2026-11-09
links:
blocks-proof: no
---
# v3election: a Proclaim with leader revision 0 creates the leader key

v3election's `Proclaim` (and `Resign`) build the election from the remote request's leader key,
`ResumeElection(s, name, req.Leader.Key, req.Leader.Rev)`, with nothing checked
(`server/etcdserver/api/v3election/election.go:68`). `Election.Proclaim` fences its put with
`CreateRevision(leaderKey) = leaderRev` (`client/v3/concurrency/election.go:115`). A comparison on
an absent key compares create revision `0`, so with `Rev = 0` (the protobuf default when the client
leaves it unset) and a key that does not exist, the fence holds and the put creates the key under
the caller's lease: `Proclaim` succeeds for a key that never campaigned, possibly not under the
election's prefix.

**Why not an issue:** a precondition the API does not state (the leader key is meant to be the one
`Campaign` returned, whose revision is positive); found by code reading; the effect is only a key
the caller may write anyway.

## Proof

no: `Election.Proclaim.spec` states its fence as the comparison W0's model evaluates (`ownerCmp`'s
`Compare.holds`), which holds of an absent key at revision `0`; nothing relies on the key being
present.

## Notes

- Batch 1d's reviews (`notes/specs-only/reviews/1d-provability-1.md` F3, `1d-completeness-1.md` C2):
  the round-0 spec claimed the key present on success, false at revision `0`.
- A check in v3election (`Rev > 0`, and the key under the election's prefix) would make the API's
  intent explicit.
