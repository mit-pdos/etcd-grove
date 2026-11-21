---
upstream: none
checked: 2026-11-21
links: []
blocks-proof: no
---

# A healthy shared Raft witness cannot help a joint configuration commit

**Impact:** A leader in the experimental witness fork stops committing proposals when one
half of a joint configuration needs its witness and the other has a majority
of regular voters. The stall occurs with either the incoming or the outgoing
half relying on the witness.

The Go test starts the leader with voter sets {1, 2, 5} and {1, 3, 4, 5, 6}.
Voter 5 is the witness in both. Voter 2 is unavailable. The leader appends a
proposal, accepts acknowledgements from voters 3, 4 and 6, and delivers all
pending witness requests and replies. The larger half already has a regular
majority. In the smaller half the leader and the live witness can form a
majority. [Go test](raft-witness-joint-progress/witness_joint_progress_test.go)

**Expected:** The leader commits the proposal with these acknowledgements.

**Reproduction:** Copy the test to the Raft module root at `3e3ed2d29742` and run
`go test . -run '^TestSharedWitnessCommitsWithOneHalfMissingAVoter$' -count=1`.
In both orientations the test on the VM observed commit index 1 after proposing
the entry at index 4.

**Cause:** The tracker returns an empty result when only one of the
two halves selects the shared witness, so the leader never offers it the
proposal. [Pinned tracker](https://github.com/upamanyus/etcd/blob/3e3ed2d2974287a24803a1772d1a4216cc5aee05/tracker/tracker.go#L274-L312)

## Proof

The stall concerns progress. The fork also has a leader completeness regression
test for a joint configuration where the larger half lacks a regular majority.
The witness's acknowledgement counts in both halves, so its proposed index
must account for the acknowledgements in each. [Original safety case](../notes/raft-witness-vs-pr168/joint-oltq.md)

## Fix

The tracker offers the shared witness the smaller of the two supported indices.
A half selecting the witness needs quorum minus one regular acknowledgements.
A half that excluded it needs a full regular majority. The Go regression passes
in both orientations, and the existing regression for a candidate missing a
committed entry also passes. [Fork fix](https://github.com/upamanyus/etcd/commit/13190826c05a3e8357e7a9041db70ab5a0644582)
