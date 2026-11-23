package swift

import "testing"

// S7 (the ballot): an ack the replica that is now the leader sent in an older
// ballot, as a follower, does not carry the leader's hashes.
func TestIssueS7_OldBallotAckNotLeaders(t *testing.T) {
	r := newTestReplica(t, 3, 2, 4, false)

	// an old ballot's ack of the replica that is now the leader is not the
	// leader's: its hashes are not recorded
	e := cid(1, 2)
	r.handleProposal(put(e, 3, "z"))
	before := r.hlog[3].hash
	r.leaderAckHash(&MFastAck{Replica: 1, Ballot: 0, CmdId: e, Checksum: []SHash{{H: [32]byte{9}}}})
	if r.hlog[3].hash != before {
		t.Fatalf("an ack of ballot 0 was taken as ballot 4's leader's hashes")
	}
}
