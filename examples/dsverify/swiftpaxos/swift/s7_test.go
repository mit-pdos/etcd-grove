package swift

import "testing"

// S7: a replica must take as the leader's hashes only an ack of the current
// ballot's leader that has a hash per key; updateLogs indexed past the hashes
// after its (non-exiting) Fatal: a panic.
//
// Replica 2 of three at ballot 4 (leader 1). Replica 1's acks carry no
// hashes when they are light slow acks it sent in ballot 0 (batched into an
// MOptAcks: Checksum empty), or the fast acks handleSync sends.
func TestIssueS7_LeaderHashesChecked(t *testing.T) {
	r := newTestReplica(t, 3, 2, 4, false)
	c, d := cid(1, 0), cid(1, 1)

	defer func() {
		if p := recover(); p != nil {
			t.Fatalf("panic: %v", p)
		}
	}()
	// an ack without hashes, before the proposal: recorded as pending, then
	// applied by the proposal
	r.recordLeaderHash(c, 0, []SHash{})
	r.handleProposal(put(c, 3, "x"))
	// after the proposal
	r.handleProposal(put(d, 3, "y"))
	r.recordLeaderHash(d, 1, nil)

}
