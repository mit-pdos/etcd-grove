package epaxos

import (
	"bufio"
	"bytes"
	"testing"
)

// TestPreAcceptReplyEmptyDepsRoundTrip [PAR-UNM]: (*PreAcceptReply).Unmarshal sets bs = b[:4]
// only inside the Deps loop, so with no Deps it reads each CommittedDeps entry into b[:21] and
// consumes bytes past the message. Marshal followed by Unmarshal must give the message back and
// leave the next message intact.
func TestPreAcceptReplyEmptyDepsRoundTrip(t *testing.T) {
	m := &PreAcceptReply{Replica: 1, Instance: 2, Ballot: 3, VBallot: 4, Seq: 5,
		Deps: []int32{}, CommittedDeps: []int32{7, 8}, Status: PREACCEPTED}
	var buf bytes.Buffer
	w := bufio.NewWriter(&buf)
	m.Marshal(w)
	w.WriteByte(0xAB)
	w.Flush()
	r := bufio.NewReader(&buf)
	var got PreAcceptReply
	if err := got.Unmarshal(r); err != nil {
		t.Fatalf("Unmarshal: %v", err)
	}
	if len(got.CommittedDeps) != 2 || got.CommittedDeps[0] != 7 || got.CommittedDeps[1] != 8 {
		t.Fatalf("CommittedDeps = %v, want [7 8]", got.CommittedDeps)
	}
	if b, err := r.ReadByte(); err != nil || b != 0xAB {
		t.Fatalf("next byte = %v, %v; want 0xAB (stream out of sync)", b, err)
	}
}
