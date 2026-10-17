package quorum

import "testing"

func TestOneLessThanQuorumSingleVoter(t *testing.T) {
	defer func() {
		if r := recover(); r != nil {
			t.Fatalf("OneLessThanQuorum of a one-voter config panicked: %v", r)
		}
	}()
	MajorityConfig{1: {}}.OneLessThanQuorum(mapAckIndexer{1: 5})
}
