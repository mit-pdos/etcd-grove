package ledger

// R1-wake: GetDecisionOrWake's channel is closed when the slot's decision is recorded (SetDecision) or the slot is
// reset (Reset, under the slot's lock), once; a waiter that comes after the decision gets no channel.

import (
	"testing"
	"time"

	"rabia/internal/message"
)

func closedSoon(ch chan struct{}) bool {
	select {
	case <-ch:
		return true
	case <-time.After(time.Second):
		return false
	}
}

func TestWakeOnDecisionAndReset(t *testing.T) {
	s := &Slot{}
	s.Reset()
	_, done, w1 := s.GetDecisionOrWake()
	_, _, w2 := s.GetDecisionOrWake()
	if done || w1 == nil || w1 != w2 {
		t.Fatalf("not done: want one shared channel, got done=%v %v %v", done, w1, w2)
	}
	go s.SetDecision(message.ConsensusObj{ProId: 7})
	if !closedSoon(w1) {
		t.Fatal("SetDecision did not wake the waiter")
	}
	dec, done, w := s.GetDecisionOrWake()
	if !done || w != nil || dec.ProId != 7 {
		t.Fatalf("after the decision: done=%v wake=%v dec=%v", done, w, dec)
	}
	s.SetDecision(message.ConsensusObj{ProId: 8}) // no waiter: nothing to close (closing twice would panic)

	s.Lock.Lock()
	s.Reset()
	s.Lock.Unlock()
	_, done, w3 := s.GetDecisionOrWake()
	if done || w3 == nil || w3 == w1 {
		t.Fatalf("after a reset: done=%v wake=%v", done, w3)
	}
	s.Lock.Lock()
	s.Reset()
	s.Lock.Unlock()
	if !closedSoon(w3) {
		t.Fatal("Reset did not wake the waiter")
	}
}
