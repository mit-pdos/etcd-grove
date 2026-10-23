package bridge

import (
	"net"
	"testing"
)

// TestBlackholeTwicePanics confirms issues/nonissues/etcd-bridge-blackhole-twice-panic.md: a second
// Blackhole without an Unblackhole in between panics ("close of closed channel"), holding the
// bridge's mutex (so the test does not close the bridge after: Close would wait for it forever).
func TestBlackholeTwicePanics(t *testing.T) {
	l, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	b := New("127.0.0.1:1", l)
	b.Blackhole()
	defer func() {
		if r := recover(); r != nil {
			t.Logf("second Blackhole panicked: %v", r)
			return
		}
		t.Fatal("second Blackhole did not panic")
	}()
	b.Blackhole()
}
