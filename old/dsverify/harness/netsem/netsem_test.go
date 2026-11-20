package netsem

import "testing"

// examples are the measured examples; TestExamples runs them on loopback, TestVeth (veth_test.go)
// over the rig's veth links.
var examples = []struct {
	name string
	f    func() (string, error)
}{
	{"ShortRead", ShortRead},
	{"PartialWrite", PartialWrite},
	{"DeadlineUsable", DeadlineUsable},
	{"CloseThenEOF", CloseThenEOF},
	{"BreakSuffix", BreakSuffix},
	{"WriteAfterPeerClose", WriteAfterPeerClose},
	{"CloseUnreadResets", CloseUnreadResets},
	{"DialListen", DialListen},
	{"ZeroRead", ZeroRead},
	{"ErrClosed", ErrClosed},
	{"WriteCloseRace", WriteCloseRace},
	{"WriteBreakPartial", WriteBreakPartial},
	{"DialTimeoutAccepted", DialTimeoutAccepted},
}

func runExamples(t *testing.T) {
	for _, ex := range examples {
		out, err := ex.f()
		if err != nil {
			t.Errorf("%s: %v", ex.name, err)
			continue
		}
		t.Logf("%s: %s", ex.name, out)
	}
}

// TestExamples runs every example on loopback and logs what this host does (run.sh records it).
func TestExamples(t *testing.T) { runExamples(t) }
