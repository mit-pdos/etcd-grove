package kvnet

import (
	"strings"
	"testing"
)

// TestRandomOptionsValid checks, over many random seeds, that the clusters the test driver runs pass
// RunNode's and kvcheck.Check's validation (ValidCluster, ValidAddrs, MaxDirLen): a cluster they
// reject is a safe run that exercises nothing, so the validation must not reject what the driver
// generates (the non-vacuity of the top-level theorem's having no premise on the configuration).
// Each validation clause is also shown to reject.
func TestRandomOptionsValid(t *testing.T) {
	addrs := []string{"127.0.1.1:7001", "127.0.1.2:7001", "127.0.1.3:7001", "127.0.1.4:7001",
		"127.0.1.5:7001", "127.0.1.6:7001", "127.0.1.7:7001", "127.0.1.8:7001", "127.0.1.9:7001"}
	for i := 0; i < 10000; i++ {
		o := RandomOptions()
		if !ValidCluster(addrs, o.Voters, o.MaxSizePerMsg, o.MaxCommittedSizePerReady, uint64(o.MaxInflightMsgs)) {
			t.Fatalf("seed %d: %+v rejected by ValidCluster", i, o)
		}
		if !ValidAddrs(addrs, o.Voters) {
			t.Fatalf("seed %d: voters %d rejected by ValidAddrs", i, o.Voters)
		}
	}
	if uint64(len("/var/lib/kvnet")) >= MaxDirLen {
		t.Fatal("a directory name rejected")
	}
	// each clause rejects
	for _, c := range []struct {
		name  string
		addrs []string
		v     uint64
		s, cs uint64
		inf   uint64
	}{
		{"duplicate address", []string{"127.0.1.1:7001", "127.0.1.1:7001"}, 1, 0, 4096, 4},
		{"malformed address", []string{"localhost:7001"}, 1, 0, 4096, 4},
		{"no voter", addrs, 0, 0, 4096, 4},
		{"too many voters", addrs[:2], 3, 0, 4096, 4},
		{"both size limits 0", addrs, 1, 0, 0, 4},
		{"no in-flight message", addrs, 1, 0, 4096, 0},
	} {
		if ValidCluster(c.addrs, c.v, c.s, c.cs, c.inf) {
			t.Fatalf("%s: accepted", c.name)
		}
	}
	if uint64(len(strings.Repeat("d", 10))) >= MaxDirLen {
		t.Fatal("short dir rejected")
	}
}
