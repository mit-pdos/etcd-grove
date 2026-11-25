package kvraft

import (
	"strings"
	"testing"
	"time"
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
	if uint64(len("/var/lib/kvraft")) >= MaxDirLen {
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

// TestRunNodeUDPValidation is TestRandomOptionsValid's counterpart for RunNodeUDP (kvraft-udp's replica),
// which runs RunNode's checks, in the same order: on a configuration they reject it returns at once
// (each clause shown), and on one they accept every replica's own address is one openUDP can bind
// (udpAddr succeeds on every address ValidCluster accepts), so openUDP's panic is unreachable.
func TestRunNodeUDPValidation(t *testing.T) {
	addrs := "127.0.1.1:7001,127.0.1.2:7001,127.0.1.3:7001"
	for _, c := range []struct {
		name  string
		id    uint64
		addrs string
		dir   string
		v     uint64
		cs    uint64
	}{
		{"malformed address", 1, "localhost:7001", t.TempDir(), 1, 4096},
		{"duplicate address", 1, "127.0.1.1:7001,127.0.1.1:7001", t.TempDir(), 1, 4096},
		{"no voter", 1, addrs, t.TempDir(), 0, 4096},
		{"both size limits 0", 1, addrs, t.TempDir(), 1, 0},
		{"id 0", 0, addrs, t.TempDir(), 1, 4096},
		{"id past the replicas", 4, addrs, t.TempDir(), 1, 4096},
	} {
		done := make(chan struct{})
		go func() {
			RunNodeUDP(c.id, c.addrs, c.dir, c.v, true, true, true, 0, c.cs, 4)
			close(done)
		}()
		select {
		case <-done:
		case <-time.After(10 * time.Second):
			t.Fatalf("%s: RunNodeUDP did not return", c.name)
		}
	}
	for i := 0; i < 10000; i++ {
		o := RandomOptions()
		as := []string{"127.0.1.1:7001", "127.0.1.2:7001", "127.0.1.3:7001", "127.0.1.4:7001",
			"127.0.1.5:7001", "127.0.1.6:7001", "127.0.1.7:7001", "127.0.1.8:7001", "127.0.1.9:7001"}
		if !ValidCluster(as, o.Voters, o.MaxSizePerMsg, o.MaxCommittedSizePerReady, uint64(o.MaxInflightMsgs)) {
			t.Fatalf("seed %d: %+v rejected by ValidCluster", i, o)
		}
		for _, a := range as {
			if _, ok := udpAddr(a); !ok {
				t.Fatalf("seed %d: %s accepted by ValidCluster but not by udpAddr", i, a)
			}
		}
	}
}
