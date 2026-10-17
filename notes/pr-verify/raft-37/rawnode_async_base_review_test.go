package raft

import (
	"fmt"
	"strings"
	"testing"
)

// TestReviewBaseAsyncRestartAboveDurableCommit: the same restart panic as
// TestNonLocalQuorumRestartAboveDurableLog, but with
// AsyncStorageWritesNonLocalQuorum = false (plain AsyncStorageWrites, the
// pre-PR behavior). The entry is durable locally; only the HardState carrying
// commit=12 is still in the (stalled) append thread when the apply thread
// applies 12.
func TestReviewBaseAsyncRestartAboveDurableCommit(t *testing.T) {
	c := newNLQCluster(t)
	for id := uint64(1); id <= 3; id++ {
		c.rns[id].asyncStorageWritesNonLocalQuorum = false
	}
	if err := c.rns[1].Campaign(); err != nil {
		t.Fatal(err)
	}
	c.stabilize()
	if err := c.rns[1].Propose([]byte("x")); err != nil {
		t.Fatal(err)
	}
	// Run until node 1's own log durably holds the new entry, then stall it.
	for i := 0; i < 100; i++ {
		if last, _ := c.stors[1].LastIndex(); last >= 12 {
			break
		}
		c.step()
	}
	c.stalled[1] = true
	c.stabilize()
	last, _ := c.stors[1].LastIndex()
	hs, _, _ := c.stors[1].InitialState()
	t.Logf("node 1: applied %d; durable last %d, durable commit %d", c.applied[1], last, hs.Commit)
	if c.applied[1] <= hs.Commit {
		t.Fatalf("applied %d not above durable commit %d", c.applied[1], hs.Commit)
	}
	cfg := nlqConfig(1, c.stors[1], c.applied[1])
	cfg.AsyncStorageWritesNonLocalQuorum = false
	msg := func() (msg string) {
		defer func() {
			if r := recover(); r != nil {
				msg = fmt.Sprint(r)
			}
		}()
		if _, err := NewRawNode(cfg); err != nil {
			return "error: " + err.Error()
		}
		return ""
	}()
	t.Logf("restart with Applied=%d: %q", c.applied[1], msg)
	if !strings.Contains(msg, "out of range") {
		t.Fatalf("no panic: %q", msg)
	}
}

// TestReviewNLQSnapshotAboveDurableLog: with the option, the applied index can
// exceed the local MemoryStorage's last index, so the usual
// "CreateSnapshot(applied)" (and Compact(applied)) on the apply side panic.
func TestReviewNLQSnapshotAboveDurableLog(t *testing.T) {
	c := newNLQCluster(t)
	if err := c.rns[1].Campaign(); err != nil {
		t.Fatal(err)
	}
	c.stabilize()
	c.stalled[1] = true
	if err := c.rns[1].Propose([]byte("x")); err != nil {
		t.Fatal(err)
	}
	c.stabilize()
	msg := func() (msg string) {
		defer func() {
			if r := recover(); r != nil {
				msg = fmt.Sprint(r)
			}
		}()
		_, err := c.stors[1].CreateSnapshot(c.applied[1], nil, nil)
		return fmt.Sprint(err)
	}()
	t.Logf("CreateSnapshot(%d): %q", c.applied[1], msg)
	if !strings.Contains(msg, "out of bound") {
		t.Fatalf("CreateSnapshot did not fail: %q", msg)
	}
}
