package durablekv

import (
	"fmt"
	"os"
	"path/filepath"
	"testing"
	"time"

	"github.com/anishathalye/porcupine"
	"github.com/mit-pdos/etcd-grove/examples/lintest"
	pb "go.etcd.io/raft/v3/raftpb"
)

// TestCheck runs the randomized linearizability test with replicas crashing and restarting.
func TestCheck(t *testing.T) {
	for i := 0; i < 3; i++ {
		c := StartCluster(t.TempDir(), []uint64{1, 2, 3})
		r := Check(c, lintest.MonotonicClock(), 8, 40, 20*time.Millisecond)
		c.Stop()
		if r != porcupine.Ok {
			t.Fatalf("round %d: porcupine answered %v", i, r)
		}
	}
}

// TestMain runs Main, the program a proof would be about.
func TestMainProgram(t *testing.T) {
	Main(t.TempDir())
}

// TestRestartCluster writes enough to take several snapshots, with a replica restarting along
// the way, then stops every replica and starts the cluster again on its directory: the store's
// contents survive, and the operations of the new client are not mistaken for the old one's.
func TestRestartCluster(t *testing.T) {
	dir := t.TempDir()
	c := StartCluster(dir, []uint64{1, 2, 3})
	want := ""
	for i := 0; i < 3*snapEvery; i++ {
		v := fmt.Sprintf("%d,", i)
		c.Append(uint64(i%3+1), "k", v)
		want += v
		if i%50 == 25 {
			c.Restart(uint64(i/50%3 + 1))
		}
	}
	c.Put(1, "p", "x")
	c.Stop()
	for _, id := range []uint64{1, 2, 3} {
		if _, err := os.Stat(filepath.Join(dir, fmt.Sprintf("replica-%d", id))); err != nil {
			t.Fatalf("replica %d's file: %v", id, err)
		}
	}

	c2 := StartCluster(dir, []uint64{1, 2, 3})
	defer c2.Stop()
	if c2.epoch != c.epoch+1 {
		t.Fatalf("epoch %d after %d", c2.epoch, c.epoch)
	}
	for _, id := range []uint64{1, 2, 3} {
		if got := c2.Get(id, "k"); got != want {
			t.Fatalf("Get k through %d after the restart: %q, want %q", id, got, want)
		}
	}
	// the new client's first Put has the old one's first sequence number
	c2.Put(2, "p", "y")
	if got := c2.Get(3, "p"); got != "y" {
		t.Fatalf("Get p: %q, want y", got)
	}
}

// TestStorageRoundTrip checks that OpenStorage reads back what Encode wrote, compacted log
// and snapshot included.
func TestStorageRoundTrip(t *testing.T) {
	voters := []uint64{1, 2, 3}
	s, _ := OpenStorage(voters, "", false)
	var ents []*pb.Entry
	for i := uint64(1); i <= 30; i++ {
		ents = append(ents, &pb.Entry{Term: new(uint64(2)), Index: new(i), Data: []byte{byte(i)}})
	}
	s.Append(ents)
	s.SetHardState(&pb.HardState{Term: new(uint64(2)), Vote: new(uint64(1)), Commit: new(uint64(25))})
	s.CreateSnapshot(20, &pb.ConfState{Voters: voters}, encodeState(map[string]string{"a": "1"}, map[string]string{"op": "1"}))
	s.Compact(15)

	s2, good := OpenStorage(voters, string(s.Encode()), true)
	if !good {
		t.Fatal("OpenStorage rejected Encode's output")
	}
	hs, _, _ := s2.InitialState()
	if hs.GetTerm() != 2 || hs.GetVote() != 1 || hs.GetCommit() != 25 {
		t.Fatalf("hard state %v", hs)
	}
	if s2.SnapshotIndex() != 20 {
		t.Fatalf("snapshot index %d", s2.SnapshotIndex())
	}
	snap, _ := s2.Snapshot()
	kv, ops, ok := decodeState(snap.GetData())
	if !ok || kv["a"] != "1" || ops["op"] != "1" {
		t.Fatalf("snapshot data %v %v %v", kv, ops, ok)
	}
	first, _ := s2.FirstIndex()
	last, _ := s2.LastIndex()
	if first != 21 || last != 30 {
		t.Fatalf("entries [%d, %d]", first, last)
	}
	es, _ := s2.Entries(first, last+1, ^uint64(0))
	for _, e := range es {
		if e.GetData()[0] != byte(e.GetIndex()) {
			t.Fatalf("entry %v", e)
		}
	}
	if _, good := OpenStorage(voters, "junk", true); good {
		t.Fatal("OpenStorage accepted junk")
	}
}
