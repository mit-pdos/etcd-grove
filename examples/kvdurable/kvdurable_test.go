package kvdurable

import (
	"sync/atomic"
	"testing"
	"time"

	"github.com/anishathalye/porcupine"
	"github.com/mit-pdos/etcd-grove/examples/lintest"
	"go.etcd.io/raft/v3"
	pb "go.etcd.io/raft/v3/raftpb"
	"google.golang.org/protobuf/proto"
)

func TestEncode(t *testing.T) {
	id, kind, key, val, ok := decode(encode(7, opPut, "k", "v"))
	if !ok || id != 7 || kind != opPut || key != "k" || val != "v" {
		t.Fatalf("decode(encode) = %d %d %q %q %v", id, kind, key, val, ok)
	}
	r, seq, key, ok := decodeReadCtx(readCtx(3, 9, "x"))
	if !ok || r != 3 || seq != 9 || key != "x" {
		t.Fatalf("decodeReadCtx(readCtx) = %d %d %q %v", r, seq, key, ok)
	}
	kv := map[string]string{"a": "1", "b": ""}
	ops := map[string]string{string(encode(1, opGet, "a", "")): "1"}
	kv2, ops2, ok := decodeState(encodeState(kv, ops))
	if !ok || len(kv2) != 2 || kv2["a"] != "1" || len(ops2) != 1 {
		t.Fatalf("decodeState(encodeState) = %v %v %v", kv2, ops2, ok)
	}
}

type atomicU = atomic.Uint64

func ent(term, index uint64, data string) *pb.Entry {
	return &pb.Entry{Term: new(term), Index: new(index), Type: pb.EntryNormal.Enum(), Data: []byte(data)}
}

// sameStorage says whether a and b hold the same contents: hard state, snapshot, log start and
// entries.
func sameStorage(t *testing.T, a, b *Storage) {
	t.Helper()
	ha, _, _ := a.MemoryStorage.InitialState()
	hb, _, _ := b.MemoryStorage.InitialState()
	if ha.GetTerm() != hb.GetTerm() || ha.GetVote() != hb.GetVote() || ha.GetCommit() != hb.GetCommit() {
		t.Fatalf("hard state %v, restored %v", ha, hb)
	}
	sa, _ := a.MemoryStorage.Snapshot()
	sb, _ := b.MemoryStorage.Snapshot()
	if sa.GetMetadata().GetIndex() != sb.GetMetadata().GetIndex() || sa.GetMetadata().GetTerm() != sb.GetMetadata().GetTerm() ||
		string(sa.GetData()) != string(sb.GetData()) ||
		(sa.GetMetadata().GetIndex() != 0 && !proto.Equal(pb.EnsureConfState(sa.GetMetadata().GetConfState()), sb.GetMetadata().GetConfState())) {
		t.Fatalf("snapshot %v, restored %v", sa, sb)
	}
	fa, _ := a.FirstIndex()
	fb, _ := b.FirstIndex()
	la, _ := a.LastIndex()
	lb, _ := b.LastIndex()
	ta, _ := a.Term(fa - 1)
	tb, _ := b.Term(fb - 1)
	if fa != fb || la != lb || ta != tb {
		t.Fatalf("log [%d, %d] at term %d, restored [%d, %d] at term %d", fa, la, ta, fb, lb, tb)
	}
	for i := fa; i <= la; i++ {
		ea, _ := a.Entries(i, i+1, ^uint64(0))
		eb, _ := b.Entries(i, i+1, ^uint64(0))
		if !proto.Equal(ea[0], eb[0]) {
			t.Fatalf("entry %d: %v, restored %v", i, ea[0], eb[0])
		}
	}
	if !proto.Equal(a.InitialStateConf(), b.InitialStateConf()) {
		t.Fatalf("initial configuration %v, restored %v", a.InitialStateConf(), b.InitialStateConf())
	}
}

// InitialStateConf is the configuration InitialState answers.
func (s *Storage) InitialStateConf() *pb.ConfState {
	_, cs, _ := s.InitialState()
	return cs
}

// TestStorageRoundTrip checks that openStorage restores what encode wrote, and so that the image
// encode writes holds the MemoryStorage's contents: an empty storage, one with entries and a hard
// state, one with a snapshot taken above its log's start, one compacted below its snapshot, one
// that installed a snapshot, and after appends that overwrite the log's tail or start below its
// start; and that the image answers out-of-date snapshots and compactions as MemoryStorage does.
func TestStorageRoundTrip(t *testing.T) {
	boot := &pb.ConfState{Voters: []uint64{1, 2, 3}}
	check := func(name string, s *Storage) {
		t.Run(name, func(t *testing.T) {
			r, good := openStorage(boot, s.encode())
			if !good {
				t.Fatal("openStorage: not good")
			}
			sameStorage(t, s, r)
			if string(r.encode()) != string(s.encode()) {
				t.Fatal("the restored image differs")
			}
		})
	}
	fresh := func() *Storage { return newStorage(boot) }
	check("empty", fresh())

	s := fresh()
	s.Append([]*pb.Entry{ent(1, 1, "a"), ent(1, 2, ""), ent(2, 3, "c"), ent(2, 4, "d"), ent(3, 5, "e")})
	s.SetHardState(&pb.HardState{Term: new(uint64(3)), Vote: new(uint64(2)), Commit: new(uint64(4))})
	check("entries", s)

	joint := &pb.ConfState{Voters: []uint64{1, 4}, VotersOutgoing: []uint64{1, 2, 3}, LearnersNext: []uint64{2},
		AutoLeave: new(true)}
	if err := s.CreateSnapshot(3, joint, []byte("state")); err != nil {
		t.Fatal(err)
	}
	check("snapshot", s)
	if err := s.Compact(2); err != nil {
		t.Fatal(err)
	}
	check("compacted below the snapshot", s)
	if err := s.Compact(3); err != nil {
		t.Fatal(err)
	}
	check("compacted at the snapshot", s)

	s2 := fresh()
	s2.ApplySnapshot(&pb.Snapshot{Metadata: &pb.SnapshotMetadata{Index: new(uint64(7)), Term: new(uint64(4)),
		ConfState: &pb.ConfState{Voters: []uint64{2}, Learners: []uint64{5}}}, Data: []byte("x")})
	s2.SetHardState(&pb.HardState{Term: new(uint64(4)), Commit: new(uint64(7))})
	s2.Append([]*pb.Entry{ent(4, 8, "h")})
	check("installed snapshot", s2)

	s2.Append([]*pb.Entry{ent(4, 9, "i"), ent(4, 10, "j"), ent(4, 11, "k")})
	s2.Append([]*pb.Entry{ent(5, 10, "J")})
	check("tail overwritten", s2)
	s2.Append([]*pb.Entry{ent(4, 6, ""), ent(4, 7, ""), ent(4, 8, "h"), ent(6, 9, "I")})
	check("appended from below the start", s2)
	s2.Append([]*pb.Entry{ent(3, 5, ""), ent(3, 6, "")})
	check("appended below the start", s2)
	if err := s2.CreateSnapshot(9, nil, []byte("y")); err != nil {
		t.Fatal(err)
	}
	check("snapshot of the old configuration", s2)
	if err := s2.CreateSnapshot(8, nil, nil); err != raft.ErrSnapOutOfDate {
		t.Fatalf("CreateSnapshot below the snapshot: %v", err)
	}
	if err := s2.Compact(7); err != raft.ErrCompacted {
		t.Fatalf("Compact at the log's start: %v", err)
	}
	if err := s2.ApplySnapshot(&pb.Snapshot{Metadata: &pb.SnapshotMetadata{Index: new(uint64(9)), Term: new(uint64(6))}}); err != raft.ErrSnapOutOfDate {
		t.Fatalf("ApplySnapshot at the snapshot: %v", err)
	}
	check("after the refused changes", s2)

	if _, good := openStorage(boot, []byte{1, 2, 3}); good {
		t.Fatal("openStorage of garbage: good")
	}
}

func TestPutGetRead(t *testing.T) {
	c := StartCluster(Options{Voters: 3, MaxSizePerMsg: 1 << 20, MaxInflightMsgs: 256}, t.TempDir())
	defer c.Stop()
	if v := c.Get("k"); v != "" {
		t.Fatalf("initial Get = %q", v)
	}
	c.Put("k", "a")
	if v := c.Get("k"); v != "a" {
		t.Fatalf("Get after Put = %q", v)
	}
	for _, r := range c.all() {
		c.restart(r.id)
	}
	if v := c.Read("k"); v != "a" {
		t.Fatalf("Read after Put and restarts = %q", v)
	}
	if v := c.Get("k"); v != "a" {
		t.Fatalf("Get after Put and restarts = %q", v)
	}
}

func TestMain_(t *testing.T) {
	Main(t.TempDir())
}

// TestRounds runs rounds of Main's test, each with its own random options, and checks that
// porcupine accepts each trace and that the members converge after each; over all the rounds,
// that the interactions the test is for happened: kvreconf's (snapshots taken and installed at
// joint configurations and with learners, compactions, joint configurations entered, committed
// changes rejected as invalid) and durability's (crashes, restarts from a snapshot and with
// Config.Applied below it, covered entries skipped, a leader's messages sent before its write, a
// commit-only hard state left unwritten).
func TestRounds(t *testing.T) {
	rounds := 10
	if testing.Short() {
		rounds = 2
	}
	var total Stats
	for i := 0; i < rounds; i++ {
		cfg := RandomConfig()
		res, c := Run(cfg, lintest.CounterClock(), t.TempDir())
		err := c.Converged(20 * time.Second)
		var dump string
		if err != nil {
			dump = c.Dump()
		}
		c.Stop()
		t.Logf("round %d (%+v): %v; %v", i+1, cfg.Options, res, &c.Stats)
		if res != porcupine.Ok {
			t.Fatal("porcupine rejected the trace")
		}
		if err != nil {
			t.Fatalf("%v\n%s", err, dump)
		}
		for _, p := range []struct{ to, from *atomicU }{
			{&total.SnapshotsTakenJoint, &c.Stats.SnapshotsTakenJoint},
			{&total.SnapshotsInstalledJoint, &c.Stats.SnapshotsInstalledJoint},
			{&total.SnapshotsInstalledLearners, &c.Stats.SnapshotsInstalledLearners},
			{&total.Compactions, &c.Stats.Compactions},
			{&total.JointEntered, &c.Stats.JointEntered},
			{&total.ConfChangesRejected, &c.Stats.ConfChangesRejected},
			{&total.Crashes, &c.Stats.Crashes},
			{&total.RestartsFromSnapshot, &c.Stats.RestartsFromSnapshot},
			{&total.RestartsAppliedBelow, &c.Stats.RestartsAppliedBelow},
			{&total.EntriesSkipped, &c.Stats.EntriesSkipped},
			{&total.LeaderSentFirst, &c.Stats.LeaderSentFirst},
			{&total.CommitUnwritten, &c.Stats.CommitUnwritten},
		} {
			p.to.Add(p.from.Load())
		}
	}
	if testing.Short() {
		return
	}
	for name, n := range map[string]uint64{
		"snapshots taken at a joint configuration":     total.SnapshotsTakenJoint.Load(),
		"snapshots installed at a joint configuration": total.SnapshotsInstalledJoint.Load(),
		"snapshots installed with learners":            total.SnapshotsInstalledLearners.Load(),
		"compactions":                                  total.Compactions.Load(),
		"joint configurations entered":                 total.JointEntered.Load(),
		"committed changes rejected":                   total.ConfChangesRejected.Load(),
		"crashes":                                      total.Crashes.Load(),
		"restarts from a snapshot":                     total.RestartsFromSnapshot.Load(),
		"restarts with Applied below the snapshot":     total.RestartsAppliedBelow.Load(),
		"covered entries skipped":                      total.EntriesSkipped.Load(),
		"leader messages sent before the write":        total.LeaderSentFirst.Load(),
		"commit-only hard states left unwritten":       total.CommitUnwritten.Load(),
	} {
		if n == 0 {
			t.Errorf("no %s in %d rounds", name, rounds)
		}
	}
}
