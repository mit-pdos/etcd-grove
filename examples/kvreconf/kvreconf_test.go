package kvreconf

import (
	"testing"
	"time"

	"github.com/anishathalye/porcupine"
	"github.com/mit-pdos/etcd-grove/examples/lintest"
	pb "go.etcd.io/raft/v3/raftpb"
)

func TestEncode(t *testing.T) {
	id, kind, key, val, ok := decode(encode(7, opPut, "k", "v"))
	if !ok || id != 7 || kind != opPut || key != "k" || val != "v" {
		t.Fatalf("decode(encode) = %d %d %q %q %v", id, kind, key, val, ok)
	}
	if _, _, _, _, ok := decode(nil); ok {
		t.Fatal("decode(nil) ok")
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

func single(t pb.ConfChangeType, id uint64) *pb.ConfChangeSingle {
	return &pb.ConfChangeSingle{Type: t.Enum(), NodeId: new(id)}
}

// TestValidConf checks validConf on the cases raft panics on and on some it accepts.
func TestValidConf(t *testing.T) {
	one := &pb.ConfState{Voters: []uint64{1}}
	two := &pb.ConfState{Voters: []uint64{1, 2}}
	joint := &pb.ConfState{Voters: []uint64{1, 3}, VotersOutgoing: []uint64{1, 2}}
	explicit := pb.ConfChangeTransitionJointExplicit.Enum()
	cases := []struct {
		cs   *pb.ConfState
		cc   *pb.ConfChangeV2
		want bool
	}{
		{nil, &pb.ConfChangeV2{Changes: []*pb.ConfChangeSingle{single(pb.ConfChangeAddNode, 1)}}, true},
		{one, &pb.ConfChangeV2{Changes: []*pb.ConfChangeSingle{single(pb.ConfChangeRemoveNode, 1)}}, false},
		{two, &pb.ConfChangeV2{Changes: []*pb.ConfChangeSingle{single(pb.ConfChangeRemoveNode, 1)}}, true},
		{two, &pb.ConfChangeV2{Changes: []*pb.ConfChangeSingle{single(pb.ConfChangeAddNode, 3), single(pb.ConfChangeAddNode, 4)}}, true},
		{two, &pb.ConfChangeV2{Transition: explicit, Changes: []*pb.ConfChangeSingle{single(pb.ConfChangeAddLearnerNode, 2)}}, true},
		{two, &pb.ConfChangeV2{}, false},
		{joint, &pb.ConfChangeV2{}, true},
		{joint, &pb.ConfChangeV2{Changes: []*pb.ConfChangeSingle{single(pb.ConfChangeAddNode, 4)}}, false},
		{joint, &pb.ConfChangeV2{Transition: explicit, Changes: []*pb.ConfChangeSingle{single(pb.ConfChangeAddNode, 4)}}, false},
		{one, &pb.ConfChangeV2{Transition: explicit, Changes: []*pb.ConfChangeSingle{single(pb.ConfChangeRemoveNode, 1)}}, false},
	}
	for i, tc := range cases {
		if got := validConf(tc.cs, tc.cc); got != tc.want {
			t.Errorf("case %d: validConf(%v, %v) = %v, want %v", i, tc.cs, tc.cc, got, tc.want)
		}
	}
}

func TestPutGetRead(t *testing.T) {
	c := StartCluster(Options{Voters: 3, MaxSizePerMsg: 1 << 20, MaxInflightMsgs: 256})
	defer c.Stop()
	if v := c.Get("k"); v != "" {
		t.Fatalf("initial Get = %q", v)
	}
	c.Put("k", "a")
	if v := c.Get("k"); v != "a" {
		t.Fatalf("Get after Put = %q", v)
	}
	if v := c.Read("k"); v != "a" {
		t.Fatalf("Read after Put = %q", v)
	}
}

func TestMain_(t *testing.T) {
	Main()
}

// TestRounds runs rounds of Main's test, each with its own random options, and checks that
// porcupine accepts each trace and that the members converge after each; over all the rounds,
// that the interactions the test is for happened: snapshots taken and installed at joint
// configurations and with learners, compactions, joint configurations entered, committed
// changes rejected as invalid.
func TestRounds(t *testing.T) {
	rounds := 10
	if testing.Short() {
		rounds = 2
	}
	var total Stats
	for i := 0; i < rounds; i++ {
		cfg := RandomConfig()
		res, c := Run(cfg, lintest.CounterClock())
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
		total.SnapshotsTakenJoint.Add(c.Stats.SnapshotsTakenJoint.Load())
		total.SnapshotsInstalledJoint.Add(c.Stats.SnapshotsInstalledJoint.Load())
		total.SnapshotsInstalledLearners.Add(c.Stats.SnapshotsInstalledLearners.Load())
		total.Compactions.Add(c.Stats.Compactions.Load())
		total.JointEntered.Add(c.Stats.JointEntered.Load())
		total.ConfChangesRejected.Add(c.Stats.ConfChangesRejected.Load())
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
	} {
		if n == 0 {
			t.Errorf("no %s in %d rounds", name, rounds)
		}
	}
}
