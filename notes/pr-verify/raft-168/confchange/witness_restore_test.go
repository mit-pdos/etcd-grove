package confchange

import (
	"testing"

	pb "go.etcd.io/raft/v3/raftpb"
	"go.etcd.io/raft/v3/tracker"
)

// A joint configuration in which the witness stays (here: adding voter 4 to
// voters 1 2 and witness 3) does not survive Restore of its own ConfState.
func TestWitnessRestoreJoint(t *testing.T) {
	chg := Changer{Tracker: tracker.MakeProgressTracker(10, 0), LastIndex: 10}
	cfg, trk, err := chg.Simple(pb.ConfChangeSingle{Type: pb.ConfChangeAddNode, NodeID: 1})
	must(t, err)
	chg.Tracker.Config, chg.Tracker.Progress = cfg, trk
	cfg, trk, err = chg.Simple(pb.ConfChangeSingle{Type: pb.ConfChangeAddNode, NodeID: 2})
	must(t, err)
	chg.Tracker.Config, chg.Tracker.Progress = cfg, trk
	cfg, trk, err = chg.Simple(pb.ConfChangeSingle{Type: pb.ConfChangeAddWitness, NodeID: 3})
	must(t, err)
	chg.Tracker.Config, chg.Tracker.Progress = cfg, trk
	cfg, trk, err = chg.EnterJoint(false, pb.ConfChangeSingle{Type: pb.ConfChangeAddNode, NodeID: 4})
	must(t, err)
	chg.Tracker.Config, chg.Tracker.Progress = cfg, trk
	cs := chg.Tracker.ConfState()
	t.Logf("live:     %s  ConfState %+v", chg.Tracker.Config, cs)

	cfg2, _, err := Restore(Changer{Tracker: tracker.MakeProgressTracker(10, 0), LastIndex: 10}, cs)
	must(t, err)
	t.Logf("restored: %s", cfg2)
	if cfg2.String() != chg.Tracker.Config.String() {
		t.Fatalf("Restore(ConfState()) differs from the live config:\n live     %s\n restored %s", chg.Tracker.Config, cfg2)
	}
}

func must(t *testing.T, err error) {
	t.Helper()
	if err != nil {
		t.Fatal(err)
	}
}
