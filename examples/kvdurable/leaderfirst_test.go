package kvdurable

import (
	"testing"

	"go.etcd.io/raft/v3"
	pb "go.etcd.io/raft/v3/raftpb"
)

// TestLeaderReadyKeepsTermVote checks what lets a leader send a Ready's messages before writing it
// (Replica.run, as etcd does): a Ready handed out while the node's last reported role is leader
// (its SoftState, or the last one reported) never changes the term or the vote, so that every
// promise its messages carry (the term, the vote) was written by an earlier Ready, and its own
// acknowledgement of the Ready's entries waits for Advance. Clusters of RawNodes on MemoryStorage
// (synchronous writes, each Ready written before its Advance) are stepped at random: messages
// delivered, dropped, duplicated and reordered; ticks; campaigns; leadership transfers (whose
// MsgTimeoutNow starts a forced campaign); proposals; with pre-vote and check-quorum at random.
// It also checks that a Ready whose role changes to leader comes with no term or vote change.
func TestLeaderReadyKeepsTermVote(t *testing.T) {
	runs := 200
	if testing.Short() {
		runs = 20
	}
	var leaderReadys, became uint64
	for run := 0; run < runs; run++ {
		size := 1 + below(5)
		preVote, checkQuorum := oneIn(2), oneIn(2)
		var ids []uint64
		for id := uint64(1); id <= size; id++ {
			ids = append(ids, id)
		}
		type node struct {
			rn   *raft.RawNode
			st   *raft.MemoryStorage
			lead bool
		}
		nodes := map[uint64]*node{}
		for _, id := range ids {
			st := raft.NewMemoryStorage()
			st.ApplySnapshot(&pb.Snapshot{Metadata: &pb.SnapshotMetadata{ConfState: &pb.ConfState{Voters: ids}}})
			rn, err := raft.NewRawNode(&raft.Config{ID: id, ElectionTick: 10, HeartbeatTick: 1, Storage: st,
				MaxSizePerMsg: 1 << 20, MaxInflightMsgs: 256, PreVote: preVote, CheckQuorum: checkQuorum,
				Logger: quietLogger{}})
			if err != nil {
				t.Fatal(err)
			}
			nodes[id] = &node{rn: rn, st: st}
		}
		var inflight []*pb.Message
		for step := 0; step < 2000; step++ {
			id := ids[below(size)]
			n := nodes[id]
			switch below(20) {
			case 0:
				n.rn.Campaign()
			case 1:
				n.rn.TransferLeader(ids[below(size)])
			case 2, 3:
				n.rn.Propose([]byte("x"))
			case 4, 5, 6, 7:
				n.rn.Tick()
			default:
				if len(inflight) > 0 {
					i := below(uint64(len(inflight)))
					m := inflight[i]
					if !oneIn(8) {
						inflight = append(inflight[:i], inflight[i+1:]...)
					}
					if !oneIn(10) {
						nodes[m.GetTo()].rn.Step(copyMsg(m))
					}
				}
			}
			for _, id := range ids {
				n := nodes[id]
				for n.rn.HasReady() {
					prev, _, _ := n.st.InitialState()
					rd := n.rn.Ready()
					if rd.SoftState != nil {
						wasLead := n.lead
						n.lead = rd.SoftState.RaftState == raft.StateLeader
						if n.lead && !wasLead {
							became++
						}
					}
					hs := rd.HardState
					if n.lead {
						leaderReadys++
						if !raft.IsEmptyHardState(hs) && (hs.GetTerm() != prev.GetTerm() || hs.GetVote() != prev.GetVote()) {
							t.Fatalf("run %d: node %d's Ready at role leader changes the hard state from %v to %v",
								run, id, prev, hs)
						}
					}
					if !raft.IsEmptySnap(rd.Snapshot) {
						n.st.ApplySnapshot(rd.Snapshot)
					}
					if !raft.IsEmptyHardState(hs) {
						n.st.SetHardState(hs)
					}
					n.st.Append(rd.Entries)
					for _, m := range rd.Messages {
						if m.GetTo() != id {
							inflight = append(inflight, copyMsg(m))
						}
					}
					n.rn.Advance(rd)
				}
			}
		}
	}
	t.Logf("%d Readys at role leader, %d becoming leader: no term or vote change", leaderReadys, became)
	if became == 0 {
		t.Fatal("no node became leader")
	}
}
