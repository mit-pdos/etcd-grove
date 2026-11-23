package swift

import (
	"github.com/imdea-software/swiftpaxos/client"
	"github.com/imdea-software/swiftpaxos/state"
)

// GHOST (L2, the verification's linearization; notes/l2-design.md in the Lean project): ghost
// code, no behaviour change. Each replica step of the protocol's model is recorded, before any
// send that exposes it, as its words on the node's ghost (client.GhostStep: a prophecy's
// resolutions under a mutex, no-ops when the program runs). The words: the event's kind (4 to
// 11), then its fields; a ballot is a word, a command id two (client, sequence number), a
// command its op, key, value length and bytes, a list its length and its elements.

func ghostId(ws []uint64, id CommandId) []uint64 {
	return append(ws, uint64(uint32(id.ClientId)), uint64(uint32(id.SeqNum)))
}

func ghostIds(ws []uint64, ids []CommandId) []uint64 {
	ws = append(ws, uint64(len(ids)))
	for _, id := range ids {
		ws = ghostId(ws, id)
	}
	return ws
}

func ghostCmd(ws []uint64, c state.Command) []uint64 {
	ws = append(ws, uint64(c.Op), uint64(c.K), uint64(len(c.V)))
	for _, b := range c.V {
		ws = append(ws, uint64(b))
	}
	return ws
}

// ghostHandle: replica handles command id (c) in ballot b (GHOST).
func ghostHandle(b int32, id CommandId, c state.Command) {
	ws := []uint64{4, uint64(b)}
	ws = ghostId(ws, id)
	client.GhostStep(ghostCmd(ws, c))
}

// ghostPreaccept: replica pre-accepts id in ballot b with dependencies dep (GHOST).
func ghostPreaccept(b int32, id CommandId, dep []CommandId) {
	ws := []uint64{5, uint64(b)}
	ws = ghostId(ws, id)
	client.GhostStep(ghostIds(ws, dep))
}

// ghostAccept: replica accepts id in ballot b (GHOST).
func ghostAccept(b int32, id CommandId) {
	client.GhostStep([]uint64{6, uint64(b), uint64(uint32(id.ClientId)), uint64(uint32(id.SeqNum))})
}

// ghostCommit: replica commits id in ballot b (GHOST).
func ghostCommit(b int32, id CommandId) {
	client.GhostStep([]uint64{7, uint64(b), uint64(uint32(id.ClientId)), uint64(uint32(id.SeqNum))})
}

// ghostNewBallot: replica moves to ballot b (GHOST).
func ghostNewBallot(b int32) {
	client.GhostStep([]uint64{8, uint64(b)})
}

// ghostReport: replica reports m for m's ballot (GHOST).
func ghostReport(m *MNewLeaderAckN) {
	ws := []uint64{9, uint64(m.Ballot), uint64(m.Cballot), uint64(len(m.CmdIds))}
	for i := range m.CmdIds {
		ws = ghostId(ws, m.CmdIds[i])
		ws = append(ws, uint64(m.Phases[i]))
		ws = ghostCmd(ws, m.Cmds[i])
		ws = ghostIds(ws, m.Deps[i].Dep)
	}
	client.GhostStep(ws)
}

// ghostComputeSync: ballot b's leader computes its MSync from the reports msgs (GHOST).
func ghostComputeSync(b int32, msgs []interface{}) {
	ws := []uint64{10, uint64(b), uint64(len(msgs))}
	for _, m := range msgs {
		ws = append(ws, uint64(m.(*MNewLeaderAckN).Replica))
	}
	client.GhostStep(ws)
}

// ghostTakeSync: replica takes ballot b's MSync (GHOST).
func ghostTakeSync(b int32) {
	client.GhostStep([]uint64{11, uint64(b)})
}
