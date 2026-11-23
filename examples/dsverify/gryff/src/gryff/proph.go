package gryff

// Verification workaround (ghost code, D9; no Go behavior change): each replica's trace prophecy. A
// replica stores the package's prophecy (traceProph, D13) in NewReplica (r.proph) and resolves it,
// under r.mtx, with every event its run loop handles (EPaxosRMWHandler.Loop) and every instance its
// executor executes (Exec.strongconnect), as words: the event's kind, then the fields of the
// model's projection of the event, in order (gryff-verify GryffProof/Model/Codec.lean, evCodec; the
// table: notes/stage2-codec.md). A Go int32 or int8 is resolved as uint64(x) (sign-extended), a
// uint8 as uint64(x), a list (a []state.Command, a [DS]int32) as 1 before each element, then 0.
// primitive.NewProph and ProphId.ResolveU64 do nothing in Go.

import ( // verification workaround (ghost code, D9): trace prophecy
	"github.com/goose-lang/primitive" // verification workaround (ghost code, D13): trace prophecy
	"gryff/src/epaxosproto"           // verification workaround (ghost code, D9): trace prophecy
	"gryff/src/gryffproto"            // verification workaround (ghost code, D9): trace prophecy
	"gryff/src/state"                 // verification workaround (ghost code, D9): trace prophecy
) // verification workaround (ghost code, D9): trace prophecy

// verification workaround (ghost code, D13): the trace prophecy is created by the gryff package's
// initialization (every node that imports gryff creates one; only a replica node uses it, through
// NewReplica, which stores it in r.proph), so that a replica node holds its prediction before it
// registers with the master. primitive.NewProph does nothing in Go.
var traceProph primitive.ProphId // verification workaround (ghost code, D13): the node's trace prophecy

func init() { // verification workaround (ghost code, D13): the node's trace prophecy
	p := primitive.NewProph() // verification workaround (ghost code, D13): through a local variable (Goose's copy rule)
	traceProph = p            // verification workaround (ghost code, D13): the node's trace prophecy
} // verification workaround (ghost code, D13): the node's trace prophecy

const ( // verification workaround (ghost code, D9): trace prophecy
	evRead1            uint64 = 1  // verification workaround (ghost code, D9): trace prophecy
	evRead2            uint64 = 2  // verification workaround (ghost code, D9): trace prophecy
	evRead1Reply       uint64 = 3  // verification workaround (ghost code, D9): trace prophecy
	evRead2Reply       uint64 = 4  // verification workaround (ghost code, D9): trace prophecy
	evWrite1           uint64 = 5  // verification workaround (ghost code, D9): trace prophecy
	evWrite2           uint64 = 6  // verification workaround (ghost code, D9): trace prophecy
	evWrite1Reply      uint64 = 7  // verification workaround (ghost code, D9): trace prophecy
	evWrite2Reply      uint64 = 8  // verification workaround (ghost code, D9): trace prophecy
	evPreAccept        uint64 = 9  // verification workaround (ghost code, D9): trace prophecy
	evPreAcceptReply   uint64 = 10 // verification workaround (ghost code, D9): trace prophecy
	evPreAcceptOK      uint64 = 11 // verification workaround (ghost code, D9): trace prophecy
	evAccept           uint64 = 12 // verification workaround (ghost code, D9): trace prophecy
	evAcceptReply      uint64 = 13 // verification workaround (ghost code, D9): trace prophecy
	evCommit           uint64 = 14 // verification workaround (ghost code, D9): trace prophecy
	evPrepare          uint64 = 15 // verification workaround (ghost code, D9): trace prophecy
	evPrepareReply     uint64 = 16 // verification workaround (ghost code, D9): trace prophecy
	evExecuted         uint64 = 17 // verification workaround (ghost code, D9): trace prophecy
	evExecuteOverwrite uint64 = 18 // verification workaround (ghost code, D9): trace prophecy
	evRead             uint64 = 19 // verification workaround (ghost code, D9): trace prophecy
	evWrite            uint64 = 20 // verification workaround (ghost code, D9): trace prophecy
	evRMW              uint64 = 21 // verification workaround (ghost code, D9): trace prophecy
	evForceWrite       uint64 = 22 // verification workaround (ghost code, D9): trace prophecy
	evRecover          uint64 = 23 // verification workaround (ghost code, D9): trace prophecy
	evExec             uint64 = 24 // verification workaround (ghost code, D9): trace prophecy
) // verification workaround (ghost code, D9): trace prophecy

func (r *Replica) resolveTag(t *gryffproto.Tag) { // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(t.Ts))   // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(t.Cid))  // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(t.Rmwc)) // verification workaround (ghost code, D9): trace prophecy
} // verification workaround (ghost code, D9): trace prophecy

func (r *Replica) resolveValTag(vt *gryffproto.ValTag) { // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(vt.V)) // verification workaround (ghost code, D9): trace prophecy
	r.resolveTag(&vt.T)              // verification workaround (ghost code, D9): trace prophecy
} // verification workaround (ghost code, D9): trace prophecy

func (r *Replica) resolveDep(d *gryffproto.Dep) { // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(d.Key)) // verification workaround (ghost code, D9): trace prophecy
	r.resolveValTag(&d.Vt)            // verification workaround (ghost code, D9): trace prophecy
} // verification workaround (ghost code, D9): trace prophecy

func (r *Replica) resolveCmds(cmds []state.Command) { // verification workaround (ghost code, D9): trace prophecy
	for i := 0; i < len(cmds); i++ { // verification workaround (ghost code, D9): trace prophecy
		r.proph.ResolveU64(1)                        // verification workaround (ghost code, D9): trace prophecy
		r.proph.ResolveU64(uint64(cmds[i].Op))       // verification workaround (ghost code, D9): trace prophecy
		r.proph.ResolveU64(uint64(cmds[i].K))        // verification workaround (ghost code, D9): trace prophecy
		r.proph.ResolveU64(uint64(cmds[i].V))        // verification workaround (ghost code, D9): trace prophecy
		r.proph.ResolveU64(uint64(cmds[i].OldValue)) // verification workaround (ghost code, D9): trace prophecy
	} // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(0) // verification workaround (ghost code, D9): trace prophecy
} // verification workaround (ghost code, D9): trace prophecy

func (r *Replica) resolveDeps(deps [DS]int32) { // verification workaround (ghost code, D9): trace prophecy
	for i := 0; i < DS; i++ { // verification workaround (ghost code, D9): trace prophecy
		r.proph.ResolveU64(1)               // verification workaround (ghost code, D9): trace prophecy
		r.proph.ResolveU64(uint64(deps[i])) // verification workaround (ghost code, D9): trace prophecy
	} // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(0) // verification workaround (ghost code, D9): trace prophecy
} // verification workaround (ghost code, D9): trace prophecy

func (r *Replica) resolveRead1(m *gryffproto.Read1Proxied) { // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(evRead1)             // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(m.RequestId)) // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(m.ClientId))  // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(m.K))         // verification workaround (ghost code, D9): trace prophecy
	r.resolveDep(&m.D)                      // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(m.ReplicaId)) // verification workaround (ghost code, D9): trace prophecy
	r.resolveValTag(&m.Vt)                  // verification workaround (ghost code, D9): trace prophecy
} // verification workaround (ghost code, D9): trace prophecy

func (r *Replica) resolveRead2(m *gryffproto.Read2Proxied) { // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(evRead2)             // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(m.RequestId)) // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(m.ClientId))  // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(m.K))         // verification workaround (ghost code, D9): trace prophecy
	r.resolveValTag(&m.Vt)                  // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(m.ReplicaId)) // verification workaround (ghost code, D9): trace prophecy
} // verification workaround (ghost code, D9): trace prophecy

func (r *Replica) resolveRead1Reply(m *gryffproto.Read1Reply) { // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(evRead1Reply)        // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(m.RequestId)) // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(m.ClientId))  // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(m.ReplicaId)) // verification workaround (ghost code, D9): trace prophecy
	r.resolveValTag(&m.Vt)                  // verification workaround (ghost code, D9): trace prophecy
} // verification workaround (ghost code, D9): trace prophecy

func (r *Replica) resolveRead2Reply(m *gryffproto.Read2Reply) { // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(evRead2Reply)        // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(m.RequestId)) // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(m.ClientId))  // verification workaround (ghost code, D9): trace prophecy
} // verification workaround (ghost code, D9): trace prophecy

func (r *Replica) resolveWrite1(m *gryffproto.Write1Proxied) { // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(evWrite1)             // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(m.RequestId))  // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(m.ClientId))   // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(m.ForceWrite)) // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(m.K))          // verification workaround (ghost code, D9): trace prophecy
	r.resolveDep(&m.D)                       // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(m.ReplicaId))  // verification workaround (ghost code, D9): trace prophecy
} // verification workaround (ghost code, D9): trace prophecy

func (r *Replica) resolveWrite2(m *gryffproto.Write2Proxied) { // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(evWrite2)            // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(m.RequestId)) // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(m.ClientId))  // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(m.K))         // verification workaround (ghost code, D9): trace prophecy
	r.resolveValTag(&m.Vt)                  // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(m.ReplicaId)) // verification workaround (ghost code, D9): trace prophecy
} // verification workaround (ghost code, D9): trace prophecy

func (r *Replica) resolveWrite1Reply(m *gryffproto.Write1Reply) { // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(evWrite1Reply)       // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(m.RequestId)) // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(m.ClientId))  // verification workaround (ghost code, D9): trace prophecy
	r.resolveValTag(&m.Vt)                  // verification workaround (ghost code, D9): trace prophecy
} // verification workaround (ghost code, D9): trace prophecy

func (r *Replica) resolveWrite2Reply(m *gryffproto.Write2Reply) { // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(evWrite2Reply)       // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(m.RequestId)) // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(m.ClientId))  // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(m.Applied))   // verification workaround (ghost code, D9): trace prophecy
} // verification workaround (ghost code, D9): trace prophecy

func (r *Replica) resolvePreAccept(m *gryffproto.PreAccept) { // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(evPreAccept)        // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(m.LeaderId)) // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(m.Replica))  // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(m.Instance)) // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(m.Ballot))   // verification workaround (ghost code, D9): trace prophecy
	r.resolveCmds(m.Command)               // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(m.Seq))      // verification workaround (ghost code, D9): trace prophecy
	r.resolveDeps(m.Deps)                  // verification workaround (ghost code, D9): trace prophecy
	r.resolveValTag(&m.Base)               // verification workaround (ghost code, D9): trace prophecy
} // verification workaround (ghost code, D9): trace prophecy

func (r *Replica) resolvePreAcceptReply(m *gryffproto.PreAcceptReply) { // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(evPreAcceptReply)   // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(m.Replica))  // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(m.Instance)) // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(m.OK))       // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(m.Ballot))   // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(m.Seq))      // verification workaround (ghost code, D9): trace prophecy
	r.resolveDeps(m.Deps)                  // verification workaround (ghost code, D9): trace prophecy
	r.resolveValTag(&m.Base)               // verification workaround (ghost code, D9): trace prophecy
} // verification workaround (ghost code, D9): trace prophecy

func (r *Replica) resolvePreAcceptOK(m *epaxosproto.PreAcceptOK) { // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(evPreAcceptOK)      // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(m.Instance)) // verification workaround (ghost code, D9): trace prophecy
} // verification workaround (ghost code, D9): trace prophecy

func (r *Replica) resolveAccept(m *gryffproto.EAccept) { // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(evAccept)           // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(m.LeaderId)) // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(m.Replica))  // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(m.Instance)) // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(m.Ballot))   // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(m.Seq))      // verification workaround (ghost code, D9): trace prophecy
	r.resolveDeps(m.Deps)                  // verification workaround (ghost code, D9): trace prophecy
	r.resolveCmds(m.Command)               // verification workaround (ghost code, D9): trace prophecy
	r.resolveValTag(&m.Base)               // verification workaround (ghost code, D9): trace prophecy
} // verification workaround (ghost code, D9): trace prophecy

func (r *Replica) resolveAcceptReply(m *epaxosproto.AcceptReply) { // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(evAcceptReply)      // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(m.Replica))  // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(m.Instance)) // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(m.OK))       // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(m.Ballot))   // verification workaround (ghost code, D9): trace prophecy
} // verification workaround (ghost code, D9): trace prophecy

func (r *Replica) resolveCommit(m *gryffproto.ECommit) { // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(evCommit)           // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(m.Replica))  // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(m.Instance)) // verification workaround (ghost code, D9): trace prophecy
	r.resolveCmds(m.Command)               // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(m.Seq))      // verification workaround (ghost code, D9): trace prophecy
	r.resolveDeps(m.Deps)                  // verification workaround (ghost code, D9): trace prophecy
	r.resolveValTag(&m.Base)               // verification workaround (ghost code, D9): trace prophecy
} // verification workaround (ghost code, D9): trace prophecy

func (r *Replica) resolvePrepare(m *epaxosproto.Prepare) { // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(evPrepare)          // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(m.LeaderId)) // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(m.Replica))  // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(m.Instance)) // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(m.Ballot))   // verification workaround (ghost code, D9): trace prophecy
} // verification workaround (ghost code, D9): trace prophecy

func (r *Replica) resolvePrepareReply(m *gryffproto.PrepareReply) { // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(evPrepareReply)       // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(m.AcceptorId)) // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(m.Replica))    // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(m.Instance))   // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(m.OK))         // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(m.Ballot))     // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(m.VBallot))    // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(m.Status))     // verification workaround (ghost code, D9): trace prophecy
	r.resolveCmds(m.Command)                 // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(m.Seq))        // verification workaround (ghost code, D9): trace prophecy
	r.resolveDeps(m.Deps)                    // verification workaround (ghost code, D9): trace prophecy
	r.resolveValTag(&m.Base)                 // verification workaround (ghost code, D9): trace prophecy
} // verification workaround (ghost code, D9): trace prophecy

func (r *Replica) resolveExecuted(m *gryffproto.Executed) { // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(evExecuted)         // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(m.Replica))  // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(m.Instance)) // verification workaround (ghost code, D9): trace prophecy
} // verification workaround (ghost code, D9): trace prophecy

func (r *Replica) resolveExecuteOverwrite(m *ExecuteOverwrite) { // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(evExecuteOverwrite) // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(m.V))        // verification workaround (ghost code, D9): trace prophecy
	r.resolveTag(m.T)                      // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(m.Leader))   // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(m.Slot))     // verification workaround (ghost code, D9): trace prophecy
} // verification workaround (ghost code, D9): trace prophecy

func (r *Replica) resolveRead(m *gryffproto.Read) { // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(evRead)              // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(m.RequestId)) // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(m.ClientId))  // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(m.K))         // verification workaround (ghost code, D9): trace prophecy
	r.resolveDep(&m.D)                      // verification workaround (ghost code, D9): trace prophecy
} // verification workaround (ghost code, D9): trace prophecy

func (r *Replica) resolveWrite(m *gryffproto.Write) { // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(evWrite)             // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(m.RequestId)) // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(m.ClientId))  // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(m.K))         // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(m.V))         // verification workaround (ghost code, D9): trace prophecy
	r.resolveDep(&m.D)                      // verification workaround (ghost code, D9): trace prophecy
} // verification workaround (ghost code, D9): trace prophecy

func (r *Replica) resolveRMW(m *gryffproto.RMW) { // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(evRMW)               // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(m.RequestId)) // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(m.ClientId))  // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(m.K))         // verification workaround (ghost code, D9): trace prophecy
	r.resolveDep(&m.D)                      // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(m.OldValue))  // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(m.NewValue))  // verification workaround (ghost code, D9): trace prophecy
} // verification workaround (ghost code, D9): trace prophecy

func (r *Replica) resolveForceWrite() { // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(evForceWrite) // verification workaround (ghost code, D9): trace prophecy
} // verification workaround (ghost code, D9): trace prophecy

func (r *Replica) resolveRecover(q int32, i int32) { // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(evRecover) // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(q)) // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(i)) // verification workaround (ghost code, D9): trace prophecy
} // verification workaround (ghost code, D9): trace prophecy

func (r *Replica) resolveExec(q int32, i int32) { // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(evExec)    // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(q)) // verification workaround (ghost code, D9): trace prophecy
	r.proph.ResolveU64(uint64(i)) // verification workaround (ghost code, D9): trace prophecy
} // verification workaround (ghost code, D9): trace prophecy
