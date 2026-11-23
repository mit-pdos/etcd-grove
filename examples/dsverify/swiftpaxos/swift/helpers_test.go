package swift

import (
	"bufio"
	"testing"

	"github.com/imdea-software/swiftpaxos/dlog"
	"github.com/imdea-software/swiftpaxos/replica"
	"github.com/imdea-software/swiftpaxos/replica/defs"
	fastrpc "github.com/imdea-software/swiftpaxos/rpc"
	"github.com/imdea-software/swiftpaxos/state"
	cmap "github.com/orcaman/concurrent-map"
)

// newTestReplica builds a replica in memory, without network: the batcher's
// and the sender's channels are buffered and nobody reads them (a test may),
// there is no reply channel goroutine unless dreply is set. With
// MaxDescRoutines = 0 (seqDescs) every descriptor is handled by the calling
// goroutine, so a test drives the handlers deterministically.
func newTestReplica(t *testing.T, n int, id int32, ballot int32, dreply bool) *Replica {
	rr := &replica.Replica{
		Logger:        &dlog.Logger{},
		N:             n,
		F:             (n - 1) / 2,
		Id:            id,
		Alive:         make([]bool, n),
		ClientWriters: make(map[int32]*bufio.Writer),
		State:         state.InitState(),
		ProposeChan:   make(chan *defs.GPropose, 1000),
		Exec:          true,
		Dreply:        dreply,
	}
	for i := range rr.Alive {
		rr.Alive[i] = true
	}
	r := &Replica{
		Replica:         rr,
		ballot:          ballot,
		cballot:         ballot,
		status:          NORMAL,
		cmdDescs:        cmap.New(),
		delivered:       cmap.New(),
		keys:            make(map[state.Key]keyInfo),
		hlog:            make(map[state.Key]*HashLog),
		pendingHashUpds: make(map[CommandId]*UpdateEntry),
		history:         make([]commandStaticDesc, 1000),
		optExec:         true,
		deliverChan:     make(chan CommandId, 1000),
		recover:         make(chan int32, 8),
		proposes:        make(map[CommandId]*defs.GPropose),
		proposeDeps:     make(map[CommandId]Dep),
		slowAddrs:       make(map[string]struct{}),
		accepted:        make(map[CommandId]struct{}),
		waiting:         make(map[CommandId][]CommandId),
		recheckChan:     make(chan CommandId, 1000),
	}
	r.SQ = replica.NewMajorityOf(n)
	qs, err := replica.NewQuorumSystem(n/2+1, rr, "")
	if err != nil {
		t.Fatal(err)
	}
	r.qs = qs
	r.fixedMajority = true
	r.FQ = qs.AQ(ballot)
	r.batcher = &Batcher{
		fastAcks:      make(chan BatcherOp, 1000),
		lightSlowAcks: make(chan BatcherOp, 1000),
	}
	r.sender = make(replica.Sender, 1000)
	if dreply {
		r.repchan = NewReplyChan(r)
	}
	return r
}

// seqDescs makes every descriptor sequential for the test's duration.
func seqDescs(t *testing.T) {
	old := MaxDescRoutines
	MaxDescRoutines = 0
	t.Cleanup(func() { MaxDescRoutines = old })
}

func cid(c, s int32) CommandId { return CommandId{ClientId: c, SeqNum: s} }

func put(c CommandId, k int64, v string) *defs.GPropose {
	return &defs.GPropose{Propose: &defs.Propose{CommandId: c.SeqNum, ClientId: c.ClientId,
		Command: state.Command{Op: state.PUT, K: state.Key(k), V: state.Value(v)}}}
}

func get(c CommandId, k int64) *defs.GPropose {
	return &defs.GPropose{Propose: &defs.Propose{CommandId: c.SeqNum, ClientId: c.ClientId,
		Command: state.Command{Op: state.GET, K: state.Key(k), V: state.NIL()}}}
}

// propose does what run's propose case does for one proposal.
func propose(r *Replica, p *defs.GPropose) {
	r.ProposeChan <- p
	runOnce(r)
}

// runOnce handles one message the way run's select does, for the channels a
// test feeds (proposals, deliveries, acks).
func runOnce(r *Replica) {
	select {
	case p := <-r.ProposeChan:
		r.handleProposal(p)
	case id := <-r.recheckChan:
		r.getCmdDesc(id, "recheck", nil)
	default:
	}
	r.drainRechecks()
}

// withCs gives r its message channels (initCs: large buffers, only for the
// tests that use them).
func withCs(r *Replica) *Replica {
	initCs(&r.cs, fastrpc.NewTableId(defs.RPC_TABLE))
	return r
}
