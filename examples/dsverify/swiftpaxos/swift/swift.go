package swift

import (
	"fmt"
	"sync"
	"sync/atomic"
	"time"

	"github.com/imdea-software/swiftpaxos/config"
	"github.com/imdea-software/swiftpaxos/dlog"
	"github.com/imdea-software/swiftpaxos/hook"
	"github.com/imdea-software/swiftpaxos/replica"
	"github.com/imdea-software/swiftpaxos/replica/defs"
	"github.com/imdea-software/swiftpaxos/state"
	"github.com/orcaman/concurrent-map"
)

type Replica struct {
	*replica.Replica

	// ballotL orders the run loop's writes of ballot with BeTheLeader's
	// read, in an rpc goroutine (R6); the run loop reads it without
	ballotL sync.Mutex
	ballot  int32
	cballot int32
	status  int

	cmdDescs  cmap.ConcurrentMap
	delivered cmap.ConcurrentMap
	// deliveredAny (SW4, verification workaround): false iff delivered is empty, outside
	// deliver's Set..Store and handleSync's last Remove..Store; BeTheLeader reads it instead of
	// delivered.IsEmpty(), which read-locks every shard from any number of rpc goroutines
	deliveredAny atomic.Bool

	sender  replica.Sender
	batcher *Batcher
	repchan *replyChan

	keys map[state.Key]keyInfo
	hlog map[state.Key]*HashLog

	// cntL protects seqnum and routineCount, which the run loop and the
	// descriptors' goroutines update (S4)
	cntL            sync.Mutex
	seqnum          int
	pendingHashUpds map[CommandId]*UpdateEntry

	// historyL protects history's slots: the reply goroutine hands them out
	// modulo len(history), so a slot can be reused while (or after) its
	// previous holder writes it (SW-F2)
	historyL     sync.Mutex
	history      []commandStaticDesc
	historySize  int
	historyStart int

	qs *replica.QuorumSystem
	SQ replica.QuorumI
	FQ replica.QuorumI
	cs CommunicationSupply

	fixedMajority bool

	optExec     bool
	fastRead    bool
	deliverChan chan CommandId

	// execL makes deliver's check of the dependencies, the mark in
	// delivered and the execution one step (S3); it protects execLog, the
	// commands executed since the last MSync, which a recovery reports (R3)
	execL   sync.Mutex
	execLog []commandStaticDesc

	descPool     sync.Pool
	poolLevel    int
	routineCount int

	recover        chan int32
	recStart       time.Time
	newLeaderAckNs *replica.MsgSet
	// the ballot newLeaderAckNs was last reinitialised for (verification workaround, D30)
	newLeaderAckNsBallot int32

	proposes map[CommandId]*defs.GPropose
	// SWB-11: the dependencies handleProposal computed for the proposals
	// since the last MSync (run loop only): a recovery reports them for a
	// proposal its stopped descriptor did not take (fillNewLeaderAckN)
	proposeDeps map[CommandId]Dep

	// the commands proposed to this replica since its last MSync, in the
	// order it handled them (run loop only): a recovery report lists its
	// commands in this order (F3)
	handled []CommandId

	// the last MSync taken (run loop only): its commands are committed
	// here, and a recovery report has each of them, whether or not its
	// descriptor took it before a stop (N3)
	lastSync *MSync

	// N2: the commands accepted in this ballot, and the commands whose
	// leader's ack waits for the acceptance of a dependency (dependency ->
	// waiting commands); recheckChan gives the run loop the waiting ones
	acceptL     sync.Mutex
	accepted    map[CommandId]struct{}
	waiting     map[CommandId][]CommandId
	recheckChan chan CommandId
	// N2-loop: the waiting commands whose dependency a sequential
	// descriptor accepted (under acceptL; only the run loop adds to it); the
	// run loop rechecks them at the end of the same step, and those they
	// free in turn
	rechecks []CommandId

	// take only slow paths for these addresses
	slowAddrs map[string]struct{}
}

type commandDesc struct {
	phase      int
	cmd        state.Command
	dep        Dep
	hs         []SHash
	seqnum     int
	propose    *defs.GPropose
	proposeDep Dep

	slowPathH      *replica.MsgSet
	fastPathH      *replica.MsgSet
	afterPropagate *hook.OptCondF

	msgs     chan interface{}
	active   bool
	slowPath bool
	seq      bool
	stopChan chan *sync.WaitGroup

	successors  []CommandId
	successorsL sync.Mutex

	// execute before sending an MSync message
	defered func()

	// the leader's ack, waiting for the acceptance of a dependency (N2)
	waitingAck *MFastAck
	// verification workaround (P3): the ballots of the leader acks stored in afterPropagate
	// while propose is nil (one per ballot)
	storedBallots []int32
}

// proposeMsg is a proposal for a descriptor (handleProposal's), with the
// dependencies, the path hashes and the leader's number computed for it
// (seqnum -1 at a follower): the descriptor's owner sets them (SWB-11).
type proposeMsg struct {
	p      *defs.GPropose
	dep    Dep
	hs     []SHash
	seqnum int
}

type commandStaticDesc struct {
	cmdId    CommandId
	phase    int
	cmd      state.Command
	dep      Dep
	slowPath bool
	defered  func()
}

type readDesc struct {
	hs      []SHash
	dep     Dep
	propose *defs.GPropose
}

// Test-only instrumentation (nil unless a test, or the build tag
// swiftexeclog with SWIFT_EXECLOG set, sets them; no behaviour change when
// nil): ExecHook is called at each execution (under execL), SyncHook when a
// replica takes an MSync (its state is reset), ReplyHook when a client
// registers a command's result.
var (
	ExecHook  func(rid int32, cmdId CommandId, cmd state.Command, val state.Value, ballot int32)
	SyncHook  func(rid int32, ballot int32)
	ReplyHook func(clientId int32, cmdId CommandId, val state.Value)
)

func New(alias string, rid int, addrs []string, exec, fastRead, optExec, AQreconf bool,
	pl, f int, conf *config.Config, l *dlog.Logger, slowAddrs []string) *Replica {
	cmap.SHARD_COUNT = 32768

	r := &Replica{
		Replica: replica.New(alias, rid, f, addrs, false, exec, false, conf, l),

		ballot:  0,
		cballot: 0,
		status:  NORMAL,

		cmdDescs:  cmap.New(),
		delivered: cmap.New(),

		keys:            make(map[state.Key]keyInfo),
		hlog:            make(map[state.Key]*HashLog),
		seqnum:          0,
		pendingHashUpds: make(map[CommandId]*UpdateEntry),

		history:      make([]commandStaticDesc, HISTORY_SIZE),
		historySize:  0,
		historyStart: 0,

		fixedMajority: false,

		optExec:     optExec,
		fastRead:    fastRead,
		deliverChan: make(chan CommandId, defs.CHAN_BUFFER_SIZE),

		poolLevel:    pl,
		routineCount: 0,

		recover: make(chan int32, 8),

		descPool: sync.Pool{
			New: func() interface{} {
				return &commandDesc{}
			},
		},

		proposes:    make(map[CommandId]*defs.GPropose),
		proposeDeps: make(map[CommandId]Dep),

		accepted:    make(map[CommandId]struct{}),
		waiting:     make(map[CommandId][]CommandId),
		recheckChan: make(chan CommandId, defs.CHAN_BUFFER_SIZE),

		slowAddrs: make(map[string]struct{}),
	}

	for _, addr := range slowAddrs {
		r.slowAddrs[addr] = struct{}{}
	}

	useFastAckPool = pl > 1

	r.SQ = replica.NewMajorityOf(r.N)
	r.FQ = replica.NewThreeQuartersOf(r.N)

	r.sender = replica.NewSender(r.Replica)
	r.batcher = NewBatcher(r, 16, releaseFastAck, func(_ *MLightSlowAck) {})
	r.repchan = NewReplyChan(r)

	qs, err := replica.NewQuorumSystem(r.N/2+1, r.Replica, conf.Quorum)
	if err != nil && err != replica.THREE_QUARTERS {
		r.Fatal(err)
	}
	r.qs = qs
	r.ballot = r.qs.BallotAt(0)
	if r.ballot == -1 {
		r.ballot = 0
	}
	r.cballot = r.ballot
	if err != replica.THREE_QUARTERS {
		r.fixedMajority = true
		r.FQ = r.qs.AQ(r.ballot)
	}

	initCs(&r.cs, r.RPC)

	r.Println("the leader is:", r.leader(), "ballot is:", r.ballot)

	hook.HookUser1(func() {
		totalNum := 0
		slowPaths := 0
		r.historyL.Lock()
		defer r.historyL.Unlock()
		for i := 0; i < HISTORY_SIZE; i++ {
			if r.history[i].dep == nil {
				continue
			}
			totalNum++
			if r.history[i].slowPath {
				slowPaths++
			}
		}

		fmt.Printf("Total number of commands: %d\n", totalNum)
		fmt.Printf("Number of slow paths: %d\n", slowPaths)
	})

	r.Println("SQ:", r.SQ)
	r.Println("FQ:", r.FQ)

	go r.run()

	return r
}

// TODO: do something more elegant
func (r *Replica) BeTheLeader(_ *defs.BeTheLeaderArgs, reply *defs.BeTheLeaderReply) error {
	if r.deliveredAny.Load() {
		b := r.qs.BallotAt(1)
		r.recover <- b
		reply.Leader = r.Id
	} else {
		r.ballotL.Lock()
		reply.Leader = r.leader()
		r.ballotL.Unlock()
	}
	reply.NextLeader = replica.Leader(r.qs.BallotAt(1), r.N)
	if reply.Leader == 0 {
		reply.Leader = -2
	}
	if reply.NextLeader == 0 {
		reply.NextLeader = -2
	}
	return nil
}

func (r *Replica) run() {
	r.ConnectToPeers()
	latencies := r.ComputeClosestPeers()
	for _, l := range latencies {
		d := time.Duration(l*1000*1000) * time.Nanosecond
		if d > r.cs.maxLatency {
			r.cs.maxLatency = d
		}
	}

	go r.WaitForClientConnections()

	for !r.Shutdown {
		select {
		case newBallot := <-r.recover:
			// R-Q1: a recovery whose ballot would exceed MaxBallot is refused
			if b, ok := r.recoveryBallot(newBallot); ok {
				newLeader := &MNewLeader{
					Replica: r.Id,
					Ballot:  b,
				}
				r.sender.SendToAll(newLeader, r.cs.newLeaderRPC)
				r.reinitNewLeaderAckNs(b)
				r.handleNewLeader(newLeader)
			}

		case cmdId := <-r.deliverChan:
			r.getCmdDesc(cmdId, "deliver", nil)

		case cmdId := <-r.recheckChan:
			r.getCmdDesc(cmdId, "recheck", nil)

		case propose := <-r.ProposeChan:
			r.handleProposal(propose)

		case m := <-r.cs.fastAckChan:
			fastAck := m.(*MFastAck)
			r.leaderAckHash(fastAck)
			// This is a simple fix of the FIXME above:
			r.getCmdDescSeq(fastAck.CmdId, fastAck, nil, nil, r.leader() == r.Id)
			// r.getCmdDescSeq(fastAck.CmdId, fastAck, nil, nil, false)

		case m := <-r.cs.lightSlowAckChan:
			lightSlowAck := m.(*MLightSlowAck)
			r.getCmdDesc(lightSlowAck.CmdId, lightSlowAck, nil)

		case m := <-r.cs.acksChan:
			acks := m.(*MAcks)
			for _, f := range acks.FastAcks {
				r.leaderAckHash(&f)
				// This is a simple fix of the FIXME above:
				r.getCmdDescSeq(f.CmdId, copyFastAck(&f), nil, nil, r.leader() == r.Id)
				// r.getCmdDescSeq(f.CmdId, copyFastAck(&f), nil, nil, false)
			}
			for _, s := range acks.LightSlowAcks {
				ls := s
				r.getCmdDesc(s.CmdId, &ls, nil)
			}

		case m := <-r.cs.optAcksChan:
			optAcks := m.(*MOptAcks)
			for _, ack := range optAcks.Acks {
				fastAck := newFastAck()
				fastAck.Replica = optAcks.Replica
				fastAck.Ballot = optAcks.Ballot
				ackCmdId := ack.CmdId
				fastAck.CmdId = ackCmdId
				fastAck.Checksum = ack.Checksum
				fastAck.Seqnum = ack.Seqnum
				if !IsNilDepOfCmdId(ack.CmdId, ack.Dep) {
					fastAck.Dep = ack.Dep
				} else {
					fastAck.Dep = nil
				}
				r.leaderAckHash(fastAck)
				// This is a simple fix of the FIXME above:
				r.getCmdDescSeq(fastAck.CmdId, fastAck, nil, nil, r.leader() == r.Id)
				// r.getCmdDescSeq(fastAck.CmdId, fastAck, nil, nil, false)
			}

		case m := <-r.cs.newLeaderChan:
			newLeader := m.(*MNewLeader)
			r.handleNewLeader(newLeader)

		case m := <-r.cs.syncChan:
			sync := m.(*MSync)
			r.handleSync(sync)
		}
		r.drainRechecks()
	}
}

// drainRechecks rechecks the commands rechecks holds, and those their
// acceptance frees, until none is left (run loop only, N2-loop).
func (r *Replica) drainRechecks() {
	for {
		r.acceptL.Lock()
		if len(r.rechecks) == 0 {
			r.acceptL.Unlock()
			return
		}
		w := r.rechecks[0]
		r.rechecks = r.rechecks[1:]
		r.acceptL.Unlock()
		r.getCmdDesc(w, "recheck", nil)
	}
}

// handleProposal is run's propose case.
func (r *Replica) handleProposal(propose *defs.GPropose) {
	var cmdId CommandId
	cmdId.ClientId = propose.ClientId
	cmdId.SeqNum = propose.CommandId
	// A command is proposed once (R4): a second proposal (handleSync's
	// re-sent ones, which it first removes from proposes, are not second)
	// would add the command again to its key's dependencies.
	if _, dup := r.proposes[cmdId]; dup || r.delivered.Has(cmdId.String()) {
		return
	}
	r.proposes[cmdId] = propose
	r.handled = append(r.handled, cmdId)
	dep, hs := r.getDepAndHashes(propose.Command, cmdId)
	r.proposeDeps[cmdId] = dep
	// the leader numbers its proposals here, in the order of their path
	// hashes (getDepAndHashes), not in handlePropose, which a descriptor's
	// goroutine may run out of that order: a follower takes the hash of the
	// highest number it was acknowledged as its synced path (HashLog.update),
	// so every command it removed from its pending list is in that path (F2)
	seqnum := -1
	if r.leader() == r.Id {
		r.cntL.Lock()
		seqnum = r.seqnum
		r.seqnum++
		r.cntL.Unlock()
	}
	if upd, exists := r.pendingHashUpds[cmdId]; exists && r.leader() != r.Id {
		// TODO: when pipelining this can break ordering, disabling fast paths.
		delete(r.pendingHashUpds, cmdId)
		r.recordLeaderHash(cmdId, upd.seqnum, upd.hash)
	}
	ghostHandle(r.ballot, cmdId, propose.Command) // GHOST (L2)
	// FIXME: leader can receive fastAck before Propose,
	//        in this case desc is not seq
	// SWB-11: the dependencies, hashes and number go with the proposal to
	// the descriptor's owner, which sets them (handlePropose)
	desc := r.getCmdDescWith(cmdId, &proposeMsg{p: propose, dep: dep, hs: hs, seqnum: seqnum},
		r.leader() == r.Id)
	if desc == nil {
		r.Fatal("Got proposal for the delivered command", cmdId)
	}
}

// recoveryBallot is the ballot of the recovery run's recover case starts
// (newBallot from the recover channel: -1, or a ballot of the quorum file),
// and false when that ballot would exceed replica.MaxBallot (R-Q1: ballots
// are int32 and every recovery raises the ballot; the recovery is refused
// instead of wrapping the ballot negative).
func (r *Replica) recoveryBallot(newBallot int32) (int32, bool) {
	var b int32
	ok := true
	if newBallot != -1 {
		if newBallot > r.ballot {
			b = newBallot
			ok = 0 <= b && b <= replica.MaxBallot(r.N)
		} else {
			b, ok = r.qs.SameHigherOk(newBallot, r.ballot)
		}
	} else {
		b, ok = replica.NextBallotOfOk(r.Id, r.ballot, r.N)
	}
	if !ok {
		return r.ballot, false
	}
	return r.aliveQuorumBallot(b)
}

// aliveQuorumBallot is the first of this replica's ballots from b on whose fast quorum is alive
// (the recover case of run). F1: the ballots of one leader cycle through its NumAQ fast quorums,
// so after one cycle without an alive quorum the search stops (b is then one of this replica's
// ballots, above the one it started from) instead of adding N to the int32 ballot until it wraps
// negative (AQ then divides by zero).
//
// R-Q1: false when the next candidate would exceed replica.MaxBallot.
func (r *Replica) aliveQuorumBallot(b int32) (int32, bool) {
	tries := 0
	for quorumIsAlive := false; r.fixedMajority && !quorumIsAlive && tries <= r.qs.NumAQ(r.Id); tries++ {
		quorumIsAlive = true
		for rid := range r.qs.AQ(b) {
			// Alive is written by the peers' readers under r.M (R6)
			r.M.Lock()
			alive := r.Alive[rid]
			r.M.Unlock()
			if rid != r.Id && !alive {
				nb, ok := replica.NextBallotOfOk(r.Id, b, r.N)
				if !ok {
					return b, false
				}
				b = nb
				quorumIsAlive = false
				break
			}
		}
	}
	return b, true
}

func (r *Replica) handlePropose(pm *proposeMsg, desc *commandDesc, cmdId CommandId) {
	// SWB-11: set by the descriptor's owner (its goroutine, or the run loop
	// for a sequential one), the first writer's (handleSyncEntry's or this)
	if pm.dep != nil && desc.proposeDep == nil {
		desc.proposeDep = pm.dep
		if pm.hs != nil {
			desc.hs = pm.hs
			desc.seqnum = pm.seqnum
		}
	}
	msg := pm.p
	if r.status != NORMAL || desc.propose != nil {
		return
	}

	desc.propose = msg
	desc.cmd = msg.Command
	if desc.phase == COMMIT { // GHOST (L2): unreachable (nonissues/e1), the deferred commit
		ghostCommit(r.ballot, cmdId)
	}

	if !r.FQ.Contains(r.Id) {
		desc.afterPropagate.Recall()
		return
	}

	desc.dep = desc.proposeDep
	desc.phase = PRE_ACCEPT
	ghostPreaccept(r.ballot, cmdId, desc.dep) // GHOST (L2)
	// Verification workaround (P5, no reachable behaviour change): the fast ack's fields are
	// read before Recall. Recall's stored closures change desc.dep only together with
	// desc.slowPath = true (a follower adopting the leader's dependencies), and then the
	// function returns below before building the ack; so the values are the ones read after.
	ackDep, ackHs, ackSeq := desc.dep, desc.hs, desc.seqnum
	// SWB-6: Recall's functions may deliver the command and retire desc (to the pool, where
	// newDesc may reuse it): check delivered before reading desc again (same truth value).
	recalled := desc.afterPropagate.Recall()
	if r.delivered.Has(cmdId.String()) || (recalled && desc.slowPath) {
		// in this case a process already sent an MSlowAck
		// message, hence, no need to send MFastAck
		return
	}
	// N2-nofast: the leader's ack is here and waits under N2 for this command's dependencies
	// (desc.waitingAck); the command takes the slow path (this follower sends its slow ack when
	// it accepts), so a fast ack now would only be extra messages, as when desc.slowPath is set
	if recalled && desc.waitingAck != nil && r.Id != r.leader() {
		return
	}

	if _, exists := r.slowAddrs[msg.Addr]; exists && r.Id != r.leader() {
		return
	}

	fastAck := newFastAck()
	fastAck.Replica = r.Id
	fastAck.Ballot = r.ballot
	fastAck.CmdId = cmdId
	fastAck.Dep = ackDep
	fastAck.Checksum = ackHs
	if r.Id == r.leader() {
		fastAck.Seqnum = ackSeq
	}

	isRead := r.fastRead && msg.Command.Op != state.PUT

	fastAckSend := copyFastAck(fastAck)
	if !r.optExec {
		r.batcher.SendFastAck(fastAckSend)
	} else {
		if (r.Id == r.leader() && !isRead) || (isRead && desc.propose.Proxy) {
			r.batcher.SendFastAck(fastAckSend)
			// TODO: save old state
			if r.deliver(desc, cmdId) {
				// executed and freed: no access after (S8b)
				return
			}
		} else {
			r.batcher.SendFastAckClient(fastAckSend, msg.ClientId)
		}
	}
	r.handleFastAck(fastAck, desc)
}

func (r *Replica) handleFastAck(msg *MFastAck, desc *commandDesc) {
	if msg.Replica == r.leader() {
		r.fastAckFromLeader(msg, desc)
	} else {
		r.commonCaseFastAck(msg, desc)
	}
}

func (r *Replica) fastAckFromLeader(msg *MFastAck, desc *commandDesc) {
	// Verification workaround (P3, no reachable behaviour change): before the proposal, store at
	// most one leader ack per ballot. A leader sends one ack per command and ballot on each peer
	// stream, and the streams do not duplicate bytes, so a second ack of a stored ballot never
	// arrives; the check gives the proof a bound on the stored functions.
	if desc.propose == nil {
		for _, b := range desc.storedBallots {
			if b == msg.Ballot {
				return
			}
		}
		desc.storedBallots = append(desc.storedBallots, msg.Ballot)
	}
	desc.afterPropagate.Call(func() {
		if r.status != NORMAL || r.ballot != msg.Ballot {
			return
		}
		// Verification workaround (SWB-8; no reachable behaviour change): at a follower, a
		// function stored with others may run after an earlier one committed and delivered the
		// command and retired desc; desc is not touched then. In Go the extra stored functions
		// are stale ballots' and return at the check above.
		if r.leader() != r.Id && r.delivered.Has(msg.CmdId.String()) {
			return
		}

		// N2: make sure that
		//    ∀ id' ∈ d. phase[id'] ∈ {ACCEPT, COMMIT}
		// before accepting (a follower: the leader's dependencies are its
		// own proposals); otherwise wait, the run loop gives the ack back
		// once the dependency is accepted
		if r.leader() != r.Id && !r.depsAccepted(msg.Dep, msg.CmdId) {
			desc.waitingAck = msg
			return
		}
		desc.waitingAck = nil
		// a sequential descriptor is the run loop's (N2-loop)
		defer r.markAccepted(msg.CmdId, desc.seq)

		desc.phase = ACCEPT
		ghostAccept(msg.Ballot, msg.CmdId) // GHOST (L2)
		dep := Dep(msg.Dep)
		hs := desc.hs
		neq := !desc.dep.Equals(dep)
		fast := r.FQ.Contains(r.Id)
		slow := r.SQ.Contains(r.Id)
		sendSlowAck := r.leader() != r.Id && (slow || (fast && neq))
		msgCmdId := msg.CmdId
		msgChecksum := msg.Checksum

		defer func() {
			if r.leader() == r.Id || r.delivered.Has(msgCmdId.String()) {
				return
			}
			if !sendSlowAck && r.optExec && !SHashesEq(hs, msgChecksum) {
				lightSlowAck := &MLightSlowAck{
					Replica: r.Id,
					Ballot:  r.ballot,
					CmdId:   msgCmdId,
				}

				r.sender.SendToClient(msgCmdId.ClientId, lightSlowAck, r.cs.lightSlowAckRPC)
			}
		}()

		// Adopt the leader's dependencies before its ack is added to the
		// message sets: the ack can complete a quorum, and the command then
		// commits (and executes) with desc.dep (S1).
		if sendSlowAck && neq && !r.delivered.Has(msgCmdId.String()) {
			desc.dep = dep
		}

		desc.slowPathH.Add(msg.Replica, true, msg)
		delivered := r.delivered.Has(msgCmdId.String())
		if !delivered {
			desc.fastPathH.Add(msg.Replica, true, msg)
			delivered = r.delivered.Has(msgCmdId.String())
		}

		if sendSlowAck {
			if !delivered {
				// (delivered: a sequential descriptor may be freed, S8b)
				desc.slowPath = true
			}

			lightSlowAck := &MLightSlowAck{
				Replica: r.Id,
				Ballot:  r.ballot,
				CmdId:   msgCmdId,
			}

			if !r.optExec {
				r.batcher.SendLightSlowAck(lightSlowAck)
			} else {
				r.batcher.SendLightSlowAckClient(lightSlowAck, msgCmdId.ClientId)
			}
			if !delivered {
				r.handleLightSlowAck(lightSlowAck, desc)
			}
		}
	})
}

// depsAccepted says whether each of deps (but cmdId) is accepted in this
// ballot or delivered; if not, it records cmdId as waiting for the first one
// that is not (N2).
func (r *Replica) depsAccepted(deps []CommandId, cmdId CommandId) bool {
	r.acceptL.Lock()
	defer r.acceptL.Unlock()
	for _, d := range deps {
		if d == cmdId {
			continue
		}
		if _, ok := r.accepted[d]; ok || r.delivered.Has(d.String()) {
			continue
		}
		r.waiting[d] = append(r.waiting[d], cmdId)
		return false
	}
	return true
}

// markAccepted records cmdId as accepted in this ballot and gives the run
// loop the commands that waited for it (N2): inLoop (the caller is the run
// loop), on rechecks, which it takes at the end of this step (N2-loop);
// otherwise through recheckChan.
func (r *Replica) markAccepted(cmdId CommandId, inLoop bool) {
	r.acceptL.Lock()
	r.accepted[cmdId] = struct{}{}
	ws := r.waiting[cmdId]
	delete(r.waiting, cmdId)
	if inLoop {
		r.rechecks = append(r.rechecks, ws...)
		ws = nil
	}
	r.acceptL.Unlock()
	for _, w := range ws {
		go func(w CommandId) {
			r.recheckChan <- w
		}(w)
	}
}

func (r *Replica) commonCaseFastAck(msg *MFastAck, desc *commandDesc) {
	if r.status != NORMAL || r.ballot != msg.Ballot {
		return
	}

	msgCmdId := msg.CmdId
	if msg.Dep == nil {
		desc.slowPathH.Add(msg.Replica, msg.Replica == r.leader(), msg)
		if r.delivered.Has(msgCmdId.String()) {
			return
		}
	}
	desc.fastPathH.Add(msg.Replica, msg.Replica == r.leader(), msg)
}

func getFastAndSlowAcksHandler(r *Replica, desc *commandDesc) replica.MsgSetHandler {
	return func(leaderMsg interface{}, msgs []interface{}) {

		if leaderMsg == nil {
			return
		}

		leaderFastAck := leaderMsg.(*MFastAck)

		desc.phase = COMMIT
		// GHOST (L2, D92): resolved only once the proposal is installed; otherwise
		// handlePropose's deferred ghostCommit resolves it (unreachable in Go:
		// nonissues/e1 in the Lean project). No behaviour change: only the ghost
		// resolution is conditional.
		if desc.propose != nil {
			ghostCommit(leaderFastAck.Ballot, leaderFastAck.CmdId)
		}

		for _, depCmdId := range desc.dep {
			depDesc := r.getCmdDesc(depCmdId, nil, nil)
			if depDesc == nil {
				continue
			}
			depDesc.successorsL.Lock()
			depDesc.successors = append(depDesc.successors, leaderFastAck.CmdId)
			depDesc.successorsL.Unlock()
		}

		r.deliver(desc, leaderFastAck.CmdId)
	}
}

func (r *Replica) handleLightSlowAck(msg *MLightSlowAck, desc *commandDesc) {
	fastAck := newFastAck()
	fastAck.Replica = msg.Replica
	fastAck.Ballot = msg.Ballot
	msgCmdId := msg.CmdId
	fastAck.CmdId = msgCmdId
	fastAck.Dep = nil
	r.commonCaseFastAck(fastAck, desc)
}

// deliver says whether it finished the descriptor (a sequential one, freed
// after its history slot): its caller must not use it after (S8b).
func (r *Replica) deliver(desc *commandDesc, cmdId CommandId) bool {
	// TODO: what if desc.propose is nil ?
	//       is that possible ?
	//
	//       Don't think so
	//       Now I do
	// TODO: How is that possible ?

	if desc.propose == nil || r.delivered.Has(cmdId.String()) || !r.Exec {
		return false
	}

	if desc.phase != COMMIT && (!r.optExec || r.Id != r.leader()) {
		return false
	}

	// The check of the dependencies, the mark and the execution are one step
	// (S3): a successor delivered by another descriptor's goroutine must not
	// see this command delivered before it has executed.
	r.execL.Lock()
	for _, cmdIdPrime := range desc.dep {
		if !r.delivered.Has(cmdIdPrime.String()) {
			r.execL.Unlock()
			return false
		}
	}

	r.delivered.Set(cmdId.String(), struct{}{})
	r.deliveredAny.Store(true)
	v := desc.cmd.Execute(r.State)
	if ExecHook != nil {
		ExecHook(r.Id, cmdId, desc.cmd, v, r.ballot)
	}
	r.execLog = append(r.execLog, commandStaticDesc{
		cmdId: cmdId,
		phase: desc.phase,
		cmd:   desc.cmd,
		dep:   desc.dep,
	})
	r.execL.Unlock()

	desc.successorsL.Lock()
	if desc.successors != nil {
		for _, sucCmdId := range desc.successors {
			go func(sucCmdId CommandId) {
				r.deliverChan <- sucCmdId
			}(sucCmdId)
		}
	}
	desc.successorsL.Unlock()

	if !r.Dreply {
		return false
	}

	r.repchan.reply(desc, cmdId, v)
	if desc.seq {
		// wait for the slot number and ignore any other message
		for {
			switch slot := (<-desc.msgs).(type) {
			case int:
				r.handleMsg(slot, desc, cmdId)
				return true
			}
		}
	}
	return false
}

func (r *Replica) getCmdDesc(cmdId CommandId, msg interface{}, dep Dep) *commandDesc {
	return r.getCmdDescSeq(cmdId, msg, dep, nil, false)
}

// getCmdDescSeq: dep and hs are not used (every caller passes nil; SWB-11: a
// proposal's are in its proposeMsg, handleProposal's).
func (r *Replica) getCmdDescSeq(cmdId CommandId, msg interface{}, dep Dep, hs []SHash, seq bool) *commandDesc {
	return r.getCmdDescWith(cmdId, msg, seq)
}

// getCmdDescWith looks up cmdId's descriptor, or creates it (and its
// goroutine unless it is sequential), and gives it msg. SWB-11: it writes no
// field of an existing descriptor, which its goroutine owns (Go's memory
// model); a proposal's dependencies, hashes and number are set by the owner,
// from the proposeMsg (handlePropose).
func (r *Replica) getCmdDescWith(cmdId CommandId, msg interface{}, seq bool) *commandDesc {
	key := cmdId.String()
	if r.delivered.Has(key) {
		return nil
	}

	var desc *commandDesc
	// SWB-15 (P8): seq and msgs are read under the shard's lock: after
	// Upsert, desc may be retired and reused for another command (Go's
	// memory model; the message must not reach that command)
	var seqD bool
	var msgs chan interface{}

	r.cmdDescs.Upsert(key, nil,
		func(exists bool, mapV, _ interface{}) interface{} {
			if exists {
				desc = mapV.(*commandDesc)
				seqD, msgs = desc.seq, desc.msgs
				return desc
			}

			desc = r.newDesc()
			// SW4 (verification workaround): the check and the increment of routineCount are
			// one critical section, so at most MaxDescRoutines descriptor goroutines are live
			r.cntL.Lock()
			desc.seq = seq || desc.seq || r.routineCount >= MaxDescRoutines
			if !desc.seq {
				r.routineCount++
			}
			r.cntL.Unlock()
			seqD, msgs = desc.seq, desc.msgs
			if !desc.seq {
				go r.handleDesc(desc, cmdId)
			}

			return desc
		})

	if msg != nil {
		if seqD {
			r.handleMsg(msg, desc, cmdId)
		} else {
			msgs <- msg
		}
	}

	return desc
}

func (r *Replica) newDesc() *commandDesc {
	desc := r.allocDesc()
	desc.dep = nil
	desc.hs = nil
	desc.seqnum = -1
	// SWB-15 (P8): fresh channels (not the reused descriptor's, drained): a
	// send on the old incarnation's channel (getCmdDescWith's, captured under
	// the shard's lock) never reaches the new one
	desc.msgs = make(chan interface{}, 8)
	desc.active = true
	desc.phase = START
	// SWB-4: a reused descriptor's successors may still be appended to by a dependent command's
	// commit handler (under successorsL): reset them under the same lock.
	desc.successorsL.Lock()
	desc.successors = nil
	desc.successorsL.Unlock()
	desc.slowPath = false
	r.cntL.Lock()
	desc.seq = (r.routineCount >= MaxDescRoutines)
	r.cntL.Unlock()
	desc.defered = func() {}
	desc.storedBallots = nil
	desc.propose = nil
	desc.proposeDep = nil
	// Verification workaround (P12, no reachable behaviour change): a reused descriptor does not
	// keep the previous command's waiting leader ack. A "recheck" reaches a descriptor only for
	// its own command after that command's ack waited, which overwrote waitingAck; the proof
	// needs waitingAck to be nil or this command's ack.
	desc.waitingAck = nil
	desc.stopChan = make(chan *sync.WaitGroup, 8)

	desc.afterPropagate = desc.afterPropagate.ReinitCondF(func() bool {
		return desc.propose != nil
	})

	acceptFastAndSlowAck := func(msg, leaderMsg interface{}) bool {
		if leaderMsg == nil {
			return true
		}
		leaderFastAck := leaderMsg.(*MFastAck)
		fastAck := msg.(*MFastAck)
		return fastAck.Dep == nil ||
			(Dep(leaderFastAck.Dep)).Equals(fastAck.Dep)
	}

	// The message sets do not return acks to the pool (S8): the same ack is
	// in both sets (the leader's, the slow acks), so a release would put it
	// in the pool twice, or while the other set refers to it. The batcher
	// still returns the copies it is given (no other reference).
	freeFastAck := func(msg interface{}) {}

	h := getFastAndSlowAcksHandler(r, desc)
	desc.slowPathH = desc.slowPathH.ReinitMsgSet(r.SQ, acceptFastAndSlowAck, freeFastAck, h)
	desc.fastPathH = desc.fastPathH.ReinitMsgSet(r.FQ, acceptFastAndSlowAck, freeFastAck, h)

	return desc
}

func (r *Replica) allocDesc() *commandDesc {
	if r.poolLevel > 0 {
		return r.descPool.Get().(*commandDesc)
	}
	return &commandDesc{}
}

func (r *Replica) freeDesc(desc *commandDesc) {
	if r.poolLevel > 0 {
		r.descPool.Put(desc)
	}
}

func (r *Replica) handleDesc(desc *commandDesc, cmdId CommandId) {
	for desc.active {
		select {
		case wg := <-desc.stopChan:
			desc.active = false
			// Verification workaround (P6, no reachable behaviour change): drop the
			// messages still queued for the stopped descriptor here (newDesc drops them
			// when it reuses desc; a stopped descriptor never reads them), so the proof
			// can hand their resources back with the stop.
			for len(desc.msgs) != 0 {
				<-desc.msgs
			}
			// answer every stop request before the last access to desc:
			// after Done, handleSync may reuse it (S4)
			r.drainStops(desc)
			// SWB-14 (P7): a stopped goroutine gives its routineCount back
			// before stopDescs' Wait returns
			r.cntL.Lock()
			r.routineCount--
			r.cntL.Unlock()
			wg.Done()
			return
		case msg := <-desc.msgs:
			if r.handleMsg(msg, desc, cmdId) {
				// SWB-14: the slot case gave the goroutine's routineCount
				// back; the descriptor is out of cmdDescs: no stop request
				// comes after the ones buffered; answer them, then free
				// it (S4: not before, a reuse would race with this
				// goroutine)
				r.drainStops(desc)
				r.freeDesc(desc)
				return
			}
		}
	}
	r.drainStops(desc)
}

func (r *Replica) drainStops(desc *commandDesc) {
	for len(desc.stopChan) != 0 {
		(<-desc.stopChan).Done()
	}
}

func (r *Replica) handleMsg(m interface{}, desc *commandDesc, cmdId CommandId) bool {
	switch msg := m.(type) {

	case *proposeMsg:
		r.handlePropose(msg, desc, cmdId)

	case *MFastAck:
		if msg.CmdId == cmdId {
			r.handleFastAck(msg, desc)
		}

	case *MLightSlowAck:
		if msg.CmdId == cmdId {
			r.handleLightSlowAck(msg, desc)
		}

	case string:
		if msg == "deliver" {
			r.deliver(desc, cmdId)
		} else if msg == "recheck" && desc.waitingAck != nil {
			r.fastAckFromLeader(desc.waitingAck, desc)
		}

	case *syncEntry:
		r.handleSyncEntry(msg, desc, cmdId)

	case int:
		r.historyL.Lock()
		r.history[msg].cmdId = cmdId
		r.history[msg].phase = desc.phase
		r.history[msg].cmd = desc.cmd
		r.history[msg].dep = desc.dep
		r.history[msg].slowPath = desc.slowPath
		r.history[msg].defered = desc.defered
		r.historyL.Unlock()
		// out of cmdDescs before active is written: stopDescs reads
		// active under cmdDescs' lock (S4)
		// SWB-14: a goroutine gives its routineCount back before stopDescs can
		// return (it returns when routineCount is 0: MaxDescRoutines' bound, P2-B).
		// Verification workaround (P9, no behaviour change beyond possibly one more
		// stopDescs round): out of cmdDescs first, then the count, so that a zero
		// count means every entry still in cmdDescs is at home.
		r.cmdDescs.Remove(cmdId.String())
		if !desc.seq {
			r.cntL.Lock()
			r.routineCount--
			r.cntL.Unlock()
		}
		desc.active = false
		desc.slowPathH.Free()
		desc.fastPathH.Free()
		if desc.seq {
			r.freeDesc(desc)
		}
		return true
	}

	return false
}

func (r *Replica) leader() int32 {
	return replica.Leader(r.ballot, r.N)
}

func (r *Replica) getDepAndHashes(cmd state.Command, cmdId CommandId) (Dep, []SHash) {
	dep := []CommandId{}
	hashes := []SHash{}
	keysOfCmd := keysOf(cmd)

	for _, key := range keysOfCmd {
		info, exists := r.keys[key]
		if exists {
			cdep := info.getConflictCmds(cmd)
			dep = append(dep, cdep...)
		} else {
			info = newLightKeyInfo()
			r.keys[key] = info
		}
		info.add(cmd, cmdId)

		l, exists := r.hlog[key]
		if !exists {
			l = NewHashLog()
			r.hlog[key] = l
		}
		hashes = append(hashes, l.Append(cmd, cmdId))
	}

	return dep, hashes
}

// leaderAckHash records the hashes of an ack of this ballot's leader (S7: not
// an ack the replica that is now the leader sent in an older ballot, as a
// follower, or one without hashes).
func (r *Replica) leaderAckHash(f *MFastAck) {
	if f.Replica == r.leader() && r.leader() != r.Id && f.Ballot == r.ballot {
		// TODO: again, think about pipeline.
		r.recordLeaderHash(f.CmdId, f.Seqnum, f.Checksum)
	}
}

func (r *Replica) recordLeaderHash(cmdId CommandId, s int, hs []SHash) {
	p, exists := r.proposes[cmdId]
	if !exists {
		r.pendingHashUpds[cmdId] = &UpdateEntry{
			hash:   hs,
			seqnum: s,
		}
		return
	}
	r.updateLogs(p.Command, cmdId, s, hs)
}

func (r *Replica) updateLogs(cmd state.Command, cmdId CommandId, s int, hs []SHash) {
	keys := keysOf(cmd)

	if len(keys) != len(hs) {
		r.Fatal("the number of hashes does not match number of objects")
		// Fatal may return (a non-verbose logger): the hashes are not the
		// leader's for these keys, do not index past them (S7)
		return
	}

	for i, key := range keys {
		l, exists := r.hlog[key]
		if !exists {
			l = NewHashLog()
			r.hlog[key] = l
		}
		l.Update(cmdId, s, hs[i])
	}
}
