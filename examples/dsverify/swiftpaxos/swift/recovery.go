package swift

import (
	"log"
	"slices"
	"sync"
	"time"

	"github.com/imdea-software/swiftpaxos/replica"
	"github.com/imdea-software/swiftpaxos/replica/defs"
	"github.com/imdea-software/swiftpaxos/state"
	"github.com/orcaman/concurrent-map"
)

func (r *Replica) handleNewLeader(msg *MNewLeader) {
	if r.ballot >= msg.Ballot {
		return
	}
	log.Println("Recovering... with the ballot", msg.Ballot)

	// stop the reply channel's and the descriptors' goroutines before
	// writing the ballot and the status they read (S4)
	// (in a recovery, a higher ballot's MNewLeader: they are stopped, and
	// stop would wait for the reply channel's exited goroutine: N1)
	if r.status == NORMAL {
		r.repchan.stop()
		r.stopDescs()
	}

	r.status = RECOVERING
	r.ballotL.Lock()
	r.ballot = msg.Ballot
	r.ballotL.Unlock()
	ghostNewBallot(msg.Ballot) // GHOST (L2)
	r.recStart = time.Now()

	newLeaderAckN := &MNewLeaderAckN{
		Replica: r.Id,
		Ballot:  r.ballot,
		Cballot: r.cballot,
	}
	r.fillNewLeaderAckN(newLeaderAckN)

	if msg.Replica != r.Id {
		r.sender.SendTo(msg.Replica, newLeaderAckN, r.cs.newLeaderAckNRPC)
	} else {
		r.handleNewLeaderAckN(newLeaderAckN)
	}

	// stop processing normal channels:
	for r.status == RECOVERING {
		select {
		case m := <-r.cs.newLeaderChan:
			newLeader := m.(*MNewLeader)
			r.handleNewLeader(newLeader)

		case m := <-r.cs.newLeaderAckNChan:
			newLeaderAck := m.(*MNewLeaderAckN)
			r.handleNewLeaderAckN(newLeaderAck)

		case m := <-r.cs.syncChan:
			sync := m.(*MSync)
			r.handleSync(sync)
		}
	}
}

func (r *Replica) handleNewLeaderAckN(msg *MNewLeaderAckN) {
	if r.status != RECOVERING || r.ballot != msg.Ballot {
		return
	}
	// Verification workaround (D30, no reachable behaviour change): only acks of the ballot the
	// set was reinitialised for. An ack is sent only to its MNewLeader's sender, which
	// reinitialised the set for that ballot just before sending it; the proof's network model
	// does not record an ack's destination.
	if r.newLeaderAckNs == nil || msg.Ballot != r.newLeaderAckNsBallot {
		return
	}

	r.newLeaderAckNs.Add(msg.Replica, false, msg)
}

// recEntry is a reported command (the new leader's view of it).
type recEntry struct {
	phase int
	cmd   state.Command
	dep   Dep
	// the class of a kept command: 0 accepted or committed in the highest
	// ballot (or the previous MSync's), or proposed by its leader; 1 kept
	// because a fast quorum may have pre-accepted it (R1); 2 a dependency of a
	// kept command (closure)
	class int
}

func (r *Replica) handleNewLeaderAckNs(_ interface{}, msgs []interface{}) {
	sync := r.recoveredSync(msgs)
	ghostComputeSync(r.ballot, msgs) // GHOST (L2)
	r.sender.SendToAll(sync, r.cs.syncRPC)
	r.handleSync(sync)
}

// recoveredSync computes the new ballot's MSync from a majority's reports:
// the commands that may have been chosen in the highest ballot b of the
// reports (the Paxos rule), in one order (recovery-design.md).
func (r *Replica) recoveredSync(msgs []interface{}) *MSync {
	maxCbal := int32(-1)
	acks := []*MNewLeaderAckN{}
	for _, msg := range msgs {
		newLeaderAck := msg.(*MNewLeaderAckN)
		acks = append(acks, newLeaderAck)
		if maxCbal < newLeaderAck.Cballot {
			maxCbal = newLeaderAck.Cballot
		}
	}
	// deterministic: by replica
	slices.SortFunc(acks, func(a, b *MNewLeaderAckN) int {
		if a.Replica < b.Replica {
			return -1
		}
		if a.Replica > b.Replica {
			return 1
		}
		return 0
	})
	U := []*MNewLeaderAckN{}
	for _, a := range acks {
		if a.Cballot == maxCbal {
			U = append(U, a)
		}
	}
	oldLeader := replica.Leader(maxCbal, r.N)
	aq := r.qs.AQ(maxCbal)

	kept := make(map[CommandId]*recEntry)
	leaderInU := false
	for _, a := range U {
		if a.Replica == oldLeader {
			leaderInU = true
		}
	}

	// 1. accepted or committed in U; the old leader's own proposals
	for _, a := range U {
		for i, cmdId := range a.CmdIds {
			ph := a.Phases[i]
			ok := ph == ACCEPT || ph == COMMIT ||
				(a.Replica == oldLeader && ph == PRE_ACCEPT)
			if !ok {
				continue
			}
			e, exists := kept[cmdId]
			if !exists || (e.phase != COMMIT && ph == COMMIT) {
				kept[cmdId] = &recEntry{phase: ph, cmd: a.Cmds[i],
					dep: Dep(a.Deps[i].Dep), class: 0}
			}
		}
	}

	// 2. R1: if the old leader did not report, a command every reporter of
	// U in the old ballot's fast quorum pre-accepted with the same
	// dependencies may have been chosen on the fast path (the paper's
	// Figure 5, l. 58-61)
	R := []*MNewLeaderAckN{}
	for _, a := range U {
		if aq.Contains(a.Replica) {
			R = append(R, a)
		}
	}
	if !leaderInU {
		if len(R) > 0 {
			for i, cmdId := range R[0].CmdIds {
				if R[0].Phases[i] != PRE_ACCEPT {
					continue
				}
				if _, exists := kept[cmdId]; exists {
					continue
				}
				dep := Dep(R[0].Deps[i].Dep)
				same := true
				for _, a := range R[1:] {
					found := false
					for k, id := range a.CmdIds {
						if id == cmdId && a.Phases[k] == PRE_ACCEPT && dep.Equals(a.Deps[k].Dep) {
							found = true
							break
						}
					}
					if !found {
						same = false
						break
					}
				}
				if same {
					kept[cmdId] = &recEntry{phase: ACCEPT, cmd: R[0].Cmds[i], dep: dep, class: 1}
				}
			}
		}
	}

	// 3. closure: a kept command's dependencies are kept, with the best
	// report (the highest phase; U first); a dependency no one reports is
	// dropped from the list
	best := func(d CommandId) *recEntry {
		// F4: when rule 2 applies, R[0]'s own entry first: the closure of a
		// command kept for the fast path then follows R[0]'s order (its
		// dependencies are R[0]'s own, as rule 3b's edges), and the kept graph
		// has no cycle (another reporter's entry, of a higher phase or first by
		// id, could order a dependency after the command: a cycle, broken at
		// the smallest id)
		if !leaderInU && len(R) > 0 {
			for i, id := range R[0].CmdIds {
				if id == d {
					return &recEntry{phase: R[0].Phases[i], cmd: R[0].Cmds[i],
						dep: Dep(R[0].Deps[i].Dep), class: 2}
				}
			}
		}
		var b *recEntry
		for _, list := range [][]*MNewLeaderAckN{U, acks} {
			for _, a := range list {
				for i, id := range a.CmdIds {
					if id != d {
						continue
					}
					if b == nil || a.Phases[i] > b.phase {
						b = &recEntry{phase: a.Phases[i], cmd: a.Cmds[i],
							dep: Dep(a.Deps[i].Dep), class: 2}
					}
				}
			}
			if b != nil {
				return b
			}
		}
		return nil
	}
	work := sortedIds(kept)
	for len(work) > 0 {
		c := work[0]
		work = work[1:]
		e := kept[c]
		dep := Dep{}
		for _, d := range e.dep {
			if d == c {
				continue
			}
			if _, exists := kept[d]; !exists {
				b := best(d)
				if b == nil {
					continue
				}
				kept[d] = b
				work = append(work, d)
			}
			dep = append(dep, d)
		}
		e.dep = dep
	}

	// 3b. F3: a command kept by R1 or the closure comes after every
	// conflicting kept command that R[0] handled before it (its report's
	// order). If x was chosen on the fast path, R[0]'s path for x is the
	// leader's, and every command R[0] handled before x on x's key is in it
	// (dpath.go): the edge is the leader's order. Otherwise x was not chosen
	// and its place is free; a command R[0] handled after a chosen one is
	// put after it, as real time requires of one invoked after it completed
	// (with rule 4 for the accepted ones). No cycle: the edges follow R[0]'s
	// order among the commands of rule 2 and the closure (whose dependencies
	// are R[0]'s own), and go to accepted commands, whose dependencies are
	// accepted ones (N2); the reachability test only keeps it so.
	if !leaderInU && len(R) > 0 {
		pos := make(map[CommandId]int)
		for i, cmdId := range R[0].CmdIds {
			if _, exists := pos[cmdId]; !exists {
				pos[cmdId] = i
			}
		}
		ids := sortedIds(kept)
		for _, c := range ids {
			pc, in := pos[c]
			if kept[c].class == 0 || !in {
				continue
			}
			for _, w := range ids {
				pw, in := pos[w]
				if w == c || !in || pw > pc || !inConflict(kept[w].cmd, kept[c].cmd) {
					continue
				}
				if kept[c].dep.Contains(w) || recReaches(kept, w, c) {
					continue
				}
				kept[c].dep = append(kept[c].dep, w)
			}
		}
	}

	// 4. a command kept by R1 or the closure comes after every conflicting
	// accepted one that does not depend on it (Invariant 2; if it was chosen
	// on the fast path its dependencies are the old leader's, which put it
	// after those already)
	ids := sortedIds(kept)
	for _, c := range ids {
		if kept[c].class == 0 {
			continue
		}
		for _, a := range ids {
			if kept[a].class != 0 || !inConflict(kept[a].cmd, kept[c].cmd) {
				continue
			}
			if !recReaches(kept, c, a) && !recReaches(kept, a, c) {
				kept[c].dep = append(kept[c].dep, a)
			}
		}
	}

	// 5. one order (R5): a topological sort, smallest id first among the
	// ready ones, a cycle broken at its smallest command
	order := recOrder(kept, ids)

	// 6. the dependencies sent: the order, per key, as lightKeyInfo's
	sync := &MSync{
		Replica: r.Id,
		Ballot:  r.ballot,
		Phases:  make(map[CommandId]int),
		Cmds:    make(map[CommandId]state.Command),
		Deps:    make(map[CommandId]Dep),
	}
	keys := make(map[state.Key]keyInfo)
	for _, c := range order {
		e := kept[c]
		dep := Dep{}
		for _, k := range keysOf(e.cmd) {
			info, exists := keys[k]
			if !exists {
				info = newLightKeyInfo()
				keys[k] = info
			}
			dep = append(dep, info.getConflictCmds(e.cmd)...)
			info.add(e.cmd, c)
		}
		sync.Phases[c] = COMMIT
		sync.Cmds[c] = e.cmd
		sync.Deps[c] = dep
	}
	return sync
}

func sortedIds(m map[CommandId]*recEntry) []CommandId {
	ids := make([]CommandId, 0, len(m))
	for id := range m {
		ids = append(ids, id)
	}
	slices.SortFunc(ids, cmdIdCmp)
	return ids
}

// recReaches says whether from depends, transitively, on to.
func recReaches(kept map[CommandId]*recEntry, from, to CommandId) bool {
	seen := make(map[CommandId]bool)
	stack := []CommandId{from}
	for len(stack) > 0 {
		x := stack[len(stack)-1]
		stack = stack[:len(stack)-1]
		e, exists := kept[x]
		if !exists {
			continue
		}
		for _, y := range e.dep {
			if y == to {
				return true
			}
			if !seen[y] {
				seen[y] = true
				stack = append(stack, y)
			}
		}
	}
	return false
}

// recOrder sorts ids so that each comes after its dependencies (smallest
// first among the ready ones; in a cycle, the smallest is taken first).
func recOrder(kept map[CommandId]*recEntry, ids []CommandId) []CommandId {
	placed := make(map[CommandId]bool)
	order := []CommandId{}
	for len(order) < len(ids) {
		next := -1
		for i, c := range ids {
			if placed[c] {
				continue
			}
			ready := true
			for _, d := range kept[c].dep {
				if _, exists := kept[d]; exists && !placed[d] {
					ready = false
					break
				}
			}
			if ready {
				next = i
				break
			}
		}
		if next == -1 {
			// a cycle: the smallest remaining command
			for i, c := range ids {
				if !placed[c] {
					next = i
					break
				}
			}
		}
		placed[ids[next]] = true
		order = append(order, ids[next])
	}
	return order
}

func (r *Replica) fillNewLeaderAckN(newLeaderAckN *MNewLeaderAckN) {
	cmdIds := []CommandId{}
	phases := []int{}
	cmds := []state.Command{}
	deps := []SDep{}
	seen := make(map[CommandId]struct{})

	// the executed commands, whose descriptors are gone (R3), with the phase
	// they had when executed (a leader's optimistic executions keep theirs)
	r.execL.Lock()
	for _, e := range r.execLog {
		if _, exists := seen[e.cmdId]; exists {
			continue
		}
		seen[e.cmdId] = struct{}{}
		phase := e.phase
		if phase < PRE_ACCEPT {
			phase = PRE_ACCEPT
		}
		cmdIds = append(cmdIds, e.cmdId)
		phases = append(phases, phase)
		cmds = append(cmds, e.cmd)
		deps = append(deps, SDep{e.dep})
	}
	r.execL.Unlock()

	// the last MSync's commands, committed, with its dependencies: a
	// descriptor's goroutine may have been stopped before it took its
	// syncEntry, but this replica took the MSync and sent its slow acks (N3)
	if m := r.lastSync; m != nil {
		for cmdId := range m.Phases {
			if _, exists := seen[cmdId]; exists {
				continue
			}
			seen[cmdId] = struct{}{}
			dep := m.Deps[cmdId]
			if dep == nil {
				dep = Dep{}
			}
			cmdIds = append(cmdIds, cmdId)
			phases = append(phases, COMMIT)
			cmds = append(cmds, m.Cmds[cmdId])
			deps = append(deps, SDep{dep})
		}
	}

	r.cmdDescs.IterCb(func(_ string, v interface{}) {
		desc := v.(*commandDesc)
		if desc.propose != nil {
			cmdId := CommandId{
				ClientId: desc.propose.ClientId,
				SeqNum:   desc.propose.CommandId,
			}
			if _, exists := seen[cmdId]; !exists {
				seen[cmdId] = struct{}{}
				cmdIds = append(cmdIds, cmdId)
				phases = append(phases, desc.phase)
				cmds = append(cmds, desc.cmd)
				deps = append(deps, SDep{desc.dep})
			}
		}
	})

	// a proposal without a handled descriptor: its command, with the
	// dependencies computed at the proposal, in phase START (never kept for
	// itself); not a no-op in ACCEPT, which the new leader would commit in
	// its place (R2)
	for cmdId, propose := range r.proposes {
		if _, exists := seen[cmdId]; exists || r.delivered.Has(cmdId.String()) {
			continue
		}
		dep := []CommandId{}
		if v, exists := r.cmdDescs.Get(cmdId.String()); exists && v.(*commandDesc).proposeDep != nil {
			dep = v.(*commandDesc).proposeDep
		} else if pd, ok := r.proposeDeps[cmdId]; exists && ok {
			// SWB-11: its stopped goroutine did not take the proposal
			// (still in msgs), whose dependencies the run loop set before
			dep = pd
		}
		cmdIds = append(cmdIds, cmdId)
		phases = append(phases, START)
		cmds = append(cmds, propose.Command)
		deps = append(deps, SDep{dep})
	}

	// F3: in the order this replica handled the commands (those of the last
	// MSync, which it did not handle, first): the new leader orders the
	// commands it keeps for the fast path after those their reporter handled
	// before them (recoveredSync, rule 3b)
	rank := make(map[CommandId]int)
	for i, cmdId := range r.handled {
		if _, exists := rank[cmdId]; !exists {
			rank[cmdId] = i + 1
		}
	}
	idx := make([]int, len(cmdIds))
	for i := range idx {
		idx[i] = i
	}
	slices.SortFunc(idx, func(i, j int) int {
		ri, rj := rank[cmdIds[i]], rank[cmdIds[j]]
		if ri < rj || (ri == rj && i < j) {
			return -1
		}
		if rj < ri || (ri == rj && j < i) {
			return 1
		}
		return 0
	})
	newLeaderAckN.CmdIds = []CommandId{}
	newLeaderAckN.Phases = []int{}
	newLeaderAckN.Cmds = []state.Command{}
	newLeaderAckN.Deps = []SDep{}
	for _, i := range idx {
		cmdId := cmdIds[i]
		cmd := cmds[i]
		dep := deps[i]
		newLeaderAckN.CmdIds = append(newLeaderAckN.CmdIds, cmdId)
		newLeaderAckN.Phases = append(newLeaderAckN.Phases, phases[i])
		newLeaderAckN.Cmds = append(newLeaderAckN.Cmds, cmd)
		newLeaderAckN.Deps = append(newLeaderAckN.Deps, dep)
	}
	ghostReport(newLeaderAckN) // GHOST (L2)
}

// syncEntry gives a descriptor its command as an MSync has it; the
// descriptor's own goroutine (or the run loop, for a sequential one) sets its
// fields and delivers it.
type syncEntry struct {
	propose *defs.GPropose
	cmd     state.Command
	dep     Dep
}

func (r *Replica) handleSync(msg *MSync) {
	if r.ballot > msg.Ballot || (r.ballot == msg.Ballot && r.status == NORMAL) {
		return
	}

	if r.status == NORMAL {
		r.recStart = time.Now()
		r.repchan.stop()
		r.stopDescs()
	}

	// the proposals the MSync lacks are proposed again in the new ballot
	// (as new ones: R4)
	reproposed := []*defs.GPropose{}
	for _, cmdId := range sortedProposes(r.proposes) {
		if _, exists := msg.Phases[cmdId]; !exists {
			reproposed = append(reproposed, r.proposes[cmdId])
			delete(r.proposes, cmdId)
		}
	}

	// clear cmdDescs:
	r.cmdDescs.IterCb(func(_ string, v interface{}) {
		desc := v.(*commandDesc)
		desc.msgs = nil
		desc.stopChan = nil
		desc.slowPathH.Free()
		desc.fastPathH.Free()
		r.freeDesc(desc)
	})

	// S5: the state is the MSync's: the executions since the last MSync
	// (the old leader's optimistic ones among them) are undone; the MSync
	// has the whole history (R3), executed again below
	r.State = state.InitState()
	dkeys := []string{}
	r.delivered.IterCb(func(k string, _ interface{}) {
		dkeys = append(dkeys, k)
	})
	for _, k := range dkeys {
		r.delivered.Remove(k)
	}
	r.deliveredAny.Store(false)
	r.execL.Lock()
	r.execLog = nil
	if SyncHook != nil {
		SyncHook(r.Id, msg.Ballot)
	}
	r.execL.Unlock()

	r.cntL.Lock()
	r.routineCount = 0
	r.cntL.Unlock()
	r.cmdDescs = cmap.New()
	r.proposeDeps = make(map[CommandId]Dep)
	r.status = NORMAL
	r.ballotL.Lock()
	r.ballot = msg.Ballot
	r.ballotL.Unlock()
	r.cballot = msg.Ballot
	r.lastSync = msg
	if r.fixedMajority {
		r.FQ = r.qs.AQ(r.ballot)
	}
	r.repchan = NewReplyChan(r)
	r.historySize = 0
	ghostTakeSync(msg.Ballot) // GHOST (L2)

	// the new ballot's acceptances: the MSync's commands (N2)
	r.acceptL.Lock()
	r.accepted = make(map[CommandId]struct{})
	for cmdId := range msg.Phases {
		r.accepted[cmdId] = struct{}{}
	}
	r.waiting = make(map[CommandId][]CommandId)
	r.rechecks = nil
	r.acceptL.Unlock()

	// R5: one order, the dependencies' (a deterministic topological sort);
	// the new ballot's key dependencies are the order's: a command proposed
	// now depends on the last recovered ones of its key
	order := syncOrder(msg)
	r.keys = make(map[state.Key]keyInfo)
	// F2: the ballot's paths start empty at every replica, its leader's
	// included: a hash log's entry of an earlier ballot (a command no leader
	// acknowledged, an acknowledgement stored for a proposal that has not
	// come) would make a follower's path hash the leader's for a different
	// sequence. (A command of the MSync is in no path: it is ordered.)
	r.hlog = make(map[state.Key]*HashLog)
	r.pendingHashUpds = make(map[CommandId]*UpdateEntry)
	r.handled = nil
	for _, cmdId := range order {
		cmd := msg.Cmds[cmdId]
		for _, k := range keysOf(cmd) {
			info, exists := r.keys[k]
			if !exists {
				info = newLightKeyInfo()
				r.keys[k] = info
			}
			info.add(cmd, cmdId)
		}
	}

	// every MSync command, committed: executed in the order
	for _, cmdId := range order {
		propose, exists := r.proposes[cmdId]
		if !exists {
			propose = &defs.GPropose{Propose: &defs.Propose{
				CommandId: cmdId.SeqNum,
				ClientId:  cmdId.ClientId,
				Command:   msg.Cmds[cmdId],
			}}
			// a later proposal of it is a duplicate (R4)
			r.proposes[cmdId] = propose
		}
		dep := msg.Deps[cmdId]
		if dep == nil {
			dep = Dep{}
		}
		r.getCmdDesc(cmdId, &syncEntry{
			propose: propose,
			cmd:     msg.Cmds[cmdId],
			dep:     dep,
		}, nil)
	}

	// S6, C2: the clients get no answer without a result. The new leader
	// answers each command when it executes it (the reply channel's MReply,
	// with the result); a follower acknowledges each one in the new ballot,
	// to its client: with the leader's MReply, a slow quorum of the new
	// ballot. (No MAccept: a command the MSync lacks is not chosen; it is
	// proposed again.)
	if r.Id != r.leader() {
		for _, cmdId := range order {
			lightSlowAck := &MLightSlowAck{
				Replica: r.Id,
				Ballot:  r.ballot,
				CmdId:   cmdId,
			}
			r.sender.SendToClient(cmdId.ClientId, lightSlowAck, r.cs.lightSlowAckRPC)
		}
	}

	for _, propose := range reproposed {
		go func(propose *defs.GPropose) {
			r.ProposeChan <- propose
		}(propose)
	}

	log.Println("Recovered!")
	log.Println("Ballot:", r.ballot)
	log.Println("FQ:", r.FQ, "SQ:", r.SQ)
	// Verification workaround: the duration is printed as an int64 of nanoseconds (Perennial has
	// time.Duration's methods by name only); only this log line's text differs.
	log.Println("recovered in (ns)", int64(time.Now().Sub(r.recStart)))
}

// handleSyncEntry sets the descriptor's fields from the MSync and delivers
// it (by the descriptor's owner).
func (r *Replica) handleSyncEntry(e *syncEntry, desc *commandDesc, cmdId CommandId) {
	desc.propose = e.propose
	desc.cmd = e.cmd
	desc.dep = e.dep
	desc.proposeDep = e.dep
	desc.phase = COMMIT
	ghostCommit(r.ballot, cmdId) // GHOST (L2)
	for _, d := range e.dep {
		depDesc := r.getCmdDesc(d, nil, nil)
		if depDesc == nil {
			continue
		}
		depDesc.successorsL.Lock()
		depDesc.successors = append(depDesc.successors, cmdId)
		depDesc.successorsL.Unlock()
	}
	r.deliver(desc, cmdId)
}

func sortedProposes(m map[CommandId]*defs.GPropose) []CommandId {
	ids := make([]CommandId, 0, len(m))
	for id := range m {
		ids = append(ids, id)
	}
	slices.SortFunc(ids, cmdIdCmp)
	return ids
}

// syncOrder is the MSync's commands in their dependencies' order
// (recOrder's: smallest id first among the ready ones).
func syncOrder(msg *MSync) []CommandId {
	kept := make(map[CommandId]*recEntry)
	for cmdId := range msg.Phases {
		kept[cmdId] = &recEntry{cmd: msg.Cmds[cmdId], dep: msg.Deps[cmdId]}
	}
	return recOrder(kept, sortedIds(kept))
}

// stopDescs stops every descriptor goroutine: after it returns, none runs.
// SW-F1: a goroutine not yet stopped can create a dependency's descriptor
// (and its goroutine) in a shard already visited (getCmdDesc(dep, nil, nil));
// so the iteration is repeated until one finds no active goroutine: after a
// round's Wait, the goroutines it stopped have ended, and the descriptors
// they created are in cmdDescs for the next round.
// SWB-14 (P7): a round that finds none is not enough: a goroutine retiring
// on its history slot may have left cmdDescs before the round reached its
// shard, and still run. Every goroutine gives its routineCount back before it
// leaves cmdDescs (handleMsg's slot case) or answers a stop request
// (handleDesc), so stopDescs returns when a round stopped none and
// routineCount is 0 (<= 0: a goroutine left over from an earlier epoch cannot
// make it loop forever): no goroutine registered in routineCount runs.
func (r *Replica) stopDescs() {
	for {
		// Verification workaround (P10, no behaviour change): one WaitGroup per
		// stop request, each waited on after the round, instead of one shared
		// WaitGroup (the round still waits for every goroutine it signalled).
		var wgs []*sync.WaitGroup
		r.cmdDescs.IterCb(func(_ string, v interface{}) {
			desc := v.(*commandDesc)
			if desc.active && !desc.seq {
				wg := new(sync.WaitGroup)
				wg.Add(1)
				desc.stopChan <- wg
				wgs = append(wgs, wg)
			}
		})
		for _, wg := range wgs {
			wg.Wait()
		}
		if len(wgs) == 0 {
			r.cntL.Lock()
			running := r.routineCount
			r.cntL.Unlock()
			if running <= 0 {
				break
			}
		}
	}

	// TODO: maybe add to history even if stopped this way ?
}

func (r *Replica) reinitNewLeaderAckNs(b int32) {
	r.newLeaderAckNsBallot = b
	accept := func(_, _ interface{}) bool {
		return true
	}
	free := func(_ interface{}) {}
	Q := replica.NewMajorityOf(r.N)
	r.newLeaderAckNs = r.newLeaderAckNs.ReinitMsgSet(Q, accept, free, r.handleNewLeaderAckNs)
}
