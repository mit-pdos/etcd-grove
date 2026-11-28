// Copyright IBM Corp. 2013, 2026
// SPDX-License-Identifier: MPL-2.0

package raft

import (
	"bytes"
	"errors"
	"fmt"
	"io"
	"strings"
	"sync/atomic"
	"time"
)

const (
	minCheckInterval          = 10 * time.Millisecond
	oldestLogGaugeInterval    = 10 * time.Second
	rpcUnexpectedCommandError = "unexpected command"
)

var (
	keyCurrentTerm  = []byte("CurrentTerm")
	keyLastVoteTerm = []byte("LastVoteTerm")
	keyLastVoteCand = []byte("LastVoteCand")
)

// getRPCHeader returns an initialized RPCHeader struct for the given
// Raft instance. This structure is sent along with RPC requests and
// responses.
func (r *Raft) getRPCHeader() RPCHeader {
	return RPCHeader{
		ProtocolVersion: r.config().ProtocolVersion,
		ID:              []byte(r.config().LocalID),
		Addr:            r.trans.EncodePeer(r.config().LocalID, r.localAddr),
	}
}

// checkRPCHeader houses logic about whether this instance of Raft can process
// the given RPC message.
func (r *Raft) checkRPCHeader(rpc RPC) error {
	// Get the header off the RPC message.
	wh, ok := rpc.Command.(WithRPCHeader)
	if !ok {
		return fmt.Errorf("RPC does not have a header")
	}
	header := wh.GetRPCHeader()

	// First check is to just make sure the code can understand the
	// protocol at all.
	if header.ProtocolVersion < ProtocolVersionMin ||
		header.ProtocolVersion > ProtocolVersionMax {
		return ErrUnsupportedProtocol
	}

	// Second check is whether we should support this message, given the
	// current protocol we are configured to run. This will drop support
	// for protocol version 0 starting at protocol version 2, which is
	// currently what we want, and in general support one version back. We
	// may need to revisit this policy depending on how future protocol
	// changes evolve.
	if header.ProtocolVersion < r.config().ProtocolVersion-1 {
		return ErrUnsupportedProtocol
	}

	return nil
}

// getSnapshotVersion returns the snapshot version that should be used when
// creating snapshots, given the protocol version in use.
func getSnapshotVersion(protocolVersion ProtocolVersion) SnapshotVersion {
	// Right now we only have two versions and they are backwards compatible
	// so we don't need to look at the protocol version.
	return 1
}

// commitTuple is used to send an index that was committed,
// with an optional associated future that should be invoked.
type commitTuple struct {
	log    *Log
	future *logFuture
}

// leaderState is state that is used while we are a leader.
type leaderState struct {
	leadershipTransferInProgress int32 // indicates that a leadership transfer is in progress.
	commitCh                     chan struct{}
	commitment                   *commitment
	inflight                     []*logFuture // logFutures in log index order (a list.List upstream)
	replState                    map[ServerID]*followerReplication
	notify                       map[*verifyFuture]struct{}
	stepDown                     chan struct{}
}

// setLeader is used to modify the current leader Address and ID of the cluster
func (r *Raft) setLeader(leaderAddr ServerAddress, leaderID ServerID) {
	r.leaderLock.Lock()
	oldLeaderAddr := r.leaderAddr
	r.leaderAddr = leaderAddr
	oldLeaderID := r.leaderID
	r.leaderID = leaderID
	r.leaderLock.Unlock()
	if oldLeaderAddr != leaderAddr || oldLeaderID != leaderID {
		r.observe(LeaderObservation{Leader: leaderAddr, LeaderAddr: leaderAddr, LeaderID: leaderID})
	}
}

// requestConfigChange is a helper for the above functions that make
// configuration change requests. 'req' describes the change. For timeout,
// see AddVoter.
func (r *Raft) requestConfigChange(req configurationChangeRequest, timeout time.Duration) IndexFuture {
	var timer <-chan time.Time
	if timeout > 0 {
		timer = time.After(timeout)
	}
	future := &configurationChangeFuture{
		req: req,
	}
	future.init()
	select {
	case <-timer:
		return errorFuture{ErrEnqueueTimeout}
	case r.configurationChangeCh <- future:
		return future
	case <-r.shutdownCh:
		return errorFuture{ErrRaftShutdown}
	}
}

// run the main thread that handles leadership and RPC requests.
func (r *Raft) run() {
	for {
		// Check if we are doing a shutdown
		select {
		case <-r.shutdownCh:
			// Clear the leader to prevent forwarding
			r.setLeader("", "")
			return
		default:
		}

		switch r.getState() {
		case Follower:
			r.runFollower()
		case Candidate:
			r.runCandidate()
		case Leader:
			r.runLeader()
		}
	}
}

// runFollower runs the main loop while in the follower state.
func (r *Raft) runFollower() {
	didWarn := false
	heartbeatTimer := randomTimeout(r.config().HeartbeatTimeout)

	for r.getState() == Follower {

		select {
		case rpc := <-r.rpcCh:
			r.processRPC(rpc)

		case c := <-r.configurationChangeCh:
			// Reject any operations since we are not the leader
			c.respond(ErrNotLeader)

		case a := <-r.applyCh:
			// Reject any operations since we are not the leader
			a.respond(ErrNotLeader)

		case v := <-r.verifyCh:
			// Reject any operations since we are not the leader
			v.respond(ErrNotLeader)

		case ur := <-r.userRestoreCh:
			// Reject any restores since we are not the leader
			ur.respond(ErrNotLeader)

		case l := <-r.leadershipTransferCh:
			// Reject any operations since we are not the leader
			l.respond(ErrNotLeader)

		case c := <-r.configurationsCh:
			c.configurations = r.configurations.Clone()
			c.respond(nil)

		case b := <-r.bootstrapCh:
			b.respond(r.liveBootstrap(b.configuration))

		case <-r.leaderNotifyCh:
			//  Ignore since we are not the leader

		case <-r.followerNotifyCh:
			heartbeatTimer = time.After(0)

		case <-heartbeatTimer:
			// Restart the heartbeat timer
			hbTimeout := r.config().HeartbeatTimeout
			heartbeatTimer = randomTimeout(hbTimeout)

			// Check if we have had a successful contact
			lastContact := r.LastContact()
			if time.Since(lastContact) < hbTimeout {
				continue
			}

			// Heartbeat failed! Transition to the candidate state
			r.setLeader("", "")

			if r.configurations.latestIndex == 0 {
				if !didWarn {

					didWarn = true
				}
			} else if r.configurations.latestIndex == r.configurations.committedIndex &&
				!hasVote(r.configurations.latest, r.localID) {
				if !didWarn {

					didWarn = true
				}
			} else {

				if hasVote(r.configurations.latest, r.localID) {

					r.setState(Candidate)
					return
				} else if !didWarn {

					didWarn = true
				}
			}

		case <-r.shutdownCh:
			return
		}
	}
}

// liveBootstrap attempts to seed an initial configuration for the cluster. See
// the Raft object's member BootstrapCluster for more details. This must only be
// called on the main thread, and only makes sense in the follower state.
func (r *Raft) liveBootstrap(configuration Configuration) error {
	if !hasVote(configuration, r.localID) {
		// Reject this operation since we are not a voter
		return ErrNotVoter
	}

	// Use the pre-init API to make the static updates.
	cfg := r.config()
	err := BootstrapCluster(&cfg, r.logs, r.stable, r.snapshots, r.trans, configuration)
	if err != nil {
		return err
	}

	// Make the configuration live.
	var entry Log
	if err := r.logs.GetLog(1, &entry); err != nil {
		panic(err)
	}
	r.setCurrentTerm(1)
	r.setLastLog(entry.Index, entry.Term)
	return r.processConfigurationLogEntry(&entry)
}

// runCandidate runs the main loop while in the candidate state.
func (r *Raft) runCandidate() {
	term := r.getCurrentTerm() + 1

	// Start vote for us, and set a timeout
	var voteCh <-chan *voteResult
	var prevoteCh <-chan *preVoteResult

	// check if pre-vote is active and that this is not a leader transfer.
	// Leader transfer do not perform prevote by design
	if !r.preVoteDisabled && !r.candidateFromLeadershipTransfer.Load() {
		prevoteCh = r.preElectSelf()
	} else {
		voteCh = r.electSelf()
	}

	// Make sure the leadership transfer flag is reset after each run. Having this
	// flag will set the field LeadershipTransfer in a RequestVoteRequest to true,
	// which will make other servers vote even though they have a leader already.
	// It is important to reset that flag, because this privilege could be abused
	// otherwise.
	defer func() { r.candidateFromLeadershipTransfer.Store(false) }()

	electionTimeout := r.config().ElectionTimeout
	electionTimer := randomTimeout(electionTimeout)

	// Tally the votes, need a simple majority
	preVoteGrantedVotes := 0
	preVoteRefusedVotes := 0
	grantedVotes := 0
	votesNeeded := r.quorumSize()

	for r.getState() == Candidate {

		select {
		case rpc := <-r.rpcCh:
			r.processRPC(rpc)
		case preVote := <-prevoteCh:
			// This a pre-vote case it should trigger a "real" election if the pre-vote is won.

			// Check if the term is greater than ours, bail
			if preVote.Term > term {

				r.setState(Follower)
				r.setCurrentTerm(preVote.Term)
				return
			}

			// Check if the preVote is granted
			if preVote.Granted {
				preVoteGrantedVotes++

			} else {
				preVoteRefusedVotes++

			}

			// Check if we've won the pre-vote and proceed to election if so
			if preVoteGrantedVotes >= votesNeeded {

				preVoteGrantedVotes = 0
				preVoteRefusedVotes = 0
				electionTimer = randomTimeout(electionTimeout)
				prevoteCh = nil
				// The election asks the voters of the latest configuration, which may have changed since the
				// pre-vote began (a TimeoutNow keeps a candidate from stepping down on AppendEntries of its term,
				// which may store a configuration entry): count the votes against that configuration's quorum.
				// See verify/issues/candidate-stale-quorum.md.
				votesNeeded = r.quorumSize()
				voteCh = r.electSelf()
			}
			// Check if we've lost the pre-vote and wait for the election to timeout so we can do another time of
			// prevote.
			if preVoteRefusedVotes >= votesNeeded {

			}
		case vote := <-voteCh:
			// Check if the term is greater than ours, bail
			if vote.Term > r.getCurrentTerm() {

				r.setState(Follower)
				r.setCurrentTerm(vote.Term)
				return
			}

			// Check if the vote is granted
			if vote.Granted {
				grantedVotes++

			}

			// Check if we've become the leader
			if grantedVotes >= votesNeeded {

				r.setState(Leader)
				r.setLeader(r.localAddr, r.localID)
				return
			}
		case c := <-r.configurationChangeCh:
			// Reject any operations since we are not the leader
			c.respond(ErrNotLeader)

		case a := <-r.applyCh:
			// Reject any operations since we are not the leader
			a.respond(ErrNotLeader)

		case v := <-r.verifyCh:
			// Reject any operations since we are not the leader
			v.respond(ErrNotLeader)

		case ur := <-r.userRestoreCh:
			// Reject any restores since we are not the leader
			ur.respond(ErrNotLeader)

		case l := <-r.leadershipTransferCh:
			// Reject any operations since we are not the leader
			l.respond(ErrNotLeader)

		case c := <-r.configurationsCh:
			c.configurations = r.configurations.Clone()
			c.respond(nil)

		case b := <-r.bootstrapCh:
			b.respond(ErrCantBootstrap)

		case <-r.leaderNotifyCh:
			//  Ignore since we are not the leader

		case <-r.followerNotifyCh:
			if electionTimeout != r.config().ElectionTimeout {
				electionTimeout = r.config().ElectionTimeout
				electionTimer = randomTimeout(electionTimeout)
			}

		case <-electionTimer:
			// Election failed! Restart the election. We simply return,
			// which will kick us back into runCandidate

			return

		case <-r.shutdownCh:
			return
		}
	}
}

func (r *Raft) setLeadershipTransferInProgress(v bool) {
	if v {
		atomic.StoreInt32(&r.leaderState.leadershipTransferInProgress, 1)
	} else {
		atomic.StoreInt32(&r.leaderState.leadershipTransferInProgress, 0)
	}
}

func (r *Raft) getLeadershipTransferInProgress() bool {
	v := atomic.LoadInt32(&r.leaderState.leadershipTransferInProgress)
	return v == 1
}

func (r *Raft) setupLeaderState() {
	r.leaderState.commitCh = make(chan struct{}, 1)
	r.leaderState.commitment = newCommitment(r.leaderState.commitCh,
		r.configurations.latest,
		r.getLastIndex()+1 /* first index that may be committed in this term */)
	r.leaderState.inflight = make([]*logFuture, 0)
	r.leaderState.replState = make(map[ServerID]*followerReplication)
	r.leaderState.notify = make(map[*verifyFuture]struct{})
	r.leaderState.stepDown = make(chan struct{}, 1)
}

// runLeader runs the main loop while in leader state. Do the setup here and drop into
// the leaderLoop for the hot loop.
func (r *Raft) runLeader() {

	// Notify that we are the leader
	overrideNotifyBool(r.leaderCh, true)

	// Store the notify chan. It's not reloadable so shouldn't change before the
	// defer below runs, but this makes sure we always notify the same chan if
	// ever for both gaining and losing leadership.
	notify := r.config().NotifyCh

	// Push to the notify channel if given
	if notify != nil {
		select {
		case notify <- true:
		case <-r.shutdownCh:
			// make sure push to the notify channel ( if given )
			select {
			case notify <- true:
			default:
			}
		}
	}

	// setup leader state. This is only supposed to be accessed within the
	// leaderloop.
	r.setupLeaderState()

	// Run a background go-routine to emit metrics on log age

	// Cleanup state on step down
	defer func() {

		// Since we were the leader previously, we update our
		// last contact time when we step down, so that we are not
		// reporting a last contact time from before we were the
		// leader. Otherwise, to a client it would seem our data
		// is extremely stale.
		r.setLastContact()

		// Stop replication
		for _, p := range r.leaderState.replState {
			close(p.stopCh)
		}

		// Respond to all inflight operations
		for _, f := range r.leaderState.inflight {
			f.respond(ErrLeadershipLost)
		}

		// Respond to any pending verify requests
		for future := range r.leaderState.notify {
			future.respond(ErrLeadershipLost)
		}

		// Clear all the state
		r.leaderState.commitCh = nil
		r.leaderState.commitment = nil
		r.leaderState.inflight = nil
		r.leaderState.replState = nil
		r.leaderState.notify = nil
		r.leaderState.stepDown = nil

		// If we are stepping down for some reason, no known leader.
		// We may have stepped down due to an RPC call, which would
		// provide the leader, so we cannot always blank this out.
		r.leaderLock.Lock()
		if r.leaderAddr == r.localAddr && r.leaderID == r.localID {
			r.leaderAddr = ""
			r.leaderID = ""
		}
		r.leaderLock.Unlock()

		// Notify that we are not the leader
		overrideNotifyBool(r.leaderCh, false)

		// Push to the notify channel if given
		if notify != nil {
			select {
			case notify <- false:
			case <-r.shutdownCh:
				// On shutdown, make a best effort but do not block
				select {
				case notify <- false:
				default:
				}
			}
		}
	}()

	// Start a replication routine for each peer
	r.startStopReplication()

	// Dispatch a no-op log entry first. This gets this leader up to the latest
	// possible commit index, even in the absence of client commands. This used
	// to append a configuration entry instead of a noop. However, that permits
	// an unbounded number of uncommitted configurations in the log. We now
	// maintain that there exists at most one uncommitted configuration entry in
	// any log, so we have to do proper no-ops here.
	noop := &logFuture{log: Log{Type: LogNoop}}
	r.dispatchLogs([]*logFuture{noop})

	// Sit in the leader loop until we step down
	r.leaderLoop()
}

// startStopReplication will set up state and start asynchronous replication to
// new peers, and stop replication to removed peers. Before removing a peer,
// it'll instruct the replication routines to try to replicate to the current
// index. This must only be called from the main thread.
func (r *Raft) startStopReplication() {
	inConfig := make(map[ServerID]bool, len(r.configurations.latest.Servers))
	lastIdx := r.getLastIndex()

	// Start replication goroutines that need starting
	for _, server := range r.configurations.latest.Servers {
		if server.ID == r.localID {
			continue
		}

		inConfig[server.ID] = true

		s, ok := r.leaderState.replState[server.ID]
		if !ok {

			s = &followerReplication{
				peer:                server,
				commitment:          r.leaderState.commitment,
				stopCh:              make(chan uint64, 1),
				triggerCh:           make(chan struct{}, 1),
				triggerDeferErrorCh: make(chan *deferError, 1),
				currentTerm:         r.getCurrentTerm(),
				nextIndex:           lastIdx + 1,
				lastContact:         time.Now(),
				notify:              make(map[*verifyFuture]struct{}),
				notifyCh:            make(chan struct{}, 1),
				stepDown:            r.leaderState.stepDown,
			}

			r.leaderState.replState[server.ID] = s
			r.goFunc(func() { r.replicate(s) })
			asyncNotifyCh(s.triggerCh)
			r.observe(PeerObservation{Peer: server, Removed: false})
		} else if ok {

			s.peerLock.RLock()
			peer := s.peer
			s.peerLock.RUnlock()

			if peer.Address != server.Address {

				s.peerLock.Lock()
				s.peer = server
				s.peerLock.Unlock()
			}
		}
	}

	// Stop replication goroutines that need stopping
	for serverID, repl := range r.leaderState.replState {
		if inConfig[serverID] {
			continue
		}
		// Replicate up to lastIdx and stop

		repl.stopCh <- lastIdx
		close(repl.stopCh)
		delete(r.leaderState.replState, serverID)
		r.observe(PeerObservation{Peer: repl.peer, Removed: true})
	}

	// Update peers metric

}

// configurationChangeChIfStable returns r.configurationChangeCh if it's safe
// to process requests from it, or nil otherwise. This must only be called
// from the main thread.
//
// Note that if the conditions here were to change outside of leaderLoop to take
// this from nil to non-nil, we would need leaderLoop to be kicked.
func (r *Raft) configurationChangeChIfStable() chan *configurationChangeFuture {
	// Have to wait until:
	// 1. The latest configuration is committed, and
	// 2. This leader has committed some entry (the noop) in this term
	//    https://groups.google.com/forum/#!msg/raft-dev/t4xj6dJTP6E/d2D9LrWRza8J
	if r.configurations.latestIndex == r.configurations.committedIndex &&
		r.getCommitIndex() >= r.leaderState.commitment.startIndex {
		return r.configurationChangeCh
	}
	return nil
}

// leaderLoop is the hot loop for a leader. It is invoked
// after all the various leader setup is done.
func (r *Raft) leaderLoop() {
	// stepDown is used to track if there is an inflight log that
	// would cause us to lose leadership (specifically a RemovePeer of
	// ourselves). If this is the case, we must not allow any logs to
	// be processed in parallel, otherwise we are basing commit on
	// only a single peer (ourself) and replicating to an undefined set
	// of peers.
	stepDown := false
	// This is only used for the first lease check, we reload lease below
	// based on the current config value.
	lease := time.After(r.config().LeaderLeaseTimeout)

	for r.getState() == Leader {

		select {
		case rpc := <-r.rpcCh:
			r.processRPC(rpc)

		case <-r.leaderState.stepDown:
			r.setState(Follower)

		case future := <-r.leadershipTransferCh:
			if r.getLeadershipTransferInProgress() {

				future.respond(ErrLeadershipTransferInProgress)
				continue
			}

			// When we are leaving leaderLoop, we are no longer
			// leader, so we should stop transferring.
			leftLeaderLoop := make(chan struct{})
			defer func() { close(leftLeaderLoop) }()

			stopCh := make(chan struct{})
			doneCh := make(chan error, 1)

			// This is intentionally being setup outside of the
			// leadershipTransfer function. Because the TimeoutNow
			// call is blocking and there is no way to abort that
			// in case eg the timer expires.
			// The leadershipTransfer function is controlled with
			// the stopCh and doneCh.
			// No matter how this exits, have this function set
			// leadership transfer to false before we return
			//
			// Note that this leaves a window where callers of
			// LeadershipTransfer() and LeadershipTransferToServer()
			// may start executing after they get their future but before
			// this routine has set leadershipTransferInProgress back to false.
			// It may be safe to modify things such that setLeadershipTransferInProgress
			// is set to false before calling future.Respond, but that still needs
			// to be tested and this situation mirrors what callers already had to deal with.
			go func() {
				defer r.setLeadershipTransferInProgress(false)
				select {
				case <-time.After(r.config().ElectionTimeout):
					close(stopCh)
					err := fmt.Errorf("leadership transfer timeout")

					future.respond(err)
					<-doneCh
				case <-leftLeaderLoop:
					close(stopCh)

					future.respond(nil)
					<-doneCh
				case err := <-doneCh:
					if err != nil {

						future.respond(err)
					} else {
						// Wait for up to ElectionTimeout before flagging the
						// leadership transfer as done and unblocking applies in
						// the leaderLoop.
						select {
						case <-time.After(r.config().ElectionTimeout):
							err := fmt.Errorf("leadership transfer timeout")

							future.respond(err)
						case <-leftLeaderLoop:

							future.respond(nil)
						}
					}
				}
			}()

			// leaderState.replState is accessed here before
			// starting leadership transfer asynchronously because
			// leaderState is only supposed to be accessed in the
			// leaderloop.
			id := future.ID
			address := future.Address
			if id == nil {
				s := r.pickServer()
				if s != nil {
					id = &s.ID
					address = &s.Address
				} else {
					doneCh <- fmt.Errorf("cannot find peer")
					continue
				}
			}
			state, ok := r.leaderState.replState[*id]
			if !ok {
				doneCh <- fmt.Errorf("cannot find replication state for %s", *id)
				continue
			}
			r.setLeadershipTransferInProgress(true)
			go r.leadershipTransfer(*id, *address, state, stopCh, doneCh)

		case <-r.leaderState.commitCh:
			// Process the newly committed entries
			oldCommitIndex := r.getCommitIndex()
			commitIndex := r.leaderState.commitment.getCommitIndex()
			r.setCommitIndex(commitIndex)

			// New configuration has been committed, set it as the committed
			// value.
			if r.configurations.latestIndex > oldCommitIndex &&
				r.configurations.latestIndex <= commitIndex {
				r.setCommittedConfiguration(r.configurations.latest, r.configurations.latestIndex)
				if !hasVote(r.configurations.committed, r.localID) {
					stepDown = true
				}
			}

			groupReady := 0
			groupFutures := make(map[uint64]*logFuture)
			var lastIdxInGroup uint64

			// Pull all inflight logs that are committed off the queue.
			for _, commitLog := range r.leaderState.inflight {
				idx := commitLog.log.Index
				if idx > commitIndex {
					// Don't go past the committed index
					break
				}

				// Measure the commit time

				groupReady++
				groupFutures[idx] = commitLog
				lastIdxInGroup = idx
			}

			// Process the group
			if groupReady != 0 {
				r.processLogs(lastIdxInGroup, groupFutures)

				// The group is a prefix of inflight
				r.leaderState.inflight = r.leaderState.inflight[groupReady:]
			}

			// Measure the time to enqueue batch of logs for FSM to apply

			// Count the number of logs enqueued

			if stepDown {
				if r.config().ShutdownOnRemove {

					r.Shutdown()
				} else {

					r.setState(Follower)
				}
			}

		case v := <-r.verifyCh:
			if v.quorumSize == 0 {
				// Just dispatched, start the verification
				r.verifyLeader(v)
			} else if v.votes < v.quorumSize {
				// Early return, means there must be a new leader

				r.setState(Follower)
				delete(r.leaderState.notify, v)
				for _, repl := range r.leaderState.replState {
					repl.cleanNotify(v)
				}
				v.respond(ErrNotLeader)

			} else {
				// Quorum of members agree, we are still leader
				delete(r.leaderState.notify, v)
				for _, repl := range r.leaderState.replState {
					repl.cleanNotify(v)
				}
				// Respond once the FSM has applied every entry committed so far (processLogs has sent them all to
				// it), so that a read of the FSM after VerifyLeader reflects every entry committed before it was
				// called: Raft's read-only queries wait for the state machine to reach the read index (Ongaro's
				// dissertation, 6.4, step 4). The FSM goroutine responds after the batches sent before v.
				select {
				case r.fsmMutateCh <- interface{}(v): // explicit conversion: goose translates a select send's value without converting it to the channel's element type (Perennial goose/goose.go:2448, `ctx.expr(c.Value)`; notes/dsv-hraft.md)
				case <-r.shutdownCh:
					v.respond(ErrRaftShutdown)
				}
			}

		case future := <-r.userRestoreCh:
			if r.getLeadershipTransferInProgress() {

				future.respond(ErrLeadershipTransferInProgress)
				continue
			}
			err := r.restoreUserSnapshot(future.meta, future.reader)
			future.respond(err)

		case future := <-r.configurationsCh:
			if r.getLeadershipTransferInProgress() {

				future.respond(ErrLeadershipTransferInProgress)
				continue
			}
			future.configurations = r.configurations.Clone()
			future.respond(nil)

		case future := <-r.configurationChangeChIfStable():
			if r.getLeadershipTransferInProgress() {

				future.respond(ErrLeadershipTransferInProgress)
				continue
			}
			r.appendConfigurationEntry(future)

		case b := <-r.bootstrapCh:
			b.respond(ErrCantBootstrap)

		case newLog := <-r.applyCh:
			if r.getLeadershipTransferInProgress() {

				newLog.respond(ErrLeadershipTransferInProgress)
				continue
			}
			// Group commit, gather all the ready commits
			ready := []*logFuture{newLog}
			for i := 0; i < r.config().MaxAppendEntries; i++ {
				empty := false
				select {
				case newLog := <-r.applyCh:
					ready = append(ready, newLog)
				default:
					empty = true
				}
				if empty {
					break
				}
			}

			// Dispatch the logs
			if stepDown {
				// we're in the process of stepping down as leader, don't process anything new
				for i := range ready {
					ready[i].respond(ErrNotLeader)
				}
			} else {
				r.dispatchLogs(ready)
			}

		case <-lease:
			// Check if we've exceeded the lease, potentially stepping down
			maxDiff := r.checkLeaderLease()

			// Next check interval should adjust for the last node we've
			// contacted, without going negative
			checkInterval := r.config().LeaderLeaseTimeout - maxDiff
			if checkInterval < minCheckInterval {
				checkInterval = minCheckInterval
			}

			// Renew the lease timer
			lease = time.After(checkInterval)

		case <-r.leaderNotifyCh:
			for _, repl := range r.leaderState.replState {
				asyncNotifyCh(repl.notifyCh)
			}

		case <-r.followerNotifyCh:
			//  Ignore since we are not a follower

		case <-r.shutdownCh:
			return
		}
	}
}

// verifyLeader must be called from the main thread for safety.
// Causes the followers to attempt an immediate heartbeat.
func (r *Raft) verifyLeader(v *verifyFuture) {
	// The leader votes for itself only if it is a voter of its latest configuration: after a RemoveServer or a
	// DemoteVoter of itself, until that entry commits, it leads a configuration it has no vote in (quorumSize and
	// the commitment leave it out). See verify/issues/verify-self-vote-nonvoter.md.
	v.votes = 0
	if hasVote(r.configurations.latest, r.localID) {
		v.votes = 1
	}

	// Set the quorum size, hot-path for single node
	v.quorumSize = r.quorumSize()
	if v.votes >= v.quorumSize {
		// As when a quorum answers (leaderLoop): respond once the FSM has applied every entry committed so far.
		// See verify/issues/verify-single-voter-fsm-lag.md.
		select {
		case r.fsmMutateCh <- interface{}(v): // explicit conversion: goose translates a select send's value without converting it to the channel's element type (Perennial goose/goose.go:2448, `ctx.expr(c.Value)`; notes/dsv-hraft.md)
		case <-r.shutdownCh:
			v.respond(ErrRaftShutdown)
		}
		return
	}

	// Track this request
	v.notifyCh = r.verifyCh
	r.leaderState.notify[v] = struct{}{}

	// Trigger immediate heartbeats. Only the voters of the latest configuration vote: quorumSize counts them, and
	// a non-voter's heartbeat response says nothing about who the voters follow. See
	// verify/issues/verify-nonvoter-vote.md (upstream #725).
	for id, repl := range r.leaderState.replState {
		if !hasVote(r.configurations.latest, id) {
			continue
		}
		repl.notifyLock.Lock()
		repl.notify[v] = struct{}{}
		repl.notifyLock.Unlock()
		asyncNotifyCh(repl.notifyCh)
	}
}

// leadershipTransfer is doing the heavy lifting for the leadership transfer.
func (r *Raft) leadershipTransfer(id ServerID, address ServerAddress, repl *followerReplication, stopCh chan struct{}, doneCh chan error) {
	// make sure we are not already stopped
	select {
	case <-stopCh:
		doneCh <- nil
		return
	default:
	}

	for atomic.LoadUint64(&repl.nextIndex) <= r.getLastIndex() {
		err := &deferError{}
		err.init()
		repl.triggerDeferErrorCh <- err
		select {
		case err := <-err.errCh:
			if err != nil {
				doneCh <- err
				return
			}
		case <-stopCh:
			doneCh <- nil
			return
		}
	}

	// Step ?: the thesis describes in chap 6.4.1: Using clocks to reduce
	// messaging for read-only queries. If this is implemented, the lease
	// has to be reset as well, in case leadership is transferred. This
	// implementation also has a lease, but it serves another purpose and
	// doesn't need to be reset. The lease mechanism in our raft lib, is
	// setup in a similar way to the one in the thesis, but in practice
	// it's a timer that just tells the leader how often to check
	// heartbeats are still coming in.

	// Step 3: send TimeoutNow message to target server.
	err := r.trans.TimeoutNow(id, address, &TimeoutNowRequest{RPCHeader: r.getRPCHeader()}, &TimeoutNowResponse{})
	if err != nil {
		err = fmt.Errorf("failed to make TimeoutNow RPC to %v: %v", id, err)
	}
	doneCh <- err
}

// checkLeaderLease is used to check if we can contact a quorum of nodes
// within the last leader lease interval. If not, we need to step down,
// as we may have lost connectivity. Returns the maximum duration without
// contact. This must only be called from the main thread.
func (r *Raft) checkLeaderLease() time.Duration {
	// Track contacted nodes, we can always contact ourself
	contacted := 0

	// Store lease timeout for this one check invocation as we need to refer to it
	// in the loop and would be confusing if it ever becomes reloadable and
	// changes between iterations below.
	leaseTimeout := r.config().LeaderLeaseTimeout

	// Check each follower
	var maxDiff time.Duration
	now := time.Now()
	for _, server := range r.configurations.latest.Servers {
		if server.Suffrage == Voter {
			if server.ID == r.localID {
				contacted++
				continue
			}
			f := r.leaderState.replState[server.ID]
			diff := now.Sub(f.LastContact())
			if diff <= leaseTimeout {
				contacted++
				if diff > maxDiff {
					maxDiff = diff
				}
			} else {
				// Log at least once at high value, then debug. Otherwise it gets very verbose.
				if diff <= 3*leaseTimeout {

				} else {

				}
			}

		}
	}

	// Verify we can contact a quorum
	quorum := r.quorumSize()
	if contacted < quorum {

		r.setState(Follower)

	}
	return maxDiff
}

// quorumSize is used to return the quorum size. This must only be called on
// the main thread.
// TODO: revisit usage
func (r *Raft) quorumSize() int {
	voters := 0
	for _, server := range r.configurations.latest.Servers {
		if server.Suffrage == Voter {
			voters++
		}
	}
	return voters/2 + 1
}

// restoreUserSnapshot is used to manually consume an external snapshot, such
// as if restoring from a backup. We will use the current Raft configuration,
// not the one from the snapshot, so that we can restore into a new cluster. We
// will also use the higher of the index of the snapshot, or the current index,
// and then add 1 to that, so we force a new state with a hole in the Raft log,
// so that the snapshot will be sent to followers and used for any new joiners.
// This can only be run on the leader, and returns a future that can be used to
// block until complete.
func (r *Raft) restoreUserSnapshot(meta *SnapshotMeta, reader io.Reader) error {

	// Sanity check the version.
	version := meta.Version
	if version < SnapshotVersionMin || version > SnapshotVersionMax {
		return fmt.Errorf("unsupported snapshot version %d", version)
	}

	// We don't support snapshots while there's a config change
	// outstanding since the snapshot doesn't have a means to
	// represent this state.
	committedIndex := r.configurations.committedIndex
	latestIndex := r.configurations.latestIndex
	if committedIndex != latestIndex {
		return fmt.Errorf("cannot restore snapshot now, wait until the configuration entry at %v has been applied (have applied %v)",
			latestIndex, committedIndex)
	}

	// Cancel any inflight requests.
	for _, f := range r.leaderState.inflight {
		f.respond(ErrAbortedByRestore)
	}
	r.leaderState.inflight = make([]*logFuture, 0)

	// We will overwrite the snapshot metadata with the current term,
	// an index that's greater than the current index, or the last
	// index in the snapshot. It's important that we leave a hole in
	// the index so we know there's nothing in the Raft log there and
	// replication will fault and send the snapshot.
	term := r.getCurrentTerm()
	lastIndex := r.getLastIndex()
	if meta.Index > lastIndex {
		lastIndex = meta.Index
	}
	lastIndex++

	// Dump the snapshot. Note that we use the latest configuration,
	// not the one that came with the snapshot.
	sink, err := r.snapshots.Create(version, lastIndex, term,
		r.configurations.latest, r.configurations.latestIndex, r.trans)
	if err != nil {
		return fmt.Errorf("failed to create snapshot: %v", err)
	}
	n, err := io.Copy(sink, reader)
	if err != nil {
		_ = sink.Cancel()
		return fmt.Errorf("failed to write snapshot: %v", err)
	}
	if n != meta.Size {
		_ = sink.Cancel()
		return fmt.Errorf("failed to write snapshot, size didn't match (%d != %d)", n, meta.Size)
	}
	if err := sink.Close(); err != nil {
		return fmt.Errorf("failed to close snapshot: %v", err)
	}

	// Restore the snapshot into the FSM. If this fails we are in a
	// bad state so we panic to take ourselves out.
	fsm := &restoreFuture{ID: sink.ID()}
	fsm.ShutdownCh = r.shutdownCh
	fsm.init()
	select {
	case r.fsmMutateCh <- interface{}(fsm): // explicit conversion: goose translates a select send's value without converting it to the channel's element type (Perennial goose/goose.go:2448, `ctx.expr(c.Value)`; notes/dsv-hraft.md)
	case <-r.shutdownCh:
		return ErrRaftShutdown
	}
	if err := fsm.Error(); err != nil {
		panic(fmt.Errorf("failed to restore snapshot: %v", err))
	}

	// We set the last log so it looks like we've stored the empty
	// index we burned. The last applied is set because we made the
	// FSM take the snapshot state, and we store the last snapshot
	// in the stable store since we created a snapshot as part of
	// this process.
	r.setLastLog(lastIndex, term)
	r.setLastApplied(lastIndex)
	r.setLastSnapshot(lastIndex, term)

	// Remove old logs if r.logs is a MonotonicLogStore. Log any errors and continue.
	if logs, ok := r.logs.(MonotonicLogStore); ok && logs.IsMonotonic() {
		if err := r.removeOldLogs(); err != nil {

		}
	}

	return nil
}

// appendConfigurationEntry changes the configuration and adds a new
// configuration entry to the log. This must only be called from the
// main thread.
func (r *Raft) appendConfigurationEntry(future *configurationChangeFuture) {
	configuration, err := nextConfiguration(r.configurations.latest, r.configurations.latestIndex, future.req)
	if err != nil {
		future.respond(err)
		return
	}

	// In pre-ID compatibility mode we translate all configuration changes
	// in to an old remove peer message, which can handle all supported
	// cases for peer changes in the pre-ID world (adding and removing
	// voters). Both add peer and remove peer log entries are handled
	// similarly on old Raft servers, but remove peer does extra checks to
	// see if a leader needs to step down. Since they both assert the full
	// configuration, then we can safely call remove peer for everything.
	if r.protocolVersion < 2 {
		future.log = Log{
			Type: LogRemovePeerDeprecated,
			Data: encodePeers(configuration, r.trans),
		}
	} else {
		future.log = Log{
			Type: LogConfiguration,
			Data: EncodeConfiguration(configuration),
		}
	}

	r.dispatchLogs([]*logFuture{&future.logFuture})
	index := future.Index()
	r.setLatestConfiguration(configuration, index)
	r.leaderState.commitment.setConfiguration(configuration)
	r.startStopReplication()
}

// dispatchLog is called on the leader to push a log to disk, mark it
// as inflight and begin replication of it.
func (r *Raft) dispatchLogs(applyLogs []*logFuture) {
	now := time.Now()

	term := r.getCurrentTerm()
	lastIndex := r.getLastIndex()

	n := len(applyLogs)
	logs := make([]*Log, n)

	for idx, applyLog := range applyLogs {
		applyLog.dispatch = now
		lastIndex++
		applyLog.log.Index = lastIndex
		applyLog.log.Term = term
		applyLog.log.AppendedAt = now
		logs[idx] = &applyLog.log
		r.leaderState.inflight = append(r.leaderState.inflight, applyLog)
	}

	commitIndex := r.getCommitIndex()
	r.tryStageCommitIndex(commitIndex)

	// Write the log entry locally
	if err := r.logs.StoreLogs(logs); err != nil {

		for _, applyLog := range applyLogs {
			applyLog.respond(err)
		}
		r.setState(Follower)
		return
	}
	r.leaderState.commitment.match(r.localID, lastIndex)

	// Update the last log since it's on disk now
	r.setLastLog(lastIndex, term)

	// Notify the replicators of the new log
	for _, f := range r.leaderState.replState {
		asyncNotifyCh(f.triggerCh)
	}
}

// processLogs is used to apply all the committed entries that haven't been
// applied up to the given index limit.
// This can be called from both leaders and followers.
// Followers call this from AppendEntries, for n entries at a time, and always
// pass futures=nil.
// Leaders call this when entries are committed. They pass the futures from any
// inflight logs.
func (r *Raft) processLogs(index uint64, futures map[uint64]*logFuture) {
	// Reject logs we've applied already
	lastApplied := r.getLastApplied()
	if index <= lastApplied {

		return
	}

	applyBatch := func(batch []*commitTuple) {
		select {
		case r.fsmMutateCh <- interface{}(batch): // explicit conversion: goose translates a select send's value without converting it to the channel's element type (Perennial goose/goose.go:2448, `ctx.expr(c.Value)`; notes/dsv-hraft.md)
		case <-r.shutdownCh:
			for _, cl := range batch {
				if cl.future != nil {
					cl.future.respond(ErrRaftShutdown)
				}
			}
		}
	}

	// Store maxAppendEntries for this call in case it ever becomes reloadable. We
	// need to use the same value for all lines here to get the expected result.
	maxAppendEntries := r.config().MaxAppendEntries

	batch := make([]*commitTuple, 0, maxAppendEntries)

	// Apply all the preceding logs
	for idx := lastApplied + 1; idx <= index; idx++ {
		var preparedLog *commitTuple
		// Get the log, either from the future or from our log store
		future, futureOk := futures[idx]
		if futureOk {
			preparedLog = r.prepareLog(&future.log, future)
		} else {
			l := new(Log)
			if err := r.logs.GetLog(idx, l); err != nil {

				panic(err)
			}
			preparedLog = r.prepareLog(l, nil)
		}

		switch {
		case preparedLog != nil:
			// If we have a log ready to send to the FSM add it to the batch.
			// The FSM thread will respond to the future.
			batch = append(batch, preparedLog)

			// If we have filled up a batch, send it to the FSM
			if len(batch) >= maxAppendEntries {
				applyBatch(batch)
				batch = make([]*commitTuple, 0, maxAppendEntries)
			}

		case futureOk:
			// Invoke the future if given.
			future.respond(nil)
		}
	}

	// If there are any remaining logs in the batch apply them
	if len(batch) != 0 {
		applyBatch(batch)
	}

	// Update the lastApplied index and term
	r.setLastApplied(index)
}

// processLog is invoked to process the application of a single committed log entry.
func (r *Raft) prepareLog(l *Log, future *logFuture) *commitTuple {
	switch l.Type {
	case LogBarrier:
		// Barrier is handled by the FSM
		fallthrough

	case LogCommand:
		return &commitTuple{l, future}

	case LogConfiguration:
		// Only support this with the v2 configuration format
		if r.protocolVersion > 2 {
			return &commitTuple{l, future}
		}
	case LogAddPeerDeprecated:
	case LogRemovePeerDeprecated:
	case LogNoop:
		// Ignore the no-op

	default:
		panic(fmt.Errorf("unrecognized log type: %#v", l))
	}

	return nil
}

// tryStageCommitIndex updates the commit index in persist store if restore committed logs is enabled and log store implements CommitTrackingLogStore.
func (r *Raft) tryStageCommitIndex(commitIndex uint64) {
	if !r.RestoreCommittedLogs {
		return
	}
	store, ok := r.logs.(CommitTrackingLogStore)
	if !ok {
		return
	}
	if err := store.StageCommitIndex(commitIndex); err != nil {

	}
}

// processRPC is called to handle an incoming RPC request. This must only be
// called from the main thread.
func (r *Raft) processRPC(rpc RPC) {
	if err := r.checkRPCHeader(rpc); err != nil {
		rpc.Respond(nil, err)
		return
	}

	switch cmd := rpc.Command.(type) {
	case *AppendEntriesRequest:
		r.appendEntries(rpc, cmd)
	case *RequestVoteRequest:
		r.requestVote(rpc, cmd)
	case *RequestPreVoteRequest:
		r.requestPreVote(rpc, cmd)
	case *InstallSnapshotRequest:
		r.installSnapshot(rpc, cmd)
	case *TimeoutNowRequest:
		r.timeoutNow(rpc, cmd)
	default:

		rpc.Respond(nil, errors.New(rpcUnexpectedCommandError))
	}
}

// processHeartbeat is a special handler used just for heartbeat requests
// so that they can be fast-pathed if a transport supports it. The transport
// calls it on its own goroutine, concurrently with the main thread.
func (r *Raft) processHeartbeat(rpc RPC) {

	// Check if we are shutdown, just ignore the RPC
	select {
	case <-r.shutdownCh:
		return
	default:
	}

	// Ensure we are only handling a heartbeat
	switch cmd := rpc.Command.(type) {
	case *AppendEntriesRequest:
		// This runs on the transport's goroutine, concurrently with the main loop, which reads the term and the state
		// and acts on what it read: so it must not change them (appendEntries would, for a newer term or when this
		// server is not a follower). It answers a heartbeat of the current term to a follower, and a stale one with the
		// current term, as appendEntries does; it refuses any other, which reaches the main loop with the leader's next
		// AppendEntries.
		resp := &AppendEntriesResponse{
			RPCHeader: r.getRPCHeader(),
			Term:      r.getCurrentTerm(),
			LastLog:   r.getLastIndex(),
		}
		if cmd.Term > resp.Term || (cmd.Term == resp.Term && r.getState() != Follower) {
			rpc.Respond(nil, errors.New("heartbeat refused on the fast path: it would change the term or the state"))
			return
		}
		if cmd.Term == resp.Term {
			if len(cmd.Addr) > 0 {
				r.setLeader(r.trans.DecodePeer(cmd.Addr), ServerID(cmd.ID))
			} else {
				r.setLeader(r.trans.DecodePeer(cmd.Leader), ServerID(cmd.ID))
			}
			resp.Success = true
			r.setLastContact()
		}
		rpc.Respond(resp, nil)
	default:

		rpc.Respond(nil, fmt.Errorf("unexpected command"))
	}
}

// appendEntries is invoked when we get an append entries RPC call. This must
// only be called from the main thread.
func (r *Raft) appendEntries(rpc RPC, a *AppendEntriesRequest) {

	// Setup a response
	resp := &AppendEntriesResponse{
		RPCHeader:      r.getRPCHeader(),
		Term:           r.getCurrentTerm(),
		LastLog:        r.getLastIndex(),
		Success:        false,
		NoRetryBackoff: false,
	}
	var rpcErr error
	defer func() {
		rpc.Respond(resp, rpcErr)
	}()

	// Ignore an older term
	if a.Term < r.getCurrentTerm() {
		return
	}

	// Increase the term if we see a newer one, also transition to follower
	// if we ever get an appendEntries call
	if a.Term > r.getCurrentTerm() || (r.getState() != Follower && !r.candidateFromLeadershipTransfer.Load()) {
		// Ensure transition to follower
		r.setState(Follower)
		r.setCurrentTerm(a.Term)
		resp.Term = a.Term
	}

	// Save the current leader
	if len(a.Addr) > 0 {
		r.setLeader(r.trans.DecodePeer(a.Addr), ServerID(a.ID))
	} else {
		r.setLeader(r.trans.DecodePeer(a.Leader), ServerID(a.ID))
	}
	// Verify the last log entry
	if a.PrevLogEntry > 0 {
		lastIdx, lastTerm := r.getLastEntry()

		var prevLogTerm uint64
		if a.PrevLogEntry == lastIdx {
			prevLogTerm = lastTerm
		} else {
			var prevLog Log
			if err := r.logs.GetLog(a.PrevLogEntry, &prevLog); err != nil {

				resp.NoRetryBackoff = true
				return
			}
			prevLogTerm = prevLog.Term
		}

		if a.PrevLogTerm != prevLogTerm {

			resp.NoRetryBackoff = true
			return
		}
	}

	// Process any new entries
	if len(a.Entries) > 0 {

		// Delete any conflicting entries, skip any duplicates
		lastLogIdx, _ := r.getLastLog()
		var newEntries []*Log
		for i, entry := range a.Entries {
			if entry.Index > lastLogIdx {
				newEntries = a.Entries[i:]
				break
			}
			var storeEntry Log
			if err := r.logs.GetLog(entry.Index, &storeEntry); err != nil {

				return
			}
			if entry.Term != storeEntry.Term {

				if err := r.logs.DeleteRange(entry.Index, lastLogIdx); err != nil {

					return
				}
				if entry.Index <= r.configurations.latestIndex {
					r.setLatestConfiguration(r.configurations.committed, r.configurations.committedIndex)
				}
				newEntries = a.Entries[i:]
				break
			}
		}

		if n := len(newEntries); n > 0 {
			// Stage the future commit index if possible
			lastNewIndex := newEntries[len(newEntries)-1].Index
			commitIndex := min(a.LeaderCommitIndex, lastNewIndex)
			r.tryStageCommitIndex(commitIndex)

			// Append the new entries
			if err := r.logs.StoreLogs(newEntries); err != nil {

				// TODO: leaving r.getLastLog() in the wrong
				// state if there was a truncation above
				return
			}

			// Handle any new configuration changes
			for _, newEntry := range newEntries {
				if err := r.processConfigurationLogEntry(newEntry); err != nil {

					rpcErr = err
					return
				}
			}

			// Update the lastLog
			last := newEntries[n-1]
			r.setLastLog(last.Index, last.Term)
		}

	}

	// Update the commit index
	if a.LeaderCommitIndex > 0 && a.LeaderCommitIndex > r.getCommitIndex() {
		// Only commit up to the last index this request vouches is present in
		// the leader's log: the last entry it sent, or the matched previous
		// entry when it sent none (canonical Raft's "index of last new entry",
		// Ongaro-Ousterhout Figure 2). Using r.getLastIndex() here would let a
		// follower commit an uncommitted suffix of an older term that the leader
		// never vouched for. See issues/follower-overcommit.md.
		lastVouched := a.PrevLogEntry
		if len(a.Entries) > 0 {
			lastVouched = a.Entries[len(a.Entries)-1].Index
		}
		idx := min(a.LeaderCommitIndex, lastVouched)
		r.setCommitIndex(idx)
		if r.configurations.latestIndex <= idx {
			r.setCommittedConfiguration(r.configurations.latest, r.configurations.latestIndex)
		}
		r.processLogs(idx, nil)

	}

	// Everything went well, set success
	resp.Success = true
	r.setLastContact()
}

// processConfigurationLogEntry takes a log entry and updates the latest
// configuration if the entry results in a new configuration. This must only be
// called from the main thread, or from NewRaft() before any threads have begun.
func (r *Raft) processConfigurationLogEntry(entry *Log) error {
	switch entry.Type {
	case LogConfiguration:
		r.setCommittedConfiguration(r.configurations.latest, r.configurations.latestIndex)
		r.setLatestConfiguration(DecodeConfiguration(entry.Data), entry.Index)

	case LogAddPeerDeprecated, LogRemovePeerDeprecated:
		r.setCommittedConfiguration(r.configurations.latest, r.configurations.latestIndex)
		conf, err := decodePeers(entry.Data, r.trans)
		if err != nil {
			return err
		}
		r.setLatestConfiguration(conf, entry.Index)
	}
	return nil
}

// requestVote is invoked when we get a request vote RPC call.
func (r *Raft) requestVote(rpc RPC, req *RequestVoteRequest) {

	r.observe(*req)

	// Setup a response
	resp := &RequestVoteResponse{
		RPCHeader: r.getRPCHeader(),
		Term:      r.getCurrentTerm(),
		Granted:   false,
	}
	var rpcErr error
	defer func() {
		rpc.Respond(resp, rpcErr)
	}()

	// Version 0 servers will panic unless the peers is present. It's only
	// used on them to produce a warning message.
	if r.protocolVersion < 2 {
		resp.Peers = encodePeers(r.configurations.latest, r.trans)
	}

	// Check if we have an existing leader [who's not the candidate] and also
	// check the LeadershipTransfer flag is set. Usually votes are rejected if
	// there is a known leader. But if the leader initiated a leadership transfer,
	// vote!
	var candidate ServerAddress
	var candidateBytes []byte
	if len(req.Addr) > 0 {
		candidate = r.trans.DecodePeer(req.Addr)
		candidateBytes = req.Addr
	} else {
		candidate = r.trans.DecodePeer(req.Candidate)
		candidateBytes = req.Candidate
	}

	// For older raft version ID is not part of the packed message
	// We assume that the peer is part of the configuration and skip this check
	if len(req.ID) > 0 {
		candidateID := ServerID(req.ID)
		// if the Servers list is empty that mean the cluster is very likely trying to bootstrap,
		// Grant the vote
		if len(r.configurations.latest.Servers) > 0 && !inConfiguration(r.configurations.latest, candidateID) {

			return
		}
	}
	if leaderAddr, _ := r.LeaderWithID(); leaderAddr != "" && leaderAddr != candidate && !req.LeadershipTransfer {

		return
	}

	// Ignore an older term
	if req.Term < r.getCurrentTerm() {
		return
	}

	// Increase the term if we see a newer one
	if req.Term > r.getCurrentTerm() {
		// Ensure transition to follower

		r.setState(Follower)
		r.setCurrentTerm(req.Term)

		resp.Term = req.Term
	}

	// if we get a request for vote from a nonVoter  and the request term is higher,
	// step down and update term, but reject the vote request
	// This could happen when a node, previously voter, is converted to non-voter
	// The reason we need to step in is to permit to the cluster to make progress in such a scenario
	// More details about that in https://github.com/hashicorp/raft/pull/526
	if len(req.ID) > 0 {
		candidateID := ServerID(req.ID)
		if len(r.configurations.latest.Servers) > 0 && !hasVote(r.configurations.latest, candidateID) {

			return
		}
	}
	// Check if we have voted yet
	lastVoteTerm, err := r.stable.GetUint64(keyLastVoteTerm)
	if err != nil && err.Error() != "not found" {

		return
	}
	lastVoteCandBytes, err := r.stable.Get(keyLastVoteCand)
	if err != nil && err.Error() != "not found" {

		return
	}

	// Check if we've voted in this election before
	if lastVoteTerm == req.Term && lastVoteCandBytes != nil {

		if bytes.Equal(lastVoteCandBytes, candidateBytes) {

			resp.Granted = true
		}
		return
	}

	// Reject if their term is older
	lastIdx, lastTerm := r.getLastEntry()
	if lastTerm > req.LastLogTerm {

		return
	}

	if lastTerm == req.LastLogTerm && lastIdx > req.LastLogIndex {

		return
	}

	// Persist a vote for safety
	if err := r.persistVote(req.Term, candidateBytes); err != nil {

		return
	}

	resp.Granted = true
	r.setLastContact()
}

// requestPreVote is invoked when we get a request Pre-Vote RPC call.
func (r *Raft) requestPreVote(rpc RPC, req *RequestPreVoteRequest) {

	r.observe(*req)

	// Setup a response
	resp := &RequestPreVoteResponse{
		RPCHeader: r.getRPCHeader(),
		Term:      r.getCurrentTerm(),
		Granted:   false,
	}
	var rpcErr error
	defer func() {
		rpc.Respond(resp, rpcErr)
	}()

	// Check if we have an existing leader [who's not the candidate] and also
	candidate := r.trans.DecodePeer(req.GetRPCHeader().Addr)
	candidateID := ServerID(req.ID)

	// if the Servers list is empty that mean the cluster is very likely trying to bootstrap,
	// Grant the vote
	if len(r.configurations.latest.Servers) > 0 && !inConfiguration(r.configurations.latest, candidateID) {

		return
	}

	if leaderAddr, _ := r.LeaderWithID(); leaderAddr != "" && leaderAddr != candidate {

		return
	}

	// Ignore an older term
	if req.Term < r.getCurrentTerm() {
		return
	}

	if req.Term > r.getCurrentTerm() {
		// continue processing here to possibly grant the pre-vote as in a "real" vote this will transition us to follower

		resp.Term = req.Term
	}

	// if we get a request for a pre-vote from a nonVoter  and the request term is higher, do not grant the Pre-Vote
	// This could happen when a node, previously voter, is converted to non-voter
	if len(r.configurations.latest.Servers) > 0 && !hasVote(r.configurations.latest, candidateID) {

		return
	}

	// Reject if their term is older
	lastIdx, lastTerm := r.getLastEntry()
	if lastTerm > req.LastLogTerm {

		return
	}

	if lastTerm == req.LastLogTerm && lastIdx > req.LastLogIndex {

		return
	}

	resp.Granted = true
}

// installSnapshot is invoked when we get a InstallSnapshot RPC call.
// We must be in the follower state for this, since it means we are
// too far behind a leader for log replay. This must only be called
// from the main thread.
func (r *Raft) installSnapshot(rpc RPC, req *InstallSnapshotRequest) {

	// Setup a response
	resp := &InstallSnapshotResponse{
		Term:    r.getCurrentTerm(),
		Success: false,
	}
	var rpcErr error
	defer func() {
		_, _ = io.Copy(io.Discard, rpc.Reader) // ensure we always consume all the snapshot data from the stream [see issue #212]
		rpc.Respond(resp, rpcErr)
	}()

	// Sanity check the version
	if req.SnapshotVersion < SnapshotVersionMin ||
		req.SnapshotVersion > SnapshotVersionMax {
		rpcErr = fmt.Errorf("unsupported snapshot version %d", req.SnapshotVersion)
		return
	}

	// Ignore an older term
	if req.Term < r.getCurrentTerm() {

		return
	}

	// Increase the term if we see a newer one
	if req.Term > r.getCurrentTerm() {
		// Ensure transition to follower
		r.setState(Follower)
		r.setCurrentTerm(req.Term)
		resp.Term = req.Term
	}

	// Save the current leader
	if len(req.ID) > 0 {
		r.setLeader(r.trans.DecodePeer(req.Addr), ServerID(req.ID))
	} else {
		r.setLeader(r.trans.DecodePeer(req.Leader), ServerID(req.ID))
	}

	// The FSM has already applied this snapshot's last entry: restoring it would move the FSM back to an older
	// state (a read served after VerifyLeader or a Barrier could then miss a write it must see), and the log
	// already holds what the snapshot stands for (Raft, Fig. 13 step 6: retain the log and reply). Nothing to
	// install. See verify/issues/snapshot-rollback.md.
	if req.LastLogIndex <= r.getLastApplied() {
		resp.Success = true
		r.setLastContact()
		return
	}

	// Create a new snapshot
	var reqConfiguration Configuration
	var reqConfigurationIndex uint64
	if req.SnapshotVersion > 0 {
		reqConfiguration = DecodeConfiguration(req.Configuration)
		reqConfigurationIndex = req.ConfigurationIndex
	} else {
		reqConfiguration, rpcErr = decodePeers(req.Peers, r.trans)
		if rpcErr != nil {

			return
		}
		reqConfigurationIndex = req.LastLogIndex
	}
	version := getSnapshotVersion(r.protocolVersion)
	sink, err := r.snapshots.Create(version, req.LastLogIndex, req.LastLogTerm,
		reqConfiguration, reqConfigurationIndex, r.trans)
	if err != nil {

		rpcErr = fmt.Errorf("failed to create snapshot: %v", err)
		return
	}

	// Separately track the progress of streaming a snapshot over the network
	// because this too can take a long time.
	countingRPCReader := newCountingReader(rpc.Reader)

	// Spill the remote snapshot to disk
	transferMonitor := startSnapshotRestoreMonitor(countingRPCReader, req.Size, true)
	n, err := io.Copy(sink, countingRPCReader)
	transferMonitor.StopAndWait()
	if err != nil {
		_ = sink.Cancel()

		rpcErr = err
		return
	}

	// Check that we received it all
	if n != req.Size {
		_ = sink.Cancel()

		rpcErr = fmt.Errorf("short read")
		return
	}

	// Finalize the snapshot
	if err := sink.Close(); err != nil {

		rpcErr = err
		return
	}

	// Restore snapshot
	future := &restoreFuture{ID: sink.ID()}
	future.ShutdownCh = r.shutdownCh
	future.init()
	select {
	case r.fsmMutateCh <- interface{}(future): // explicit conversion: goose translates a select send's value without converting it to the channel's element type (Perennial goose/goose.go:2448, `ctx.expr(c.Value)`; notes/dsv-hraft.md)
	case <-r.shutdownCh:
		future.respond(ErrRaftShutdown)
		return
	}

	// Wait for the restore to happen
	if err := future.Error(); err != nil {

		rpcErr = err
		return
	}

	// Update the lastApplied so we don't replay old logs
	r.setLastApplied(req.LastLogIndex)

	// Update the last stable snapshot info
	r.setLastSnapshot(req.LastLogIndex, req.LastLogTerm)

	// Restore the peer set
	r.setLatestConfiguration(reqConfiguration, reqConfigurationIndex)
	r.setCommittedConfiguration(reqConfiguration, reqConfigurationIndex)

	// Clear old logs if r.logs is a MonotonicLogStore. Otherwise compact the
	// logs. In both cases, log any errors and continue.
	if mlogs, ok := r.logs.(MonotonicLogStore); ok && mlogs.IsMonotonic() {
		if err := r.removeOldLogs(); err != nil {

		}
	} else {
		// Raft (Fig. 13, steps 6-7): keep the log only if it holds the snapshot's last entry (same index and
		// term), compacting it as after a snapshot of our own; otherwise discard the whole log, whose entries may
		// conflict with the snapshot (an uncommitted suffix of an older term), and continue from the snapshot.
		// See verify/issues/snapshot-install-conflict.md.
		var last Log
		if err := r.logs.GetLog(req.LastLogIndex, &last); err == nil && last.Term == req.LastLogTerm {
			// The kept entries after the snapshot may hold a newer configuration than the snapshot's: the latest
			// configuration is the latest in the log (as NewRaft's scan after the snapshot). See
			// verify/issues/snapshot-install-config.md.
			lastLogIdx, _ := r.getLastLog()
			for index := req.LastLogIndex + 1; index <= lastLogIdx; index++ {
				var entry Log
				if err := r.logs.GetLog(index, &entry); err != nil {
					panic(err)
				}
				if err := r.processConfigurationLogEntry(&entry); err != nil {
					rpcErr = err
					return
				}
			}
			if err := r.compactLogs(req.LastLogIndex); err != nil {

			}
		} else {
			lastLogIdx, _ := r.getLastLog()
			if err := r.logs.DeleteRange(1, lastLogIdx); err != nil {

			}
			r.setLastLog(req.LastLogIndex, req.LastLogTerm)
		}
	}

	resp.Success = true
	r.setLastContact()
}

// setLastContact is used to set the last contact time to now
func (r *Raft) setLastContact() {
	r.lastContactLock.Lock()
	r.lastContact = time.Now()
	r.lastContactLock.Unlock()
}

type voteResult struct {
	RequestVoteResponse
	voterID ServerID
}

type preVoteResult struct {
	RequestPreVoteResponse
	voterID ServerID
}

// electSelf is used to send a RequestVote RPC to all peers, and vote for
// ourself. This has the side affecting of incrementing the current term. The
// response channel returned is used to wait for all the responses (including a
// vote for ourself). This must only be called from the main thread.
func (r *Raft) electSelf() <-chan *voteResult {
	// Create a response channel
	respCh := make(chan *voteResult, len(r.configurations.latest.Servers))

	// Increment the term
	newTerm := r.getCurrentTerm() + 1

	r.setCurrentTerm(newTerm)
	// Construct the request
	lastIdx, lastTerm := r.getLastEntry()
	req := &RequestVoteRequest{
		RPCHeader: r.getRPCHeader(),
		Term:      newTerm,
		// this is needed for retro compatibility, before RPCHeader.Addr was added
		Candidate:          r.trans.EncodePeer(r.localID, r.localAddr),
		LastLogIndex:       lastIdx,
		LastLogTerm:        lastTerm,
		LeadershipTransfer: r.candidateFromLeadershipTransfer.Load(),
	}

	// Construct a function to ask for a vote
	askPeer := func(peer Server) {
		r.goFunc(func() {

			resp := &voteResult{voterID: peer.ID}
			err := r.trans.RequestVote(peer.ID, peer.Address, req, &resp.RequestVoteResponse)
			if err != nil {

				resp.Term = req.Term
				resp.Granted = false
			}
			respCh <- resp
		})
	}

	// For each peer, request a vote
	for _, server := range r.configurations.latest.Servers {
		if server.Suffrage == Voter {
			if server.ID == r.localID {

				// Persist a vote for ourselves
				if err := r.persistVote(req.Term, req.Addr); err != nil {

					return nil

				}
				// Include our own vote
				respCh <- &voteResult{
					RequestVoteResponse: RequestVoteResponse{
						RPCHeader: r.getRPCHeader(),
						Term:      req.Term,
						Granted:   true,
					},
					voterID: r.localID,
				}
			} else {

				askPeer(server)
			}
		}
	}

	return respCh
}

// preElectSelf is used to send a RequestPreVote RPC to all peers, and vote for
// ourself. This will not increment the current term. The
// response channel returned is used to wait for all the responses (including a
// vote for ourself).
// This must only be called from the main thread.
func (r *Raft) preElectSelf() <-chan *preVoteResult {

	// At this point transport should support pre-vote
	// but check just in case
	prevoteTrans, prevoteTransSupported := r.trans.(WithPreVote)
	if !prevoteTransSupported {
		panic("preElection is not possible if the transport don't support pre-vote")
	}

	// Create a response channel
	respCh := make(chan *preVoteResult, len(r.configurations.latest.Servers))

	// Propose the next term without actually changing our state
	newTerm := r.getCurrentTerm() + 1

	// Construct the request
	lastIdx, lastTerm := r.getLastEntry()
	req := &RequestPreVoteRequest{
		RPCHeader:    r.getRPCHeader(),
		Term:         newTerm,
		LastLogIndex: lastIdx,
		LastLogTerm:  lastTerm,
	}

	// Construct a function to ask for a vote
	askPeer := func(peer Server) {
		r.goFunc(func() {

			resp := &preVoteResult{voterID: peer.ID}

			err := prevoteTrans.RequestPreVote(peer.ID, peer.Address, req, &resp.RequestPreVoteResponse)

			// If the target server do not support Pre-vote RPC we count this as a granted vote to allow
			// the cluster to progress.
			if err != nil && strings.Contains(err.Error(), rpcUnexpectedCommandError) {

				resp.Term = req.Term
				resp.Granted = true
			} else if err != nil {

				resp.Term = req.Term
				resp.Granted = false
			}
			respCh <- resp

		})
	}

	// For each peer, request a vote
	for _, server := range r.configurations.latest.Servers {
		if server.Suffrage == Voter {
			if server.ID == r.localID {

				// cast a pre-vote for our self
				respCh <- &preVoteResult{
					RequestPreVoteResponse: RequestPreVoteResponse{
						RPCHeader: r.getRPCHeader(),
						Term:      req.Term,
						Granted:   true,
					},
					voterID: r.localID,
				}
			} else {

				askPeer(server)
			}
		}
	}

	return respCh
}

// persistVote is used to persist our vote for safety.
// Verification fork (issues/hraft-persistvote-torn-vote.md; upstream #746, PR #747): the candidate is
// written before the term. A crash between the two writes then leaves the older vote's term with the
// new candidate, below the current term (persisted before), so requestVote never takes it for a vote
// already given in this term; upstream's order left the new term with the older vote's candidate,
// which requestVote granted again without the log check.
func (r *Raft) persistVote(term uint64, candidate []byte) error {
	if err := r.stable.Set(keyLastVoteCand, candidate); err != nil {
		return err
	}
	if err := r.stable.SetUint64(keyLastVoteTerm, term); err != nil {
		return err
	}
	return nil
}

// setCurrentTerm is used to set the current term in a durable manner.
func (r *Raft) setCurrentTerm(t uint64) {
	// Persist to disk first
	if err := r.stable.SetUint64(keyCurrentTerm, t); err != nil {
		panic(fmt.Errorf("failed to save current term: %v", err))
	}
	r.raftState.setCurrentTerm(t)
}

// setState is used to update the current state. Any state
// transition causes the known leader to be cleared. This means
// that leader should be set only after updating the state.
func (r *Raft) setState(state RaftState) {
	r.setLeader("", "")
	oldState := r.getState()
	r.raftState.setState(state)
	if oldState != state {
		r.observe(state)
	}
}

// pickServer returns the follower that is most up to date and participating in quorum.
// Because it accesses leaderstate, it should only be called from the leaderloop.
func (r *Raft) pickServer() *Server {
	var pick *Server
	var current uint64
	for _, server := range r.configurations.latest.Servers {
		if server.ID == r.localID || server.Suffrage != Voter {
			continue
		}
		state, ok := r.leaderState.replState[server.ID]
		if !ok {
			continue
		}
		nextIdx := atomic.LoadUint64(&state.nextIndex)
		if nextIdx > current {
			current = nextIdx
			tmp := server
			pick = &tmp
		}
	}
	return pick
}

// initiateLeadershipTransfer starts the leadership on the leader side, by
// sending a message to the leadershipTransferCh, to make sure it runs in the
// mainloop.
func (r *Raft) initiateLeadershipTransfer(id *ServerID, address *ServerAddress) LeadershipTransferFuture {
	future := &leadershipTransferFuture{ID: id, Address: address}
	future.init()

	if id != nil && *id == r.localID {
		err := fmt.Errorf("cannot transfer leadership to itself")

		future.respond(err)
		return future
	}

	select {
	case r.leadershipTransferCh <- future:
		return future
	case <-r.shutdownCh:
		return errorFuture{ErrRaftShutdown}
	default:
		return errorFuture{ErrEnqueueTimeout}
	}
}

// timeoutNow is what happens when a server receives a TimeoutNowRequest.
func (r *Raft) timeoutNow(rpc RPC, req *TimeoutNowRequest) {
	r.setLeader("", "")
	r.setState(Candidate)
	r.candidateFromLeadershipTransfer.Store(true)
	rpc.Respond(&TimeoutNowResponse{}, nil)
}

// setLatestConfiguration stores the latest configuration and updates a copy of it.
func (r *Raft) setLatestConfiguration(c Configuration, i uint64) {
	r.configurations.latest = c
	r.configurations.latestIndex = i
	cc := c.Clone()
	r.latestConfiguration.Store(&cc)
}

// setCommittedConfiguration stores the committed configuration.
func (r *Raft) setCommittedConfiguration(c Configuration, i uint64) {
	r.configurations.committed = c
	r.configurations.committedIndex = i
}

// getLatestConfiguration reads the configuration from a copy of the main
// configuration, which means it can be accessed independently from the main
// loop.
func (r *Raft) getLatestConfiguration() Configuration {
	// this switch catches the case where this is called without having set
	// a configuration previously.
	if c := r.latestConfiguration.Load(); c != nil {
		return *c
	}
	return Configuration{}
}
