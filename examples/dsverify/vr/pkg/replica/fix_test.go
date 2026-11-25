package replica

import (
	"fmt"
	"testing"

	"github.com/tangledbytes/go-vsr/pkg/events"
	"github.com/tangledbytes/go-vsr/pkg/log"
	vsrtime "github.com/tangledbytes/go-vsr/pkg/time"
)

// V2 (primary): VR §4.1 step 3: the primary records the request in its client table when it
// accepts it, so that a resend of a request in progress is dropped. A client that times out and
// resends its request before the reply must not get it executed twice.
func TestFixV2ResendInProgressIsNotExecutedTwice(t *testing.T) {
	c := newCluster(t)
	c.request(0, 1, 1)
	c.request(0, 1, 1) // the client's resend: request 1 is still in progress
	c.deliver(any_)
	if len(c.executed[0]) == 0 {
		t.Fatal("request 1 was not executed")
	}
	c.checkAtMostOnce("V2 (VR §4.1 step 3: the client table records the request in progress)")
}

// V2 (backup): VR §4.1 step 4: a backup that prepares an op records its request number (not
// the client's id) in its client table.
func TestFixV2BackupRecordsTheRequestNumber(t *testing.T) {
	c := newCluster(t)
	c.request(0, 9, 1)
	c.deliver(and(typ(events.EventPrepare), to(1)))
	if got := c.reps[1].state.ClientTable[9].RequestNumber; got != 1 {
		t.Fatalf("V2 (VR §4.1 step 4): backup 1 prepared request 1 of client 9 and recorded request number %d", got)
	}
}

// V13: VR §4.1: the client table holds each client's most recent request. A backup that has
// prepared a client's request 2 and then executes its request 1 (the commit of op 1 arrives
// with the PREPARE of op 2) must still record request 2: a lowered entry no longer recognizes a
// resend of request 2 as a duplicate.
func TestFixV13ExecutionDoesNotLowerTheClientTable(t *testing.T) {
	c := newCluster(t)
	c.request(0, 1, 1)
	c.deliver(and(typ(events.EventPrepare), to(1)))
	c.deliver(typ(events.EventPrepareOK)) // the primary executes request 1 and replies
	c.drop(any_)                          // the COMMITs and the PREPARE to replica 2 are lost
	c.request(0, 1, 2)                    // the client's next request
	c.deliver(and(typ(events.EventPrepare), to(1)))
	if len(c.executed[1]) != 1 {
		t.Fatalf("backup 1 executed %q, want op 1", c.executed[1])
	}
	if e := c.reps[1].state.ClientTable[1]; e.RequestNumber != 2 {
		t.Fatalf("V13 (VR §4.1: the client table holds the most recent request): backup 1 prepared request 2 of client 1, then executed request 1, and its table now records %+v", e)
	}
}

// V13: a write that executes nothing (the table seeded from a STARTVIEW's uncommitted ops)
// must not replace the entry of the same request, which holds its result.
func TestFixV13SeedingKeepsTheResult(t *testing.T) {
	c := newCluster(t)
	c.request(0, 1, 1)
	c.deliver(and(typ(events.EventPrepare), to(1)))
	c.deliver(typ(events.EventPrepareOK)) // replica 0 executes request 1
	c.drop(any_)                          // replica 1 does not learn the commit
	c.viewChange(1, 1, 2)                 // view 1 (primary 1) from {1, 2}: commit number 0
	if c.reps[1].state.Status != ReplicaStatusNormal || c.reps[1].state.ViewNumber != 1 {
		t.Fatalf("view 1 did not start: %+v", c.reps[1].state)
	}
	c.deliver(and(typ(events.EventStartView), to(0)))
	if e := c.reps[0].state.ClientTable[1]; !e.Finished || e.RequestNumber != 1 || e.Result != "res "+op(1, 1) {
		t.Fatalf("V13 (VR §4.1: the client table holds the result of the request executed): replica 0 executed request 1 of client 1, and after the STARTVIEW of view 1 its table records %+v", e)
	}
}

// V9: VR §4.1 step 5: after f PREPAREOKs for op n, the primary executes it and sends the reply
// for op n's request to op n's client. Two clients' first requests (both request number 1) are
// in progress: each reply must go to its own client.
func TestFixV9ReplyGoesToTheOpsClient(t *testing.T) {
	c := newCluster(t)
	c.request(0, 1, 1) // op 1
	c.request(0, 2, 1) // op 2
	c.deliver(any_)
	if len(c.executed[0]) != 2 {
		t.Fatalf("executed %q, want both requests", c.executed[0])
	}
	c.checkReplies("V9 (VR §4.1 step 5: the reply to op n goes to op n's client)")
	got := map[uint64]bool{}
	for _, m := range c.replies {
		got[m.ev.Data.(events.Reply).ClientID] = true
	}
	if !got[1] || !got[2] {
		t.Fatalf("V9: replies sent %v, want one to each client", c.replies)
	}
}

// V3: VR §4.1 step 5: the primary executes op n only after f PREPAREOKs for op n from its
// current view. PREPAREOKs for an op number the primary does not have (f + 1 of them here) must
// not make it execute anything (op n is not in its log).
func TestFixV3PrepareOKForAnOpNotInTheLog(t *testing.T) {
	c := newCluster(t)
	mustNotPanic(t, "V3 (VR §4.1 step 5: PREPAREOKs count for an op of the primary's log)", func() {
		c.submit(0, c.addrs[1], events.EventPrepareOK, events.PrepareOK{ViewNum: 0, OpNum: 1, ReplicaID: 1})
		c.submit(0, c.addrs[2], events.EventPrepareOK, events.PrepareOK{ViewNum: 0, OpNum: 1, ReplicaID: 2})
	})
	if len(c.executed[0]) != 0 || c.reps[0].state.CommitNumber != 0 {
		t.Fatalf("V3: primary 0 has no op, yet executed %q (commit number %d)", c.executed[0], c.reps[0].state.CommitNumber)
	}
}

// V3: a PREPAREOK of an earlier view does not count: replica 1 accepted op 1 of view 0, not op 1
// of view 3. Counting it, the primary of view 3 executes (and answers) an op only it holds,
// which a view change among the other two replicas then loses.
func TestFixV3PrepareOKOfAnotherViewDoesNotCount(t *testing.T) {
	c := newCluster(t)
	c.viewChange(3, 0, 2) // view 3, primary 0, from {0, 2}
	if c.reps[0].state.Status != ReplicaStatusNormal || c.reps[0].state.ViewNumber != 3 {
		t.Fatalf("view 3 did not start at replica 0: %+v", c.reps[0].state)
	}
	c.drop(any_)
	c.request(0, 5, 1) // op 1 of view 3
	c.drop(any_)       // its PREPAREs are lost: no backup holds it
	c.submit(0, c.addrs[1], events.EventPrepareOK, events.PrepareOK{ViewNum: 0, OpNum: 1, ReplicaID: 1})
	if len(c.executed[0]) != 0 {
		t.Fatalf("V3 (VR §4.1 step 5: f PREPAREOKs of the current view): primary 0 of view 3 executed %q on a PREPAREOK of view 0; no backup holds op 1 of view 3", c.executed[0])
	}
}

// V6a: VR §4.2 step 2: a replica's DOVIEWCHANGE names v', the latest view in which its status
// was normal. Replica 2, normal in view 0, times out twice (view change to view 1, then to view
// 2, before view 1 started): its DOVIEWCHANGE for view 2 must name view 0, not view 1, in which
// it never was normal (a log naming a later view wins the new primary's log selection).
func TestFixV6aLastNormalViewIsAViewThatStarted(t *testing.T) {
	c := newCluster(t)
	c.timeout(2) // view change to view 1
	c.timeout(2) // view 1 does not start; view change to view 2
	if c.reps[2].state.ViewNumber != 2 || c.reps[2].state.Status != ReplicaStatusViewChange {
		t.Fatalf("replica 2: %+v", c.reps[2].state)
	}
	c.drop(not(to(2)))
	// replica 0 joins the view change to view 2 (its STARTVIEWCHANGE reaches replica 2)
	c.submit(2, c.addrs[0], events.EventStartViewChange, events.StartViewChange{ViewNum: 2, ReplicaID: 0})
	c.deliver(and(typ(events.EventStartViewChange), to(2)))
	found := false
	for _, m := range c.pending {
		if m.ev.Type == events.EventDoViewChange && m.from == 2 {
			found = true
			if dvc := m.ev.Data.(events.DoViewChange); dvc.ViewNum == 2 && dvc.LastStableViewNum != 0 {
				t.Fatalf("V6a (VR §4.2 step 2: v' is the latest view in which the replica was normal): replica 2 was normal only in view 0, and its DOVIEWCHANGE for view 2 names view %d", dvc.LastStableViewNum)
			}
		}
	}
	if !found {
		t.Fatal("replica 2 sent no DOVIEWCHANGE")
	}
}

// V6b: VR §4.2 step 3: the new primary selects as the new log the one in the DOVIEWCHANGEs with
// the largest v' (last normal view); among those, the largest op number. History: view 1
// (primary 1) prepared a2..a5 that nobody else accepted; view 2 (primary 2, from {0, 2}) did
// not have them and committed b2 at op 2, which replica 0 executed. The new primary 0 of view 3
// gets DOVIEWCHANGEs from itself (v' = 2, ops a1 b2) and replica 1 (v' = 1, ops a1 a2..a5): the
// new log must be replica 0's, whatever order the responses are scanned in.
func TestFixV6bLogOfTheLatestNormalViewIsSelected(t *testing.T) {
	for trial := 0; trial < 64; trial++ {
		c := newCluster(t)
		c.submit(0, c.addrs[2], events.EventStartView, events.StartView{ViewNum: 2, OpNum: 2, CommitNum: 0,
			Logs: []log.Log{entry(1, 1), entry(2, 1)}, ReplicaID: 2})
		c.submit(0, c.addrs[2], events.EventCommit, events.Commit{ViewNum: 2, CommitNum: 2, ReplicaID: 2})
		if len(c.executed[0]) != 2 {
			t.Fatalf("replica 0 executed %q in view 2", c.executed[0])
		}
		c.drop(any_)
		c.submit(0, c.addrs[2], events.EventStartViewChange, events.StartViewChange{ViewNum: 3, ReplicaID: 2})
		c.deliver(and(typ(events.EventStartViewChange, events.EventDoViewChange), among(0)))
		c.submit(0, c.addrs[1], events.EventDoViewChange, events.DoViewChange{ViewNum: 3, LastStableViewNum: 1,
			Logs: []log.Log{entry(1, 1), entry(3, 1), entry(4, 1), entry(5, 1), entry(6, 1)}, OpNum: 5, CommitNum: 1, ReplicaID: 1})
		if c.reps[0].state.Status != ReplicaStatusNormal || c.reps[0].state.ViewNumber != 3 {
			t.Fatalf("view 3 did not start at replica 0: %+v", c.reps[0].state)
		}
		c.checkLogHasExecuted(fmt.Sprintf("V6b (VR §4.2 step 3: the log of the largest last normal view; trial %d)", trial), 0)
	}
}

// V10: VR §4.2 step 3: the new primary of view v installs view v once it has f + 1
// DOVIEWCHANGEs for v, and selects the log among those. Replica 0 (executed x at op 1 in view
// 0, accepted by replica 2) is changing to view 3; a DOVIEWCHANGE for view 6 from replica 1
// (which missed x) arrives first, alone; then the DOVIEWCHANGEs for view 3 from 0 and 2. The
// view installed must be 3, with a log selected from {0, 2}, not view 6 from replica 1's alone.
func TestFixV10TheViewOfTheQuorumIsInstalled(t *testing.T) {
	c := newCluster(t)
	c.request(0, 1, 1)
	c.deliver(and(typ(events.EventPrepare), to(2)))
	c.deliver(and(typ(events.EventPrepareOK), from(2)))
	if len(c.executed[0]) != 1 {
		t.Fatalf("x not executed: %q", c.executed[0])
	}
	c.drop(any_)
	c.submit(0, c.addrs[2], events.EventStartViewChange, events.StartViewChange{ViewNum: 3, ReplicaID: 2})
	c.submit(0, c.addrs[1], events.EventDoViewChange, events.DoViewChange{ViewNum: 6, LastStableViewNum: 0,
		Logs: []log.Log{}, OpNum: 0, CommitNum: 0, ReplicaID: 1})
	c.deliver(and(typ(events.EventStartViewChange, events.EventDoViewChange), among(0)))
	c.submit(0, c.addrs[2], events.EventDoViewChange, events.DoViewChange{ViewNum: 3, LastStableViewNum: 0,
		Logs: []log.Log{entry(1, 1)}, OpNum: 1, CommitNum: 0, ReplicaID: 2})
	if c.reps[0].state.Status != ReplicaStatusNormal {
		t.Fatalf("no view started at replica 0: %+v", c.reps[0].state)
	}
	if v := c.reps[0].state.ViewNumber; v != 3 {
		t.Fatalf("V10 (VR §4.2 step 3: the view whose DOVIEWCHANGEs reached f + 1 is installed): replica 0 installed view %d from 1 DOVIEWCHANGE; its log %v", v, c.reps[0].state.Logs)
	}
	c.checkLogHasExecuted("V10", 0)
}

// V5: VR §4.2 step 4: the new primary executes, in order, the committed operations it had not
// executed and updates its client table. Replica 0 committed and executed x (request 1 of
// client 1) in view 0 with replica 1; replica 2 missed it. View 2 (primary 2) starts from
// {0, 2} with x committed. The client, whose reply was lost, resends request 1 to the new
// primary: it must not be executed a second time.
func TestFixV5NewPrimaryExecutesCommittedOps(t *testing.T) {
	c := newCluster(t)
	c.request(0, 1, 1)
	c.deliver(and(typ(events.EventPrepare), to(1)))
	c.deliver(and(typ(events.EventPrepareOK), from(1)))
	if len(c.executed[0]) != 1 {
		t.Fatalf("x not executed: %q", c.executed[0])
	}
	c.drop(any_)
	c.viewChange(2, 0, 2)
	if c.reps[2].state.Status != ReplicaStatusNormal || c.reps[2].state.ViewNumber != 2 {
		t.Fatalf("view 2 did not start at replica 2: %+v", c.reps[2].state)
	}
	c.replies = nil
	c.request(2, 1, 1) // the client's resend reaches the new primary
	c.deliver(among(0, 2))
	c.checkAtMostOnce("V5 (VR §4.2 step 4: the new primary executes the committed ops and updates its client table)")
	c.checkReplies("V5")
	if len(c.replies) == 0 {
		t.Fatal("V5: the resend of an executed request got no reply from the new primary")
	}
}

// V7: VR §4.2 step 1: only a replica changing to view v collects STARTVIEWCHANGEs for v; a
// replica in state transfer is still in the view in which it was normal. Replica 2, normal in
// view 1, falls behind and starts a state transfer; a late STARTVIEWCHANGE for view 1 (sent by
// replica 0 during the view change to view 1) then arrives: it must be ignored.
func TestFixV7StartViewChangeOfTheCurrentViewInStateTransfer(t *testing.T) {
	c := newCluster(t)
	c.submit(2, c.addrs[1], events.EventStartView, events.StartView{ViewNum: 1, OpNum: 1, CommitNum: 0,
		Logs: []log.Log{entry(1, 1)}, ReplicaID: 1})
	c.submit(2, c.addrs[1], events.EventPrepare, events.Prepare{ViewNum: 1, OpNum: 3, CommitNum: 0,
		Request: events.Request{ID: 1, ClientID: 3, Op: op(3, 1)}, ReplicaID: 1})
	if c.reps[2].state.Status != ReplicaStatusStateTransfer {
		t.Fatalf("replica 2 did not start a state transfer: %+v", c.reps[2].state)
	}
	mustNotPanic(t, "V7 (VR §4.2 step 1: a replica in state transfer ignores a STARTVIEWCHANGE of its own view)", func() {
		c.submit(2, c.addrs[0], events.EventStartViewChange, events.StartViewChange{ViewNum: 1, ReplicaID: 0})
	})
	if s := c.reps[2].state; s.Status != ReplicaStatusStateTransfer || s.ViewNumber != 1 {
		t.Fatalf("V7: replica 2 changed state on a STARTVIEWCHANGE of its own view: %+v", s)
	}
}

// V8: VR §4.1 step 6: the primary sends COMMITs in normal operation; a replica that would be
// the primary of the view it is changing to has not started that view and must not announce
// it (a backup that gets a COMMIT of a later view moves toward that view by state transfer).
func TestFixV8NoCommitWhileInViewChange(t *testing.T) {
	c := newCluster(t)
	c.clock.TickBy(2 * hb) // replica 1 hears nothing from primary 0: its timer expires
	c.reps[1].Run()
	c.drain(1)
	if s := c.reps[1].state; s.Status != ReplicaStatusViewChange || s.ViewNumber != 1 {
		t.Fatalf("replica 1 did not start the view change to view 1: %+v", s)
	}
	c.clock.TickBy(hb)
	c.reps[1].Run()
	for _, m := range c.pending {
		if m.ev.Type == events.EventCommit && m.from == 1 {
			t.Fatalf("V8 (VR §4.1 step 6: COMMITs are sent in normal operation): replica 1, in the view change to view 1 (not started), sent %+v to %s", m.ev.Data, m.to)
		}
	}
}

// V11: VR §4.2 step 5: replicas in the view change install the new view from its STARTVIEW. A
// replica already normal in that view has accepted later ops of it (PREPAREOK sent: the primary
// may have committed them); a late copy of the view's STARTVIEW must not roll its log back.
func TestFixV11LateStartViewDoesNotRollBackTheLog(t *testing.T) {
	c := newCluster(t)
	sv := events.StartView{ViewNum: 1, OpNum: 1, CommitNum: 0, Logs: []log.Log{entry(1, 1)}, ReplicaID: 1}
	c.submit(2, c.addrs[1], events.EventStartView, sv)
	c.submit(2, c.addrs[1], events.EventPrepare, events.Prepare{ViewNum: 1, OpNum: 2, CommitNum: 0,
		Request: events.Request{ID: 1, ClientID: 2, Op: op(2, 1)}, ReplicaID: 1})
	if s := c.reps[2].state; s.OpNum != 2 {
		t.Fatalf("replica 2 did not accept op 2: %+v", s)
	}
	c.submit(2, c.addrs[1], events.EventStartView, sv) // the late copy
	if s := c.reps[2].state; s.OpNum != 2 || s.Logs.Len() != 2 || s.Logs.OpAt(2) != op(2, 1) {
		t.Fatalf("V11 (VR §4.2 step 5: only a replica in the view change installs a STARTVIEW of its view): replica 2 acknowledged op 2 (%q) of view 1, and a late STARTVIEW of view 1 set its op number to %d, log %v", op(2, 1), s.OpNum, s.Logs)
	}
}

// V1: VR §4.3: the NEWSTATE answers the replica's GETSTATE <v, n> with the log after op n. A
// NEWSTATE that answers an earlier GETSTATE (the transfer timed out and was retried at another
// replica, which answered first) can arrive after the replica caught up and fell behind again:
// it must not be appended to the longer log (op k of the log would no longer be op k).
func TestFixV1StaleNewStateIsNotAppended(t *testing.T) {
	c := newCluster(t)
	heartbeat := func(i int) { // primary 0's COMMIT reaches replica i (its view-change timer restarts)
		c.submit(i, c.addrs[0], events.EventCommit, events.Commit{ViewNum: 0, CommitNum: c.reps[0].state.CommitNumber, ReplicaID: 0})
	}
	c.request(0, 1, 1)
	c.deliver(any_) // op 1 committed and executed everywhere
	for cl := uint64(2); cl <= 4; cl++ {
		c.request(0, cl, 1)
	}
	c.deliver(and(typ(events.EventPrepare, events.EventPrepareOK), among(0, 1))) // ops 2..4 committed by {0, 1}
	c.drop(and(typ(events.EventPrepare), to(2), func(m msg) bool { return m.ev.Data.(events.Prepare).OpNum < 4 }))
	c.deliver(and(typ(events.EventPrepare), to(2))) // op 4: replica 2 is behind, asks primary 0
	if c.reps[2].state.Status != ReplicaStatusStateTransfer {
		t.Fatalf("replica 2 did not start a state transfer: %+v", c.reps[2].state)
	}
	stale := c.take(and(typ(events.EventGetState), to(0))) // GETSTATE <0, 1>, slow to reach 0
	if len(stale) != 1 {
		t.Fatalf("GETSTATEs to 0: %v", stale)
	}
	c.clock.TickBy(15 * vsrtime.SECOND) // the transfer times out: retried at replica 1
	heartbeat(1)
	heartbeat(2)
	c.deliver(typ(events.EventGetState, events.EventNewState))
	if s := c.reps[2].state; s.Status != ReplicaStatusNormal || s.OpNum != 4 {
		t.Fatalf("replica 2 did not catch up: %+v", s)
	}
	c.drop(to(2))
	c.request(0, 5, 1)
	c.request(0, 6, 1)
	c.deliver(and(typ(events.EventPrepare, events.EventPrepareOK), among(0, 1))) // ops 5, 6 committed
	c.drop(and(typ(events.EventPrepare), to(2), func(m msg) bool { return m.ev.Data.(events.Prepare).OpNum < 6 }))
	c.deliver(and(typ(events.EventPrepare), to(2))) // replica 2 is behind again: GETSTATE <0, 4>
	fresh := c.take(typ(events.EventGetState))
	c.resubmit(stale...) // the GETSTATE <0, 1> reaches 0 at last; its answer comes first
	c.deliver(typ(events.EventGetState, events.EventNewState))
	c.resubmit(fresh...)
	c.deliver(typ(events.EventGetState, events.EventNewState))
	heartbeat(2) // COMMIT 6: replica 2 executes up to op 6
	c.checkAtMostOnce("V1 (VR §4.3: a NEWSTATE extends the log from the op its GETSTATE named)")
	c.checkAgreement("V1 (VR §4.3: a NEWSTATE extends the log from the op its GETSTATE named)")
	if len(c.executed[2]) != 6 {
		t.Fatalf("replica 2 executed %q, want the 6 ops", c.executed[2])
	}
}

// V14: VR §4.2's correctness argument: an op accepted (PREPAREOK) by a replica stays in its log
// while its DOVIEWCHANGE may name the view in which it accepted it; so every committed op is in
// the log of some member of any f + 1 DOVIEWCHANGEs, and is in the new view's log. go-vsr's
// state transfer stays in the replica's view (its GETSTATE names its view), yet truncated the
// log to the commit number, dropping accepted ops.
//
// Schedule: view 0, primary 0: op x prepared by 0 and accepted by 1 (PREPAREOK), committed and
// executed at 0 (reply sent); 2 missed the PREPARE and 1 has not learned the commit. Replica 2
// times out to view 3 (primary 0), which starts with DOVIEWCHANGEs from {0, 2} (x kept: 0 has
// it); 1 hears nothing of it, and 2 misses its STARTVIEW. Replica 1 then gets a COMMIT of view 3
// and starts a state transfer (as released: truncating its log to its commit number 0, dropping
// x). Replica 2 times out again, to view 4 (primary 1), which starts with DOVIEWCHANGEs from
// {1, 2} only: its log must contain x, which replica 0 executed at op 1.
func TestFixV14StateTransferKeepsAcceptedOps(t *testing.T) {
	c := newCluster(t)
	c.request(0, 1, 1) // x
	c.drop(and(typ(events.EventPrepare), to(2)))
	c.deliver(and(typ(events.EventPrepare), to(1)))
	c.deliver(and(typ(events.EventPrepareOK), from(1)))
	if len(c.executed[0]) != 1 {
		t.Fatalf("x not executed at 0: %q", c.executed[0])
	}
	c.drop(any_) // the COMMITs of x are lost

	// view 3 from {0, 2}
	c.timeout(2)
	c.timeout(2)
	c.timeout(2)
	c.drop(func(m msg) bool {
		return m.ev.Type == events.EventStartViewChange && m.ev.Data.(events.StartViewChange).ViewNum < 3
	})
	c.drop(to(1))
	c.submit(0, c.addrs[2], events.EventStartViewChange, events.StartViewChange{ViewNum: 3, ReplicaID: 2})
	c.drop(to(1))
	c.deliver(and(among(0, 2), typ(events.EventStartViewChange, events.EventDoViewChange)))
	if s := c.reps[0].state; s.Status != ReplicaStatusNormal || s.ViewNumber != 3 {
		t.Fatalf("view 3 did not start at 0: %+v", s)
	}
	c.drop(typ(events.EventStartView)) // 2 misses the STARTVIEW of view 3; 1 too
	c.drop(any_)

	// replica 1 gets a COMMIT of view 3 (primary 0's heartbeat) and starts a state transfer
	c.clock.TickBy(hb)
	c.reps[0].Run()
	c.deliver(and(typ(events.EventCommit), to(1)))
	if s := c.reps[1].state; s.Status != ReplicaStatusStateTransfer {
		t.Fatalf("replica 1 did not start a state transfer: %+v", s)
	}
	c.drop(any_) // its GETSTATE names view 0: nobody answers

	// view 4 (primary 1) from {1, 2}
	c.timeout(2)
	c.deliver(and(among(1, 2), typ(events.EventStartViewChange, events.EventDoViewChange)))
	if s := c.reps[1].state; s.Status != ReplicaStatusNormal || s.ViewNumber != 4 {
		t.Fatalf("view 4 did not start at 1: %+v", s)
	}
	rule := "V14 (VR §4.2: a replica keeps the ops it accepted while its DOVIEWCHANGE may name that view; the new view's log has every committed op)"

	// the new view goes on: y is committed in view 4
	c.deliver(among(1, 2))
	c.request(1, 2, 1)
	c.deliver(among(1, 2))
	if len(c.executed[1]) == 0 {
		t.Fatalf("view 4 executed nothing")
	}
	c.checkAgreement(rule)
	c.checkLogHasExecuted(rule, 1)
}

// O2: VR §4: the primary of view v is replica v mod n. A replica that learns of a view number
// >= 2^63 (here a PREPARE of such a view makes a backup start a state transfer to it, asking
// that view's primary) must address replica v mod n.
func TestFixO2ViewNumberHighBit(t *testing.T) {
	c := newCluster(t)
	const v = uint64(1)<<63 + 1
	mustNotPanic(t, "O2 (VR §4: the primary of view v is replica v mod n)", func() {
		c.submit(1, c.addrs[0], events.EventPrepare, events.Prepare{ViewNum: v, OpNum: 1, CommitNum: 0,
			Request: events.Request{ID: 1, ClientID: 1, Op: op(1, 1)}, ReplicaID: v % 3})
	})
	gs := c.take(typ(events.EventGetState))
	if len(gs) != 1 || gs[0].to != memberAddrs[v%3] {
		t.Fatalf("O2: GETSTATEs %v, want one to the primary of view %d, replica %d", gs, v, v%3)
	}
}

// O2: VR §4: view numbers only increase. A backup of view 2^64 - 1 whose primary falls silent
// must not move to view 0 (every old message would be current again).
func TestFixO2ViewNumberDoesNotWrap(t *testing.T) {
	c := newCluster(t)
	const v = ^uint64(0) // its primary: v mod 3 = 0
	mustNotPanic(t, "O2 (VR §4: the primary of view v is replica v mod n)", func() {
		c.submit(1, c.addrs[0], events.EventStartView, events.StartView{ViewNum: v, OpNum: 0, CommitNum: 0,
			Logs: []log.Log{}, ReplicaID: 0})
		c.clock.TickBy(2 * hb)
		c.reps[1].Run()
		c.drain(1)
	})
	if got := c.reps[1].state.ViewNumber; got != v {
		t.Fatalf("O2 (VR §4: view numbers are monotone): replica 1 of view %d timed out and moved to view %d", v, got)
	}
}
