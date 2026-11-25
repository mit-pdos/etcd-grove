package kvnet

import (
	"fmt"
	"sync"
)

// The counters of Stats, by index.
const (
	StSnapshotsTaken = iota
	StSnapshotsTakenJoint
	StSnapshotsSent
	StSnapshotsInstalled
	StSnapshotsInstalledJoint
	StSnapshotsInstalledLearners
	StCompactions
	StConfChangesProposed
	StConfChangesApplied
	StConfChangesRejected
	StJointEntered
	StRestartsFromSnapshot
	StRestartsAppliedBelow
	StEntriesSkipped
	StFileWrites
	StLeaderSentFirst
	StCommitUnwritten
	StMsgsSent
	StMsgsReceived
	StMsgsDropped
	StDials
	StConnErrors
	StBadFrames
	StRestartsInProcess
	StUDPFragmentsSent       // the UDP transport's (udptransport.go): fragments written
	StUDPFragmentsReceived   // fragments received, well formed and addressed to this replica
	StUDPFragmentsDuplicate  // fragments received again (of a message pending or completed)
	StUDPFragmentsReordered  // fragments received after a later fragment of their message
	StUDPMsgsReordered       // messages completed after a later message of their sender's process
	StUDPMultiFragment       // messages reassembled from more than one fragment
	StUDPReassembliesEvicted // messages evicted incomplete (a fragment lost, or late)
	StUDPBadDatagrams        // datagrams dropped as malformed, misaddressed or inconsistent
	StUDPWriteErrors         // WriteToUDP failures
	StUDPSnapshotsAcked      // snapshots reported finished on their receiver's acknowledgment
	StUDPSnapshotResends     // snapshots sent again, unacknowledged
	StUDPSnapshotsFailed     // snapshots reported failed, unacknowledged after every resend
	StUDPAcksSent            // acknowledgments sent (of snapshots completed, again or not)
	StUDPAcksReceived        // acknowledgments received matching a snapshot waiting for one
	StUDPReceivedDropped     // messages received but dropped, their sender's step queue full
	NumStats
)

// StatNames are the counters' names, by index.
var StatNames = [NumStats]string{
	"snapshots taken", "snapshots taken joint", "snapshots sent", "snapshots installed",
	"snapshots installed joint", "snapshots installed with learners", "compactions",
	"conf changes proposed", "conf changes applied", "conf changes rejected", "joint entered",
	"restarts from a snapshot", "restarts applied below the snapshot", "entries skipped",
	"file writes", "leader sent first", "commit-only unwritten",
	"messages sent", "messages received", "messages dropped",
	"dials", "connection errors", "bad frames", "restarts in process",
	"udp fragments sent", "udp fragments received", "udp fragments duplicate",
	"udp fragments reordered", "udp messages reordered", "udp multi-fragment messages",
	"udp reassemblies evicted", "udp bad datagrams", "udp write errors", "udp snapshots acked",
	"udp snapshot resends", "udp snapshots failed", "udp acks sent", "udp acks received",
	"udp received dropped",
}

// Stats counts what an incarnation exercised, for the tests' coverage report (the driver reads
// them over the client protocol, ReqStatus); the store does not read them.
type Stats struct {
	mu sync.Mutex
	c  [NumStats]uint64
}

func (s *Stats) add(i int) {
	s.mu.Lock()
	s.c[i]++
	s.mu.Unlock()
}

// Snapshot is the counters' values.
func (s *Stats) Snapshot() [NumStats]uint64 {
	s.mu.Lock()
	v := s.c
	s.mu.Unlock()
	return v
}

// FormatStats describes counters' values, by name, leaving out the zero ones.
func FormatStats(v [NumStats]uint64) string {
	s := ""
	for i, n := range v {
		if n == 0 {
			continue
		}
		if s != "" {
			s += ", "
		}
		s += fmt.Sprintf("%s %d", StatNames[i], n)
	}
	return s
}
