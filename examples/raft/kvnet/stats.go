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
