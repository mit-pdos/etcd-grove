package semantics

import (
	"testing"
	"time"

	"go.etcd.io/etcd/pkg/v3/idutil"
)

// I2. A crash keeps the record, every entry as an earlier incarnation's
// (assumed; etcd-dist D4b, 2026-11-24).
//
// Decision: at a crash of the machine (a process's restart is one, the file
// extension's env_restarts.go) the record keeps every entry, each id ↦ some g
// becoming id ↦ none: issued by a generator of an earlier incarnation. "Issue"
// refuses an id with entry none, whatever the issuing generator's address. So
// the model excludes every execution in which a generator started after a
// crash issues an id issued before it, by any earlier incarnation.
//
// Lean: IdIssueState := GMap w64 (Option Loc), idIssueCrash, idIssueOk's
// `some none => false`, idIssue_semantics.crash (Impl.lean); the crash
// interpretation idIssue_crash_interp, its rest idIssueCrashStart, which turns
// every old fact about an id into idIssuePast (Crash.lean), exclusive with the
// new incarnation's idIssueFrag (idIssueFrag_past, Specs.lean).
//
// Excluded (under the assumption): the restarted member's generator issuing a
// request id of the previous run, whose entry may still be in the WAL; when
// that entry is applied, Trigger delivers its result to the new request
// (nonissues/etcd-request-id-restart-reuse.md). TestRestartReissuesIfClockBack
// shows Go reissuing when the assumption fails.
//
// Why: assumed; the same assumption as I1, across the machine's restarts: the
// wall clock after the restart (the RTC, then NTP) is not behind the previous
// run's generator start plus its ids / 256 ms. It cannot be keyed by the
// generator's address alone (until D4b): the heap is new after a crash, so a
// restarted generator may be allocated at a stopped one's address, and the
// record would then take the two for one and admit the reissue (a Go
// address is no identity across a restart).
func TestRestartFreshIfClockForward(t *testing.T) {
	before := idutil.NewGenerator(9, t0)
	old := issue(before, 1000)
	// crash; the machine reboots; the clock moved forward by the reboot's time
	after := idutil.NewGenerator(9, t0.Add(30*time.Second))
	if c := common(issue(after, 100000), old); len(c) != 0 {
		t.Fatalf("restart with the clock forward: %d reissued ids", len(c))
	}
}

func TestRestartReissuesIfClockBack(t *testing.T) {
	before := idutil.NewGenerator(9, t0)
	old := issue(before, 1000)
	// crash; the machine reboots with its RTC 2 s behind (corrected by NTP later)
	after := idutil.NewGenerator(9, t0.Add(-2*time.Second))
	if c := common(issue(after, 256*2000+1000), old); len(c) == 0 {
		t.Fatalf("expected a reissued id")
	}
}
