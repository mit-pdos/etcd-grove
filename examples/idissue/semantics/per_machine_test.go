package semantics

import (
	"testing"

	"go.etcd.io/etcd/pkg/v3/idutil"
)

// I3. One record per machine.
//
// Decision: the record is the extension's local state (GlobalState := Unit):
// "Issue" compares an id with the ids issued on the same machine only. Two
// machines' generators are never compared by the model.
//
// Lean: idIssueExt (LocalState := IdIssueState, GlobalState := Unit).
//
// Excluded: nothing across machines. Allowed: two machines issuing one id.
//
// Why: proved, not assumed. Two members' ids differ in the prefix, the member
// id's 16 low bits, which the deployment makes distinct (WellFormed's
// distinct low bits, TestMemberIDs); the cluster's id invariant
// (Proof/go_etcd_io/etcd/pkg/v3/idutil/Defs.lean, idClusterOk) proves it. A
// global record would assume more (it would exclude executions that a
// deployment with equal low bits has), so it would hide that premise.
func TestMachinesDisjointByPrefix(t *testing.T) {
	a := idutil.NewGenerator(1, t0)
	b := idutil.NewGenerator(2, t0) // same clock, another member
	if c := common(issue(a, 10000), issue(b, 10000)); len(c) != 0 {
		t.Fatalf("distinct prefixes: %d common ids", len(c))
	}
}

func TestMachinesCollideWithEqualLowBits(t *testing.T) {
	// member ids 0x10001 and 0x20001 have equal 16 low bits: the prefix is
	// uint16(id), so the two members' generators are one prefix's
	m1, m2 := uint64(0x10001), uint64(0x20001)
	a := idutil.NewGenerator(uint16(m1), t0)
	b := idutil.NewGenerator(uint16(m2), t0)
	if a.Next() != b.Next() {
		t.Fatal("expected equal first ids")
	}
}
