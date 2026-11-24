package semantics

import (
	"testing"
	"time"

	"go.etcd.io/etcd/pkg/v3/idutil"
)

// I1. An id has one issuer (assumed).
//
// Decision: "Issue" of (id, g) returns true, recording id ↦ some g, when the
// record has no entry for id or has g's; false (record unchanged) otherwise.
// Next's model assumes it true, so the model excludes every execution in which
// two generators of one machine issue one id.
//
// Lean: idIssueOk, idIssueNext, IdIssueStep (Impl.lean); Next.impl's `assume`
// (TrustedCode/go_etcd_io/etcd/pkg/v3/idutil.lean); wp_IdIssue,
// idIssueFrag_agree (Specs.lean).
//
// Excluded (under the assumption): a second generator of one prefix, started
// before the first's ids reach its start time, issuing one of the first's ids
// (TestOneIssuerFailsWhenClockStepsBack shows Go doing it).
//
// Why: assumed, and true of etcd under two conditions etcd relies on and does
// not check (nonissues/etcd-request-id-restart-reuse.md): the wall clock does
// not step back between two generators' starts, and the earlier generator,
// started at millisecond t0, issues at most 256·(t1 − t0) ids in all, t1 the
// later one's start (Go's comment on Generator: "etcd throughput is << 256
// req/ms"). And the two start less than 2^40 ms (34.8 years) apart: the
// timestamp field is 40 bits (Go's comment: "before 35 years"). A program that
// starts two generators of one prefix itself within those limits (not etcd:
// NewServer starts one) is outside what the model is faithful for.
func TestOneIssuerHoldsWithClockForward(t *testing.T) {
	a := idutil.NewGenerator(7, t0)
	ida := issue(a, 256*5) // 256 ids per ms for 5 ms
	b := idutil.NewGenerator(7, t0.Add(5*time.Millisecond))
	idb := issue(b, 10000)
	if c := common(ida, idb); len(c) != 0 {
		t.Fatalf("clock forward, rate within 256/ms: %d common ids", len(c))
	}
}

func TestOneIssuerFailsWhenClockStepsBack(t *testing.T) {
	a := idutil.NewGenerator(7, t0)
	ida := issue(a, 100)
	b := idutil.NewGenerator(7, t0.Add(-time.Second)) // the clock stepped back
	idb := issue(b, 256*1000+100)
	if c := common(ida, idb); len(c) == 0 {
		t.Fatalf("expected the generators to collide")
	}
}

func TestOneIssuerFailsAboveRate(t *testing.T) {
	a := idutil.NewGenerator(7, t0)
	ida := issue(a, 256*5+1) // one id above 256 per ms
	b := idutil.NewGenerator(7, t0.Add(5*time.Millisecond))
	idb := issue(b, 1)
	if c := common(ida, idb); len(c) != 1 {
		t.Fatalf("expected b's first id among a's, got %d common", len(c))
	}
}
