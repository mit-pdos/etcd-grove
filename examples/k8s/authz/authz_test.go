package authz

import (
	"context"
	"fmt"
	"os"
	"strconv"
	"testing"

	"k8s.io/apiserver/pkg/authorization/authorizer"
)

// iterations is the number of requests each test runs ($AUTHZ_ITERATIONS, default 200000).
func iterations() int {
	if n, err := strconv.Atoi(os.Getenv("AUTHZ_ITERATIONS")); err == nil && n > 0 {
		return n
	}
	return 200000
}

// runOnce is Main (MainStrict if strict) with phase 1's decision tree recorded; it returns the
// panic, if any, with the decision tree that caused it.
func runOnce(strict bool) (msg string, tree string) {
	ctx := context.Background()
	a, err := newChain()
	if err != nil {
		return "", ""
	}
	d := a.ConditionsAwareAuthorize(ctx, authorizer.AttributesRecord{})
	defer func() {
		if r := recover(); r != nil {
			msg, tree = fmt.Sprint(r), d.String()
		}
	}()
	twoPhase(ctx, a, d, strict)
	return "", ""
}

// check runs n requests and returns the distinct panics, each with its count and a decision tree.
func check(t *testing.T, strict bool) map[string]int {
	counts := map[string]int{}
	n := iterations()
	for i := 0; i < n; i++ {
		msg, tree := runOnce(strict)
		if msg == "" {
			continue
		}
		if counts[msg] == 0 {
			t.Logf("panic %q, phase-1 decision %s", msg, tree)
		}
		counts[msg]++
	}
	t.Logf("%d requests, panics: %v", n, counts)
	return counts
}

// TestMain checks that Main never panics.
func TestMainNeverPanics(t *testing.T) {
	if counts := check(t, false); len(counts) != 0 {
		t.Errorf("Main panicked: %v", counts)
	}
	// and Main itself, as the theorem states it
	for i := 0; i < 1000; i++ {
		Main()
	}
}

// TestMainStrict shows that C3 fails for an unconditional Allow (FailureDecision is NoOpinion) and
// for nothing else.
func TestMainStrict(t *testing.T) {
	counts := check(t, true)
	for msg := range counts {
		if msg != "C3 (strict): the failure decision of an Allow is not a possible decision" {
			t.Errorf("MainStrict panicked other than on C3 for an Allow: %q", msg)
		}
	}
	if counts["C3 (strict): the failure decision of an Allow is not a possible decision"] == 0 {
		t.Errorf("expected MainStrict's C3 to fail for an Allow")
	}
}

// TestPhaseTwoReached checks that the runs exercise phase 2, and phase 2's three outcomes.
func TestPhaseTwoReached(t *testing.T) {
	ctx := context.Background()
	outcomes := map[authorizer.Decision]int{}
	n := iterations() / 10
	for i := 0; i < n; i++ {
		a, err := newChain()
		if err != nil {
			t.Fatal(err)
		}
		d := a.ConditionsAwareAuthorize(ctx, authorizer.AttributesRecord{})
		if d.IsAllow() || !d.PossibleDecisions().Has(authorizer.DecisionAllow) {
			continue
		}
		dec, _, _ := a.EvaluateConditions(ctx, d, emptyData{})
		outcomes[dec]++
	}
	t.Logf("phase-2 outcomes in %d requests: %v", n, outcomes)
	for _, dec := range []authorizer.Decision{authorizer.DecisionAllow, authorizer.DecisionDeny, authorizer.DecisionNoOpinion} {
		if outcomes[dec] == 0 {
			t.Errorf("phase 2 never returned %s", dec)
		}
	}
}
