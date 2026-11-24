// Package authz runs Kubernetes' conditional authorization (KEP-5681; k8s.io/apiserver's
// pkg/authorization/authorizer and pkg/authorization/union at github.com/luxas/kubernetes
// c67a81026c8b, branch impl-conditional-authz-review, with three %v of a slice spelled out:
// github.com/upamanyus/kubernetes goose-lean-authz-fmt2) the way kube-apiserver runs it, over leaf
// authorizers that behave arbitrarily: every choice a leaf makes is a math/rand Int63n(k), whose
// spec (Spec/math/rand/Int63n.lean) says only that the result is in [0, k), so a theorem about
// Main holds for every leaf behaviour, including leaves that lie in phase 2.
//
// The protocol (Main): phase 1 asks the union authorizer for a conditions-aware decision d; if d is
// Allow the request is admitted; otherwise, if Allow is among d's possible decisions, phase 2 asks
// the union to evaluate d's conditions against the request's data. Main panics if
//
//   - (C1) the phase-2 decision is not one of Allow, Deny, NoOpinion;
//   - (C2) the phase-2 decision is not one of phase 1's possible decisions (a lying leaf must not
//     make the union return a decision phase 1 excluded);
//   - (C3) d is not Allow and d's failure decision is not one of its possible decisions.
//
// The robustness theorem about Main (no thread panics or gets stuck) therefore implies the three.
// MainStrict also checks C3 when d is Allow, where it does not hold: FailureDecision is documented
// to be Deny or NoOpinion, and an unconditional Allow's only possible decision is Allow
// (authz_test.go).
package authz

import (
	"context"
	"errors"
	"math/rand"

	"k8s.io/apimachinery/pkg/runtime"
	"k8s.io/apimachinery/pkg/runtime/schema"
	"k8s.io/apiserver/pkg/authentication/user"
	"k8s.io/apiserver/pkg/authorization/authorizer"
	"k8s.io/apiserver/pkg/authorization/union"
)

func arbBool() bool {
	return rand.Int63n(2) == 0
}

// arbErr is nil or an error, arbitrarily.
func arbErr() error {
	if arbBool() {
		return nil
	}
	return errors.New("arbitrary error")
}

func arbReason() string {
	if arbBool() {
		return ""
	}
	return "arbitrary reason"
}

// arbDecisionValue is Deny, Allow, NoOpinion or a value outside the three, arbitrarily.
func arbDecisionValue() authorizer.Decision {
	return authorizer.Decision(rand.Int63n(4))
}

// arbName is an authorizer name for a union, from a fixed list with valid names, an empty one, one
// that is not a DNS-1123 subdomain, and repeats (so a union may get the same name twice).
func arbName() string {
	names := []string{"x", "y", "", "Not_A_DNS_Name", "x", "a"}
	return names[rand.Int63n(6)]
}

// arbID is a condition ID from a fixed list with valid label keys and invalid ones: empty, not a
// label key, no domain prefix, a reserved domain (*.k8s.io); two picks may repeat (duplicate IDs).
func arbID() string {
	ids := []string{"example.com/c1", "example.com/c2", "example.com/c3", "example.org/c4",
		"", "not a key", "c5", "k8s.io/c6"}
	return ids[rand.Int63n(8)]
}

// arbType is a condition type: none (valid), a valid label key, an invalid one, or a reserved one.
func arbType() string {
	types := []string{"", "", "example.com/t", "bad type", authorizer.ConditionTypeAuthorizationCEL}
	return types[rand.Int63n(5)]
}

// arbResult is an arbitrary condition evaluation result: true, false, an error (possibly nil, which
// the library replaces by an error of its own) or unevaluatable.
func arbResult() authorizer.ConditionEvaluationResult {
	switch rand.Int63n(4) {
	case 0:
		return authorizer.ConditionEvaluationResultBoolean(true)
	case 1:
		return authorizer.ConditionEvaluationResultBoolean(false)
	case 2:
		return authorizer.ConditionEvaluationResultError(arbErr())
	default:
		return authorizer.ConditionsEvaluationResultUnevaluatable()
	}
}

// arbCondition is a condition whose ID and type are chosen when it is made (arbConds) and whose
// evaluation is arbitrary each time.
type arbCondition struct {
	id  string
	typ string
}

func (c arbCondition) GetID() string {
	return c.id
}

func (c arbCondition) GetType() string {
	return c.typ
}

func (c arbCondition) GetCondition() string {
	return "arbitrary condition"
}

func (c arbCondition) GetDescription() string {
	return ""
}

func (c arbCondition) Evaluate(ctx context.Context, data authorizer.ConditionsData) authorizer.ConditionEvaluationResult {
	return arbResult()
}

// arbConds is a slice of 0 to 3 arbitrary conditions.
func arbConds() []authorizer.Condition {
	n := rand.Int63n(4)
	var cs []authorizer.Condition
	for i := int64(0); i < n; i++ {
		cs = append(cs, arbCondition{id: arbID(), typ: arbType()})
	}
	return cs
}

// arbDecision is an arbitrary conditions-aware decision, built with the library's constructors:
// unconditional (with or without a reason and an error), a conditions map of arbitrary conditions,
// and, if depth > 0, a union of arbitrary decisions of depth-1 under arbitrary names.
func arbDecision(depth uint64) authorizer.ConditionsAwareDecision {
	switch rand.Int63n(5) {
	case 0:
		return authorizer.ConditionsAwareDecisionDeny(arbReason(), arbErr())
	case 1:
		return authorizer.ConditionsAwareDecisionAllow(arbReason(), arbErr())
	case 2:
		return authorizer.ConditionsAwareDecisionNoOpinion(arbReason(), arbErr())
	case 3:
		return authorizer.ConditionsAwareDecisionConditionsMap(arbConds(), arbConds(), arbConds())
	default:
		if depth == 0 {
			return authorizer.ConditionsAwareDecisionConditionsMap(arbConds(), arbConds(), arbConds())
		}
		var u authorizer.ConditionsAwareDecisionUnion
		n := rand.Int63n(4)
		for i := int64(0); i < n; i++ {
			u.Add(arbName(), arbDecision(depth-1))
		}
		return u.ToDecision()
	}
}

// arbMaybeEval is an authorizer's arbitrary partial evaluation of a condition.
func arbMaybeEval(ctx context.Context, cond authorizer.Condition, data authorizer.ConditionsData) authorizer.ConditionEvaluationResult {
	return arbResult()
}

// arbEval is an authorizer's arbitrary evaluation of a condition.
func arbEval(ctx context.Context, cond authorizer.Condition, data authorizer.ConditionsData) (bool, error) {
	return arbBool(), arbErr()
}

// arbAuthorizer is a conditions-aware authorizer that behaves arbitrarily (an untrusted webhook):
// its phase-1 decisions are arbDecision(depth), and in phase 2 it either lies (an arbitrary
// decision, reason and error) or evaluates with the library's helpers and arbitrary condition
// results.
type arbAuthorizer struct {
	depth uint64
}

func (z arbAuthorizer) Authorize(ctx context.Context, a authorizer.Attributes) (authorizer.Decision, string, error) {
	return arbDecisionValue(), arbReason(), arbErr()
}

func (z arbAuthorizer) ConditionsAwareAuthorize(ctx context.Context, a authorizer.Attributes) authorizer.ConditionsAwareDecision {
	return arbDecision(z.depth)
}

func (z arbAuthorizer) EvaluateConditions(ctx context.Context, d authorizer.ConditionsAwareDecision, data authorizer.ConditionsData) (authorizer.Decision, string, error) {
	switch rand.Int63n(4) {
	case 0:
		// a lying authorizer
		return arbDecisionValue(), arbReason(), arbErr()
	case 1:
		// partial evaluation, rounded down to an unconditional decision
		pd := authorizer.PartiallyEvaluateConditionsAwareDecision(ctx, d, data, arbMaybeEval)
		dec, reason, err := pd.UnconditionalPartsOrFailClosed()
		return dec, reason, err
	case 2:
		// full evaluation of a conditions map
		if d.IsConditionsMap() {
			dec, reason, err := d.ConditionsMap().Evaluate(ctx, data, arbEval)
			return dec, reason, err
		}
		return d.FailureDecision(), "failed closed", authorizer.ErrorConditionEvaluationNotSupported
	default:
		return authorizer.DecisionDeny, "", authorizer.ErrorConditionEvaluationNotSupported
	}
}

// legacyAuthorize is a conditions-unaware authorizer (authorizer.AuthorizerFunc) with arbitrary
// decisions, including values outside Deny, Allow, NoOpinion.
func legacyAuthorize(ctx context.Context, a authorizer.Attributes) (authorizer.Decision, string, error) {
	return arbDecisionValue(), arbReason(), arbErr()
}

// emptyData is the request's data for phase 2: every method returns its zero value.
type emptyData struct{}

func (emptyData) GetName() string                             { return "" }
func (emptyData) GetNamespace() string                        { return "" }
func (emptyData) GetResource() schema.GroupVersionResource    { return schema.GroupVersionResource{} }
func (emptyData) GetSubresource() string                      { return "" }
func (emptyData) GetOperation() authorizer.AdmissionOperation { return "" }
func (emptyData) GetOperationOptions() runtime.Object         { return nil }
func (emptyData) IsDryRun() bool                              { return false }
func (emptyData) GetObject() runtime.Object                   { return nil }
func (emptyData) GetOldObject() runtime.Object                { return nil }
func (emptyData) GetKind() schema.GroupVersionKind            { return schema.GroupVersionKind{} }
func (emptyData) GetUserInfo() user.Info                      { return nil }

// newChain is the authorizer chain: two arbitrary conditions-aware authorizers around a legacy one,
// in a union.
func newChain() (authorizer.Authorizer, error) {
	return union.New(
		union.NamedAuthorizer{AuthorizerName: "a", Authorizer: arbAuthorizer{depth: 2}},
		union.NamedAuthorizer{AuthorizerName: "legacy", Authorizer: authorizer.AuthorizerFunc(legacyAuthorize)},
		union.NamedAuthorizer{AuthorizerName: "b", Authorizer: arbAuthorizer{depth: 2}},
	)
}

// twoPhase runs phase 2 on phase 1's decision d where kube-apiserver would, and checks C1-C3 (C3
// also when d is Allow if strict).
func twoPhase(ctx context.Context, a authorizer.Authorizer, d authorizer.ConditionsAwareDecision, strict bool) {
	pd := d.PossibleDecisions()
	if strict && d.IsAllow() && !pd.Has(d.FailureDecision()) {
		panic("C3 (strict): the failure decision of an Allow is not a possible decision")
	}
	if d.IsAllow() {
		// admitted in phase 1
		return
	}
	if !pd.Has(d.FailureDecision()) {
		panic("C3: the failure decision is not a possible decision")
	}
	if !pd.Has(authorizer.DecisionAllow) {
		// denied (or no opinion) in phase 1
		return
	}
	dec, _, _ := a.EvaluateConditions(ctx, d, emptyData{})
	if dec != authorizer.DecisionAllow && dec != authorizer.DecisionDeny && dec != authorizer.DecisionNoOpinion {
		panic("C1: phase 2 returned an unknown decision")
	}
	if !pd.Has(dec) {
		panic("C2: phase 2 returned a decision phase 1 excluded")
	}
}

// Main runs one request through the two phases and checks C1-C3.
func Main() {
	ctx := context.Background()
	a, err := newChain()
	if err != nil {
		return
	}
	d := a.ConditionsAwareAuthorize(ctx, authorizer.AttributesRecord{})
	twoPhase(ctx, a, d, false)
}

// MainStrict is Main with C3 checked also when phase 1 allows (it fails then; see the package
// comment).
func MainStrict() {
	ctx := context.Background()
	a, err := newChain()
	if err != nil {
		return
	}
	d := a.ConditionsAwareAuthorize(ctx, authorizer.AttributesRecord{})
	twoPhase(ctx, a, d, true)
}
