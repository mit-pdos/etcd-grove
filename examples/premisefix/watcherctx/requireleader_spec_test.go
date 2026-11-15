package watcherctx

// T5-a, the restated trust-boundary axiom (7f-3a decision D1, the fallback; notes/k8s-7f5-freeze.md,
// "T5-a addendum"): WithRequireLeader.wp_proof over a watchCtx parent (WithRequireLeader.spec in
// Spec/go_etcd_io/etcd/client/v3/WithRequireLeader.lean). Its claims, each tested here on parents
// of every shape the walk of context.value distinguishes (a *valueCtx, a *cancelCtx, a *timerCtx,
// withoutCancelCtx, Background/TODO, a context type outside the standard library):
//
//   - every key that is not of the type of grpc's mdOutgoingKey answers as the parent's, through
//     Value (the WP form) and through the chain (a descendant's walk: WithCancel/WithValue of the
//     child, context.Cause, what Perennial's ctxValue models);
//   - Done, Err and Cause are the parent's (the same descriptor: the same Done channel, Deadline);
//   - the result's Value(&cancelCtxKey) is the parent's (context.Cause, WithCancel's propagation).
//
// TestOtherKeysCheckDetects shows the check is not vacuous: it fails on a variant of
// WithRequireLeader that also changes another key.

import (
	"context"
	"errors"
	"fmt"
	"testing"
	"time"

	clientv3 "go.etcd.io/etcd/client/v3"
	"google.golang.org/grpc/metadata"
)

// mdOutgoingKey is a key of the same shape and name as grpc's (an empty struct), of another type:
// not grpc's key, so the child must answer it as the parent does.
type mdOutgoingKey struct{}

type kInt int
type kStr string

// foreignCtx is a context outside the standard library (context.value's default arm calls its
// Value method): it answers kStr("foreign") itself and records the keys it is asked.
type foreignCtx struct {
	context.Context
	asked []any
}

func (f *foreignCtx) Value(k any) any {
	f.asked = append(f.asked, k)
	if k == kStr("foreign") {
		return "fv"
	}
	return f.Context.Value(k)
}

// testKeys are the keys tried: the caller's, library-like keys of several kinds, a key of the
// same shape as grpc's outgoing key, nil, a pointer, an error, and a key of an uncomparable type
// (compared with keys of other types only: no panic; the answers compared are comparable).
func testKeys() []any {
	return []any{k1{}, kInt(1), kStr("foreign"), "string-key", 7, mdOutgoingKey{}, nil,
		&struct{ x []int }{}, errors.New("an error as a key"), []int{1}}
}

// parents returns parents of each shape, each with k1{} ↦ "v1" somewhere up its chain, some with
// outgoing metadata of their own, and their cancel functions.
func parents() (map[string]context.Context, func()) {
	var cancels []func()
	bg := context.Background()
	ps := map[string]context.Context{
		"background": bg,
		"todo":       context.TODO(),
	}
	v := context.WithValue(bg, k1{}, "v1")
	ps["value"] = v
	ps["value-md"] = metadata.NewOutgoingContext(v, metadata.Pairs("a", "1"))
	c, cc := context.WithCancelCause(v)
	cancels = append(cancels, func() { cc(nil) })
	ps["cancel"] = c
	tm, tc := context.WithDeadline(context.WithValue(bg, kInt(1), "i1"), time.Now().Add(time.Hour))
	cancels = append(cancels, tc)
	ps["timer"] = tm
	ps["without-cancel"] = context.WithoutCancel(c)
	f := &foreignCtx{Context: context.WithValue(v, kStr("x"), "y")}
	ps["foreign"] = f
	ps["foreign-md"] = metadata.NewOutgoingContext(f, metadata.Pairs("b", "2"))
	return ps, func() {
		for _, c := range cancels {
			c()
		}
	}
}

// otherKeysAsParent checks the claims above of a child c of p: every key in keys answers as p's,
// directly and through descendants of c, Done and Deadline are p's. It returns the first difference.
func otherKeysAsParent(p, c context.Context, keys []any) error {
	if c.Done() != p.Done() {
		return errors.New("Done differs from the parent's")
	}
	d1, ok1 := c.Deadline()
	d2, ok2 := p.Deadline()
	if d1 != d2 || ok1 != ok2 {
		return errors.New("Deadline differs from the parent's")
	}
	if c.Err() != p.Err() {
		return fmt.Errorf("Err %v, parent %v", c.Err(), p.Err())
	}
	if context.Cause(c) != context.Cause(p) {
		return fmt.Errorf("Cause %v, parent %v", context.Cause(c), context.Cause(p))
	}
	cw, cancelC := context.WithCancel(c)
	defer cancelC()
	pw, cancelP := context.WithCancel(p)
	defer cancelP()
	type other struct{}
	cv := context.WithValue(c, other{}, "o")
	pv := context.WithValue(p, other{}, "o")
	for _, k := range keys {
		if got, want := c.Value(k), p.Value(k); got != want {
			return fmt.Errorf("Value(%T %v) = %v, parent %v", k, k, got, want)
		}
		if got, want := cw.Value(k), pw.Value(k); got != want {
			return fmt.Errorf("through WithCancel: Value(%T %v) = %v, parent %v", k, k, got, want)
		}
		if got, want := cv.Value(k), pv.Value(k); got != want {
			return fmt.Errorf("through WithValue: Value(%T %v) = %v, parent %v", k, k, got, want)
		}
	}
	return nil
}

// TestWithRequireLeaderOtherKeys: every key other than grpc's outgoing key answers as the parent's,
// through Value and through the chain, and Done, Err, Cause and Deadline are the parent's, before
// and after the parent is cancelled.
func TestWithRequireLeaderOtherKeys(t *testing.T) {
	ps, cancel := parents()
	for name, p := range ps {
		c := clientv3.WithRequireLeader(p)
		if err := otherKeysAsParent(p, c, testKeys()); err != nil {
			t.Fatalf("%s: %v", name, err)
		}
	}
	cancel()
	for name, p := range ps {
		c := clientv3.WithRequireLeader(p)
		if err := otherKeysAsParent(p, c, testKeys()); err != nil {
			t.Fatalf("%s, cancelled: %v", name, err)
		}
	}
}

// TestWithRequireLeaderCancelPropagates: WithCancel of the child is cancelled with the parent, its
// Cause the parent's (WithCancel's propagateCancel reads the child's Value(&cancelCtxKey), which
// is the parent's *cancelCtx).
func TestWithRequireLeaderCancelPropagates(t *testing.T) {
	errX := errors.New("errX")
	p, cancel := context.WithCancelCause(context.Background())
	cw, cancelW := context.WithCancel(clientv3.WithRequireLeader(p))
	defer cancelW()
	cancel(errX)
	select {
	case <-cw.Done():
	case <-time.After(10 * time.Second):
		t.Fatal("WithCancel of the child not cancelled with the parent")
	}
	if cw.Err() != context.Canceled || context.Cause(cw) != errX {
		t.Fatalf("Err %v, Cause %v: want Canceled, errX", cw.Err(), context.Cause(cw))
	}
}

// TestWithRequireLeaderForeignParentAsked: over a parent outside the standard library, the child's
// Value of another key is the parent's Value of that key (context.value's default arm calls it).
func TestWithRequireLeaderForeignParentAsked(t *testing.T) {
	f := &foreignCtx{Context: context.Background()}
	c := clientv3.WithRequireLeader(f)
	f.asked = nil
	if c.Value(kStr("foreign")) != "fv" {
		t.Fatal("the foreign parent's answer is not the child's")
	}
	if len(f.asked) != 1 || f.asked[0] != kStr("foreign") {
		t.Fatalf("the parent was asked %v, want [foreign]", f.asked)
	}
}

// withRequireLeaderAlsoOther is WithRequireLeader that also changes another key (a wrong model).
func withRequireLeaderAlsoOther(k any) func(context.Context) context.Context {
	return func(ctx context.Context) context.Context {
		return context.WithValue(clientv3.WithRequireLeader(ctx), k, "changed")
	}
}

// TestOtherKeysCheckDetects: the check fails on a WithRequireLeader that also changes another key,
// for each key tried but nil (WithValue refuses a nil key) and the uncomparable-typed one's
// pointer (fresh in testKeys, so tried below by its own value).
func TestOtherKeysCheckDetects(t *testing.T) {
	ps, cancel := parents()
	defer cancel()
	for _, k := range []any{k1{}, kInt(1), kStr("foreign"), "string-key", 7, mdOutgoingKey{}} {
		bad := withRequireLeaderAlsoOther(k)
		for name, p := range ps {
			if otherKeysAsParent(p, bad(p), testKeys()) == nil {
				t.Fatalf("%s: the check missed a change of key %T %v", name, k, k)
			}
		}
	}
	// A change of the cancel key's answer (a child detached from its parent's cancellation).
	for name, p := range ps {
		if p.Done() == nil {
			continue
		}
		detached := clientv3.WithRequireLeader(context.WithoutCancel(p))
		if otherKeysAsParent(p, detached, testKeys()) == nil {
			t.Fatalf("%s: the check missed a detached child", name)
		}
	}
}

// TestWithRequireLeaderOutgoingKeyChanged: grpc's outgoing key is the one key whose answer changes
// (so the axiom's exception is not empty): the child's outgoing metadata has hasleader, the
// parent's has not.
func TestWithRequireLeaderOutgoingKeyChanged(t *testing.T) {
	p := metadata.NewOutgoingContext(context.Background(), metadata.Pairs("a", "1"))
	c := clientv3.WithRequireLeader(p)
	md, _ := metadata.FromOutgoingContext(c)
	pmd, _ := metadata.FromOutgoingContext(p)
	if len(md.Get("hasleader")) != 1 || len(pmd.Get("hasleader")) != 0 {
		t.Fatalf("child %v, parent %v", md, pmd)
	}
}
