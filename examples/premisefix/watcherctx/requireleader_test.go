package watcherctx

// T5-a (Q2: translated, no trusted triple): clientv3.WithRequireLeader (client/v3/ctx.go:28-38) is
// metadata.NewOutgoingContext(ctx, md) with md the caller's outgoing metadata copied (or new) and
// hasleader set: a context.WithValue at grpc's outgoing key, so every other key, Done, Err,
// Deadline and the cause are the parent's, and the parent's metadata map is not written.

import (
	"context"
	"errors"
	"testing"
	"time"

	clientv3 "go.etcd.io/etcd/client/v3"
	"google.golang.org/grpc/metadata"
)

type k1 struct{}

func TestWithRequireLeaderValues(t *testing.T) {
	cause := errors.New("cause")
	parent, cancel := context.WithDeadlineCause(context.Background(), time.Now().Add(time.Hour), cause)
	parent = context.WithValue(parent, k1{}, "v1")
	for _, p := range []context.Context{parent, metadata.NewOutgoingContext(parent, metadata.Pairs("a", "1"))} {
		c := clientv3.WithRequireLeader(p)
		if c.Value(k1{}) != "v1" {
			t.Fatalf("Value(k1) = %v", c.Value(k1{}))
		}
		if c.Done() != p.Done() {
			t.Fatal("Done differs from the parent's")
		}
		d1, ok1 := c.Deadline()
		d2, ok2 := p.Deadline()
		if d1 != d2 || ok1 != ok2 {
			t.Fatal("Deadline differs")
		}
		md, _ := metadata.FromOutgoingContext(c)
		pmd, _ := metadata.FromOutgoingContext(p)
		if got := md.Get("hasleader"); len(got) != 1 || got[0] != "true" {
			t.Fatalf("hasleader = %v", got)
		}
		for k, v := range pmd {
			if got := md.Get(k); len(got) != len(v) || (len(v) > 0 && got[0] != v[0]) {
				t.Fatalf("key %q: %v, parent %v", k, got, v)
			}
		}
		if len(md) != len(pmd)+1 {
			t.Fatalf("metadata %v: want the parent's %v plus hasleader", md, pmd)
		}
	}
	cancel()
	c := clientv3.WithRequireLeader(parent)
	<-c.Done()
	if c.Err() != context.Canceled || context.Cause(c) != context.Canceled {
		t.Fatalf("Err %v, Cause %v: want the parent's", c.Err(), context.Cause(c))
	}
}

func TestWithRequireLeaderNoAlias(t *testing.T) {
	pmd := metadata.Pairs("a", "1")
	p := metadata.NewOutgoingContext(context.Background(), pmd)
	_ = clientv3.WithRequireLeader(p)
	if len(pmd) != 1 || len(pmd.Get("hasleader")) != 0 {
		t.Fatalf("the parent's metadata was written: %v", pmd)
	}
}
