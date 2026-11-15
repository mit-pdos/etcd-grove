package watcherctx

// T5-a: clientv3.WithRequireLeader (client/v3/ctx.go:28-38) is metadata.NewOutgoingContext(ctx, md)
// with md the caller's outgoing metadata copied (or new) and hasleader set: a context.WithValue at
// grpc's outgoing key, so every other key, Done, Err, Deadline and the cause are the parent's, and
// the parent's metadata map is not written.
//
// 7f-3a decision D1 (the fallback): WithRequireLeader is not translated; its trust-boundary axiom
// WithRequireLeader.wp_proof is restated over a watchCtx parent (requireleader_spec_test.go tests
// the restated text). The tests below were written for the translation (Q2, superseded) and still
// describe the code: the metadata is the parent's plus hasleader (which the axiom does not state,
// decision D3), and is not aliased.
//
// The no-alias property does not rest on the Copy at the pin: FromOutgoingContext already returns a
// fresh map with copied value slices (grpc v1.84.0 metadata.go:342-348, copyOf), so no test of
// WithRequireLeader fails without the Copy (TestWithRequireLeaderNoAliasWithoutCopy runs a copy of
// WithRequireLeader without it). TestWithRequireLeaderNoAliasDetects shows the no-alias check is not
// vacuous: it catches a writer that does alias the parent's map.

import (
	"context"
	"errors"
	"testing"
	"time"

	"go.etcd.io/etcd/api/v3/v3rpc/rpctypes"
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

// TestWithRequireLeaderCause: a parent cancelled with a cause of its own (WithCancelCause), and a
// parent whose deadline expires with one (WithDeadlineCause): the child's Err and Cause are the
// parent's, the cause the one the parent was given.
func TestWithRequireLeaderCause(t *testing.T) {
	errX := errors.New("errX")
	p, cancel := context.WithCancelCause(context.WithValue(context.Background(), k1{}, "v1"))
	for _, c := range []context.Context{clientv3.WithRequireLeader(p),
		clientv3.WithRequireLeader(metadata.NewOutgoingContext(p, metadata.Pairs("a", "1")))} {
		cancel(errX)
		<-c.Done()
		if c.Err() != context.Canceled || context.Cause(c) != errX {
			t.Fatalf("Err %v, Cause %v: want Canceled, errX", c.Err(), context.Cause(c))
		}
	}
	p2, cancel2 := context.WithDeadlineCause(context.Background(), time.Now().Add(time.Millisecond), errX)
	defer cancel2()
	c2 := clientv3.WithRequireLeader(p2)
	<-c2.Done()
	if c2.Err() != context.DeadlineExceeded || context.Cause(c2) != errX {
		t.Fatalf("Err %v, Cause %v: want DeadlineExceeded, errX", c2.Err(), context.Cause(c2))
	}
}

// parentMD is a parent's outgoing metadata whose hasleader key already holds another value.
func parentMD() metadata.MD {
	return metadata.MD{"a": {"1", "2"}, rpctypes.MetadataRequireLeaderKey: {"false"}}
}

// checkNoAlias fails if pmd (the map given to NewOutgoingContext for the parent) was written, or if
// writing the child's metadata (its hasleader slice, a value slice) reaches pmd.
func checkNoAlias(t *testing.T, pmd metadata.MD, c context.Context) bool {
	t.Helper()
	ok := true
	if got := pmd.Get(rpctypes.MetadataRequireLeaderKey); len(got) != 1 || got[0] != "false" {
		t.Logf("the parent's hasleader was written: %v", got)
		ok = false
	}
	md, _ := metadata.FromOutgoingContext(c)
	if got := md.Get(rpctypes.MetadataRequireLeaderKey); len(got) != 1 || got[0] != "true" {
		t.Logf("child's hasleader = %v", got)
		ok = false
	}
	if len(md["a"]) > 0 {
		md["a"][0] = "x"
	}
	if pmd["a"][0] != "1" || len(pmd) != 2 {
		t.Logf("the parent's metadata was written: %v", pmd)
		ok = false
	}
	return ok
}

// TestWithRequireLeaderNoAlias: the parent's metadata, whose hasleader key exists with another
// value, is not written by WithRequireLeader, nor through the child's metadata.
func TestWithRequireLeaderNoAlias(t *testing.T) {
	pmd := parentMD()
	c := clientv3.WithRequireLeader(metadata.NewOutgoingContext(context.Background(), pmd))
	if !checkNoAlias(t, pmd, c) {
		t.Fatal("aliasing")
	}
}

// withRequireLeaderNoCopy is WithRequireLeader (client/v3/ctx.go:28-38) without the Copy.
func withRequireLeaderNoCopy(ctx context.Context) context.Context {
	md, ok := metadata.FromOutgoingContext(ctx)
	if !ok {
		return metadata.NewOutgoingContext(ctx, metadata.Pairs(rpctypes.MetadataRequireLeaderKey, rpctypes.MetadataHasLeader))
	}
	md.Set(rpctypes.MetadataRequireLeaderKey, rpctypes.MetadataHasLeader)
	return metadata.NewOutgoingContext(ctx, md)
}

// TestWithRequireLeaderNoAliasWithoutCopy: without the Copy the parent is still not written
// (FromOutgoingContext's fresh map): the property the proof needs holds of the code either way.
func TestWithRequireLeaderNoAliasWithoutCopy(t *testing.T) {
	pmd := parentMD()
	c := withRequireLeaderNoCopy(metadata.NewOutgoingContext(context.Background(), pmd))
	if !checkNoAlias(t, pmd, c) {
		t.Fatal("aliasing")
	}
}

// TestWithRequireLeaderNoAliasDetects: the check catches a writer that aliases the parent's map
// (sets hasleader in it and reuses it as the child's).
func TestWithRequireLeaderNoAliasDetects(t *testing.T) {
	pmd := parentMD()
	p := metadata.NewOutgoingContext(context.Background(), pmd)
	pmd.Set(rpctypes.MetadataRequireLeaderKey, rpctypes.MetadataHasLeader)
	if checkNoAlias(t, pmd, metadata.NewOutgoingContext(p, pmd)) {
		t.Fatal("the no-alias check missed an aliasing writer")
	}
}
