// Package keepalive checks sweep-repairs-1 B2b: the client lessor's keepAliveCtxCloser compares
// Value(keepAliveCtxKey{}) only of the contexts KeepAlive stored, each a
// context.WithValue(ctx, keepAliveCtxKey{}, &ctx) answering its own key (keepAliveOk), never of
// the user's context. The old axiom (context.ValueKeepAlive) claimed the answer of every context;
// a user context whose Value panics at that key refutes it, and the real path never asks it.
package keepalive

import (
	"context"
	"net"
	"reflect"
	"sync/atomic"
	"testing"
	"time"

	"github.com/mit-pdos/etcd-grove/examples/lib/etcdstart"
	"go.uber.org/zap"
)

// panicKA is a user context that panics on Value at a key of a type named keepAliveCtxKey (so
// the old axiom's claim is false of it), and counts such calls.
type panicKA struct {
	context.Context
	asked *atomic.Int64
}

func (p panicKA) Value(k any) any {
	if k != nil && reflect.TypeOf(k).Name() == "keepAliveCtxKey" {
		p.asked.Add(1)
		panic("Value(keepAliveCtxKey{}) of a user context")
	}
	return p.Context.Value(k)
}

func freeAddr(t *testing.T) string {
	l, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	defer l.Close()
	return l.Addr().String()
}

func TestKeepAliveCloserAsksOnlyStoredContexts(t *testing.T) {
	t.Chdir(t.TempDir())
	lg := zap.NewNop()
	caddr := freeAddr(t)
	s, err := etcdstart.StartServer("ka1", freeAddr(t), caddr, lg)
	if err != nil {
		t.Fatal(err)
	}
	defer s.Stop()
	if err := etcdstart.Serve(s, caddr); err != nil {
		t.Fatal(err)
	}
	<-s.ReadyNotify()
	cli, err := etcdstart.NewClient(caddr, lg)
	if err != nil {
		t.Fatal(err)
	}
	defer cli.Close()
	var asked atomic.Int64
	closed := 0
	for round := 0; round < 20; round++ {
		gctx, gcancel := context.WithTimeout(context.Background(), 5*time.Second)
		lr, err := cli.Grant(gctx, 30)
		gcancel()
		if err != nil {
			t.Fatal(err)
		}
		// several keep-alives on one lease, each over a user context that panics at the key
		var cancels []context.CancelFunc
		var chs []<-chan any
		for i := 0; i < 3; i++ {
			base, cancel := context.WithCancel(context.Background())
			ch, err := cli.KeepAlive(panicKA{base, &asked}, lr.ID)
			if err != nil {
				t.Fatal(err)
			}
			cancels = append(cancels, cancel)
			out := make(chan any)
			go func() {
				for range ch {
				}
				close(out)
			}()
			chs = append(chs, out)
		}
		// cancel each: keepAliveCtxCloser runs, compares Value(keepAliveCtxKey{}) of the stored
		// contexts, closes that keep-alive's channel
		for i, cancel := range cancels {
			cancel()
			select {
			case <-chs[i]:
				closed++
			case <-time.After(10 * time.Second):
				t.Fatalf("round %d: keep-alive %d's channel not closed after its context was canceled", round, i)
			}
		}
	}
	if n := asked.Load(); n != 0 {
		t.Fatalf("the user context was asked Value(keepAliveCtxKey{}) %d times", n)
	}
	t.Logf("%d keep-alive channels closed by keepAliveCtxCloser; the user contexts (whose Value panics at the key) were never asked", closed)
}

// The old axiom's claim is false of panicKA: Value at a key of that name panics.
func TestOldClaimFalse(t *testing.T) {
	type keepAliveCtxKey struct{} // a key of the same type name, standing in for clientv3's unexported one
	var asked atomic.Int64
	p := panicKA{context.Background(), &asked}
	defer func() {
		if recover() == nil {
			t.Fatal("no panic")
		}
		t.Logf("a user context (an isContext) panics in Value at keepAliveCtxKey: the old axiom's claim is false of it")
	}()
	p.Value(keepAliveCtxKey{})
}
