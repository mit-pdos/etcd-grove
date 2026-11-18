package incomingofattack

import (
	"context"
	"fmt"
	"io"
	"net"
	"sync"
	"testing"
	"time"
	"unsafe"

	"google.golang.org/grpc"
	"google.golang.org/grpc/credentials/insecure"
	"google.golang.org/grpc/metadata"
)

type cancellableContext struct {
	context.Context
	lock         sync.RWMutex
	cancel       context.CancelFunc
	cancelReason error
}

func newCancellableContext(parent context.Context) *cancellableContext {
	ctx, cancel := context.WithCancel(parent)
	return &cancellableContext{Context: ctx, cancel: cancel}
}

func tok(ctx context.Context) string {
	md, ok := metadata.FromIncomingContext(ctx)
	if !ok {
		return "<none>"
	}
	v := md.Get("token")
	if len(v) == 0 {
		return "<nokey>"
	}
	return v[0]
}

type iface struct{ tab, data unsafe.Pointer }

// view p as a context.Context whose dynamic type is that of model (a *context.cancelCtx).
func punAs(model context.Context, p unsafe.Pointer) context.Context {
	var out context.Context
	m := (*iface)(unsafe.Pointer(&model))
	o := (*iface)(unsafe.Pointer(&out))
	o.tab = m.tab
	o.data = p
	return out
}

// W1's consequence: incomingOf constant on *cancellableContext values. Go: two wrappers differ.
func TestWrappersNotConstant(t *testing.T) {
	l1 := newCancellableContext(metadata.NewIncomingContext(context.Background(), metadata.Pairs("token", "A")))
	l2 := newCancellableContext(metadata.NewIncomingContext(context.Background(), metadata.Pairs("token", "B")))
	t.Logf("l1=%p tok=%s ; l2=%p tok=%s", l1, tok(l1), l2, tok(l2))
	if tok(l1) == tok(l2) {
		t.Fatal("same")
	}
}

// W0's consequence E(a): incomingOf(ccCtx a) = incomingOf(*cancelCtx a). Physically true under punning
// (both forward Value to field 0), so W0 alone refutes nothing.
// Attack (2): a user struct with an interface first field holding ci, viewed as *cancelCtx, answers as ci.
type userS struct {
	X     context.Context
	other int
}

func TestPunning(t *testing.T) {
	ci := metadata.NewIncomingContext(context.Background(), metadata.Pairs("token", "C"))
	cc, cancel := context.WithCancel(context.Background())
	defer cancel()
	t.Logf("cancelCtx type %T", cc)
	l := newCancellableContext(ci)
	v1 := punAs(cc, unsafe.Pointer(l))
	s := &userS{X: ci}
	v2 := punAs(cc, unsafe.Pointer(s))
	t.Logf("wrapper %T tok=%s ; wrapper-as-%T tok=%s ; userS-as-%T tok=%s (ci tok=%s)", l, tok(l), v1, tok(v1), v2, tok(v2), tok(ci))
	if tok(v1) != tok(l) || tok(v2) != tok(ci) {
		t.Fatal("punning differs")
	}
}

// Attack (3): afterFuncer parent: WithCancel rewrites c.Context to stopCtx{parent}; metadata unchanged.
type afCtx struct{ context.Context }

func (a afCtx) AfterFunc(f func()) func() bool { return func() bool { return true } }

func TestAfterFuncer(t *testing.T) {
	p := afCtx{metadata.NewIncomingContext(context.Background(), metadata.Pairs("token", "D"))}
	// make Done non-nil so propagateCancel reaches the afterFuncer branch
	pc, pcancel := context.WithCancel(p.Context)
	defer pcancel()
	p = afCtx{pc}
	c, cancel := context.WithCancel(p)
	defer cancel()
	// read field 0 of the *cancelCtx
	field0 := *(*context.Context)((*iface)(unsafe.Pointer(&c)).data)
	t.Logf("field0 %T (parent %T); child tok=%s", field0, p, tok(c))
	if tok(c) != "D" {
		t.Fatal("lost")
	}
	// derived children
	cc, cf := context.WithCancelCause(p)
	defer cf(nil)
	dc, dcf := context.WithTimeout(p, time.Hour)
	defer dcf()
	wc := context.WithoutCancel(p)
	vc := context.WithValue(p, "k", "v")
	t.Logf("cause %T %s; timer %T %s; without %T %s; value %T %s", cc, tok(cc), dc, tok(dc), wc, tok(wc), vc, tok(vc))
}

// Attacks (4)/(6): a real grpc server, two concurrent streams with different tokens.
func TestRealGrpcTwoStreams(t *testing.T) {
	lis, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	var mu sync.Mutex
	seen := map[string]string{}
	var both sync.WaitGroup
	both.Add(2)
	handler := func(srv any, ss grpc.ServerStream) error {
		ci := ss.Context()
		_, isAF := ci.(interface{ AfterFunc(func()) func() bool })
		c1, cancel := context.WithCancel(ci)
		defer cancel()
		l := &cancellableContext{Context: c1, cancel: cancel}
		mu.Lock()
		seen[tok(ci)] = fmt.Sprintf("ci=%T(%p) afterFuncer=%v child=%s wrapper=%s", ci, ci, isAF, tok(c1), tok(l))
		mu.Unlock()
		both.Done()
		both.Wait() // both streams alive at once: one run, two run contexts
		return nil
	}
	s := grpc.NewServer(grpc.UnknownServiceHandler(handler))
	go s.Serve(lis)
	defer s.Stop()
	conn, err := grpc.NewClient(lis.Addr().String(), grpc.WithTransportCredentials(insecure.NewCredentials()))
	if err != nil {
		t.Fatal(err)
	}
	defer conn.Close()
	var wg sync.WaitGroup
	for _, tk := range []string{"T1", "T2"} {
		wg.Add(1)
		go func(tk string) {
			defer wg.Done()
			ctx := metadata.AppendToOutgoingContext(context.Background(), "token", tk)
			st, err := conn.NewStream(ctx, &grpc.StreamDesc{ServerStreams: true, ClientStreams: true}, "/x.Y/Z")
			if err != nil {
				t.Error(err)
				return
			}
			st.CloseSend()
			var m []byte
			for st.RecvMsg(&m) != io.EOF {
				break
			}
		}(tk)
	}
	wg.Wait()
	for k, v := range seen {
		t.Logf("stream token %s: %s", k, v)
	}
	if len(seen) != 2 {
		t.Fatalf("seen %v", seen)
	}
}
