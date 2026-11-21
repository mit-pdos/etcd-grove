package grpcdifftest_test

import (
	"context"
	"fmt"
	"io"
	"net"
	"strconv"
	"sync"
	"sync/atomic"
	"testing"
	"time"

	"google.golang.org/grpc"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/status"

	"models.lab/internal/grpcdifftest/svc"
)

// TestStopMidStream: Stop while a bidirectional stream is open: Recv fails with Unavailable and
// the handler's context is canceled.
func TestStopMidStream(t *testing.T) {
	srv := svc.New()
	l, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	s := grpc.NewServer()
	svc.RegisterEchoServer(s, srv)
	go s.Serve(l)
	_, c := dial(t, l.Addr().String())
	st, err := c.Bidi(ctx5(t))
	if err != nil {
		t.Fatal(err)
	}
	id := fresh()
	st.Send(svc.M(id + " echo 1"))
	if m, err := st.Recv(); err != nil || m.GetValue() != "1" {
		t.Fatal(m, err)
	}
	s.Stop()
	_, err = st.Recv()
	wantStatus(t, err, codes.Unavailable, "")
	eventually(t, "the handler's end", func() bool { s := srv.Seen(id); return s != nil && s.CtxErr != nil })
}

// TestCutMidStream: a connection cut under a server stream: Recv fails with Unavailable after
// the messages received before the cut.
func TestCutMidStream(t *testing.T) {
	srv, addr := serve(t)
	p := newProxy(t, addr)
	_, c := dial(t, p.l.Addr().String())
	id := fresh()
	st, err := c.ServerStream(ctx5(t), svc.M(id+" forever"))
	if err != nil {
		t.Fatal(err)
	}
	for i := 1; i <= 5; i++ {
		if m, err := st.Recv(); err != nil || m.GetValue() != strconv.Itoa(i) {
			t.Fatal(m, err)
		}
	}
	p.cut()
	for {
		_, err := st.Recv()
		if err != nil {
			wantStatus(t, err, codes.Unavailable, "")
			break
		}
	}
	eventually(t, "the handler's end", func() bool { s := srv.Seen(id); return s != nil && s.CtxErr != nil })
	if srv.Runs(id) != 1 {
		t.Fatal(srv.Runs(id))
	}
}

// TestAtMostOnce: calls and streams under connection cuts (a proxy cut every few milliseconds) and
// deadlines. What holds of every behavior of grpc-go, and of every behavior of the model (run.sh
// also runs this test with the model's choices random): a handler runs at most once per call; a
// call that succeeds ran its handler exactly once and returns its reply; a failed call's code is
// not OK; a server stream's messages arrive in order and all of them before its successful end,
// but for one exception. grpc-go v1.84.0 can end a server stream cleanly (RecvMsg's io.EOF) with no
// message and no handler run: after a transparent retry (the first attempt refused), when the
// replayed SendMsg's write on the new attempt fails, csAttempt.sendMsg returns io.EOF and
// clientStream.retryLocked returns it as it is (shouldRetry passes a non-retryable error through),
// bypassing recvMsg's status check (nonissues/grpc-transparent-retry-spurious-eof.md). The model
// keeps that code, and its random choices reach it (refusals); the test counts such an end apart
// (`spurious`, logged) and requires it to come with no message and no handler run.
func TestAtMostOnce(t *testing.T) {
	var spurious atomic.Int64
	defer func() { t.Logf("%d spurious clean ends of a server stream", spurious.Load()) }()
	srv, addr := serve(t)
	p := newProxy(t, addr)
	_, c := dial(t, p.l.Addr().String())
	stop := make(chan struct{})
	go func() {
		for {
			select {
			case <-stop:
				return
			case <-time.After(15 * time.Millisecond):
				p.cut()
			}
		}
	}()
	defer close(stop)
	var wg sync.WaitGroup
	errs := make(chan error, 1000)
	var oks, fails sync.Map
	for g := 0; g < 8; g++ {
		wg.Add(1)
		go func(g int) {
			defer wg.Done()
			for i := 0; i < 40; i++ {
				id := fresh()
				ctx, cancel := context.WithTimeout(context.Background(), time.Duration(5+i%20)*5*time.Millisecond)
				var err error
				got := ""
				switch i % 3 {
				case 0:
					var r *svc.Msg
					r, err = c.Unary(ctx, svc.M(id+" echo "+id), grpc.WaitForReady(i%2 == 0))
					if err == nil {
						got = r.GetValue()
					}
				case 1:
					var st grpc.ServerStreamingClient[svc.Msg]
					st, err = c.ServerStream(ctx, svc.M(id+" stream 20"))
					if err == nil {
						n := 0
						for {
							m, rerr := st.Recv()
							if rerr != nil {
								if rerr != io.EOF {
									err = rerr
								} else if n == 0 && srv.Runs(id) == 0 {
									// grpc-go's spurious end after a transparent retry (above):
									// a behavior of grpc-go, kept by the model; not a success.
									spurious.Add(1)
									err = rerr
								} else if n != 20 {
									errs <- fmt.Errorf("%s: EOF after %d messages", id, n)
								}
								break
							}
							n++
							if m.GetValue() != strconv.Itoa(n) {
								errs <- fmt.Errorf("%s: message %d is %q", id, n, m.GetValue())
							}
						}
						got = id
					}
				case 2:
					var st grpc.ClientStreamingClient[svc.Msg, svc.Msg]
					st, err = c.ClientStream(ctx)
					if err == nil {
						st.Send(svc.M(id + " a"))
						st.Send(svc.M(id + " b"))
						var r *svc.Msg
						r, err = st.CloseAndRecv()
						if err == nil {
							if r.GetValue() == id+" a,"+id+" b" {
								got = id
							} else {
								got = r.GetValue()
							}
						}
					}
				}
				cancel()
				if runs := srv.Runs(id); runs > 1 {
					errs <- fmt.Errorf("%s: handler ran %d times", id, runs)
				}
				if err == nil {
					oks.Store(id, true)
					if got != id {
						errs <- fmt.Errorf("%s: reply %q", id, got)
					}
					if srv.Runs(id) != 1 {
						errs <- fmt.Errorf("%s: succeeded, handler ran %d times", id, srv.Runs(id))
					}
				} else {
					fails.Store(id, true)
					if status.Code(err) == codes.OK {
						errs <- fmt.Errorf("%s: error with code OK: %v", id, err)
					}
				}
			}
		}(g)
	}
	wg.Wait()
	close(errs)
	for err := range errs {
		t.Error(err)
	}
	n := 0
	oks.Range(func(any, any) bool { n++; return true })
	t.Logf("%d of 320 calls succeeded", n)
}
