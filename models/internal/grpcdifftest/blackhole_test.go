package grpcdifftest_test

import (
	"context"
	"fmt"
	"io"
	"net"
	"sync"
	"testing"
	"time"

	"google.golang.org/grpc"

	"models.lab/internal/grpcdifftest/svc"
)

// holeProxy forwards connections to target, but while holed it accepts connections and drops
// every byte of them (etcd's test bridge's Blackhole); unhole closes those and forwards new ones.
type holeProxy struct {
	l      net.Listener
	mu     sync.Mutex
	holed  bool
	held   []net.Conn
	target string
}

func newHoleProxy(t *testing.T, target string) *holeProxy {
	l, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	p := &holeProxy{l: l, target: target}
	t.Cleanup(func() { l.Close(); p.unhole() })
	go func() {
		for {
			c, err := l.Accept()
			if err != nil {
				return
			}
			p.mu.Lock()
			if p.holed {
				p.held = append(p.held, c)
				p.mu.Unlock()
				go io.Copy(io.Discard, c)
				continue
			}
			p.mu.Unlock()
			s, err := net.Dial("tcp", target)
			if err != nil {
				c.Close()
				continue
			}
			go func() { io.Copy(s, c); s.Close() }()
			go func() { io.Copy(c, s); c.Close() }()
		}
	}()
	return p
}

func (p *holeProxy) hole() { p.mu.Lock(); p.holed = true; p.mu.Unlock() }

func (p *holeProxy) unhole() {
	p.mu.Lock()
	p.holed = false
	for _, c := range p.held {
		c.Close()
	}
	p.held = nil
	p.mu.Unlock()
}

// TestBlackhole: a wait-for-ready call made while its connection's bytes are all dropped waits
// (grpc-go sends nothing on a connection whose server preface has not arrived) and its handler
// does not run; once the hole ends (its connections closed), the call goes out on a new
// connection and succeeds, its handler run once.
func TestBlackhole(t *testing.T) {
	srv, addr := serve(t)
	p := newHoleProxy(t, addr)
	p.hole()
	_, c := dial(t, p.l.Addr().String())
	id := fresh()
	done := make(chan error, 1)
	go func() {
		ctx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
		defer cancel()
		r, err := c.Unary(ctx, svc.M(id+" echo up"), grpc.WaitForReady(true))
		if err == nil && r.GetValue() != "up" {
			err = fmt.Errorf("reply %q", r.GetValue())
		}
		done <- err
	}()
	time.Sleep(300 * time.Millisecond)
	select {
	case err := <-done:
		t.Fatalf("returned in the hole: %v", err)
	default:
	}
	if srv.Runs(id) != 0 {
		t.Fatal(srv.Runs(id))
	}
	p.unhole()
	if err := <-done; err != nil {
		t.Fatal(err)
	}
	if srv.Runs(id) != 1 {
		t.Fatal(srv.Runs(id))
	}
}
