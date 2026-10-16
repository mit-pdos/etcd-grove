// Reproduction of issues/etcd-lease-requireleader-ctx-misaligned.md.
//
// Package clientv3, file client/v3/close_require_leader_ctx_test.go of go.etcd.io/etcd (module
// go.etcd.io/etcd/client/v3), at the etcd pin of etc/goose.py: 107edf7e4 (branch goose-lean of
// upamanyus/etcd).
//
// Run, in client/v3:
//
//	GOTOOLCHAIN=go1.27.1 go test . -run '^TestCloseRequireLeaderCtxMisaligned$' -count=1
//
// Fails at the pin (shows the bug): "C's channel still open after C's context was cancelled".
package clientv3

import (
	"context"
	"testing"
)

func TestCloseRequireLeaderCtxMisaligned(t *testing.T) {
	l := &lessor{keepAlives: make(map[LeaseID]*keepAlive), donec: make(chan struct{})}
	mk := func(ctx context.Context) (context.Context, chan *LeaseKeepAliveResponse) {
		ctx = context.WithValue(ctx, keepAliveCtxKey{}, &ctx) // as KeepAlive does
		return ctx, make(chan *LeaseKeepAliveResponse, 1)
	}
	ctxA, cancelA := context.WithCancel(WithRequireLeader(context.Background()))
	ctxB, cancelB := context.WithCancel(context.Background())
	ctxC, cancelC := context.WithCancel(context.Background())
	defer cancelA()
	defer cancelB()
	kA, chA := mk(ctxA)
	kB, chB := mk(ctxB)
	kC, chC := mk(ctxC)
	ka := &keepAlive{
		chs:   []chan<- *LeaseKeepAliveResponse{chA, chB, chC},
		ctxs:  []context.Context{kA, kB, kC},
		donec: make(chan struct{}),
	}
	l.keepAlives[1] = ka
	l.closeRequireLeader() // closes chA; ctxs becomes [kA, kB]
	cancelC()
	l.keepAliveCtxCloser(kC, 1, ka.donec) // finds no kC: closes nothing
	select {
	case _, ok := <-chC:
		if !ok {
			return
		}
	default:
	}
	t.Error("C's channel still open after C's context was cancelled")
}
