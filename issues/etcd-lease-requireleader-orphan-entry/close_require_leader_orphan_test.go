// Reproduction of issues/etcd-lease-requireleader-orphan-entry.md.
//
// Package clientv3, file client/v3/close_require_leader_orphan_test.go of go.etcd.io/etcd
// (module go.etcd.io/etcd/client/v3), at the etcd pin of etc/goose.py: 107edf7e4 (branch
// goose-lean of upamanyus/etcd).
//
// Run, in client/v3:
//
//	GOTOOLCHAIN=go1.27.1 go test . -run '^TestCloseRequireLeaderOrphanEntry$' -count=1
//
// Fails at the pin (shows the bug): "entry kept with 0 subscribers".
package clientv3

import (
	"context"
	"testing"
	"time"
)

func TestCloseRequireLeaderOrphanEntry(t *testing.T) {
	l := &lessor{keepAlives: make(map[LeaseID]*keepAlive), donec: make(chan struct{})}
	l.keepAlives[1] = &keepAlive{
		chs:           []chan<- *LeaseKeepAliveResponse{make(chan *LeaseKeepAliveResponse, 1)},
		ctxs:          []context.Context{WithRequireLeader(context.Background())},
		nextKeepAlive: time.Now(),
		donec:         make(chan struct{}),
	}
	l.closeRequireLeader()
	if ka, ok := l.keepAlives[1]; ok {
		t.Errorf("entry kept with %d subscribers", len(ka.chs))
	}
}
