package clientv3

import (
	"sync"
	"testing"
	"time"

	"go.uber.org/zap"

	"go.etcd.io/etcd/client/v3/internal/resolver"
)

// Each case is a call that a names-only postulate of the pr-verify/etcd-21714 branch claims
// returns (no panic) for every client whose fields are merely read-only (clientDialAt,
// clientBuiltAt, epMu/resolver points-to), and which in fact panics.
func mustPanic(t *testing.T, name string, f func()) {
	t.Helper()
	defer func() {
		r := recover()
		if r == nil {
			t.Errorf("%s: no panic", name)
		} else {
			t.Logf("%s: panic: %v", name, r)
		}
	}()
	f()
}

func TestReviewPostulatesPanic(t *testing.T) {
	// Client.dialWithBalancer, clientDialAt c with epMu = nil (logger set, Token "").
	mustPanic(t, "dialWithBalancer/epMu nil", func() {
		c := &Client{}
		c.lg.Store(zap.NewNop())
		c.dialWithBalancer()
	})
	// Client.dialWithBalancer, clientDialAt c with no endpoints.
	mustPanic(t, "dialWithBalancer/no endpoints", func() {
		c := &Client{epMu: new(sync.RWMutex)}
		c.lg.Store(zap.NewNop())
		c.dialWithBalancer()
	})
	// Client.SetEndpoints with resolver ↦□ null (resolver.New's spec does not say non-null).
	mustPanic(t, "SetEndpoints/resolver nil", func() {
		c := &Client{epMu: new(sync.RWMutex)}
		c.SetEndpoints("127.0.0.1:2379")
	})
	// Client.SetEndpoints with epMu ↦□ null.
	mustPanic(t, "SetEndpoints/epMu nil", func() {
		c := &Client{resolver: resolver.New()}
		c.SetEndpoints("127.0.0.1:2379")
	})
	// EtcdManualResolver.Close of null (spec: for all r).
	mustPanic(t, "EtcdManualResolver.Close/nil", func() {
		var r *resolver.EtcdManualResolver
		r.Close()
	})
	// Client.Close of a clientBuiltAt client whose cancel/ctx are nil.
	mustPanic(t, "Close/cancel nil", func() {
		c := &Client{}
		c.lg.Store(zap.NewNop())
		c.Close()
	})
	// Client.autoSync of a clientBuiltAt client whose ctx is nil.
	mustPanic(t, "autoSync/ctx nil", func() {
		c := &Client{cfg: Config{AutoSyncInterval: time.Millisecond}}
		c.lg.Store(zap.NewNop())
		c.autoSync()
	})
	// Client.checkVersion of a clientBuiltAt client whose ctx is nil.
	mustPanic(t, "checkVersion/ctx nil", func() {
		c := &Client{epMu: new(sync.RWMutex)}
		c.lg.Store(zap.NewNop())
		c.checkVersion()
	})
}
