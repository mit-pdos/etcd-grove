package repro

import (
	"slices"
	"sync"
	"testing"
)

// Minimal faithful reproduction of clientv3.Client, NewCtxClient, SetEndpoints,
// Endpoints, and resolver.EtcdManualResolver before and after PR #22658.

type etcdManualResolver struct {
	endpoints []string
}

func (r *etcdManualResolver) SetEndpoints(eps ...string) {
	// Faithful to client/v3/internal/resolver/resolver.go:52-55:
	// dereferencing r.endpoints panics when r == nil.
	r.endpoints = eps
}

type client struct {
	epMu      *sync.RWMutex
	endpoints []string
	resolver  *etcdManualResolver
}

func newCtxClient() *client {
	return &client{
		epMu:     new(sync.RWMutex),
		resolver: nil,
	}
}

func (c *client) setEndpointsBeforePR22658(eps ...string) {
	c.epMu.Lock()
	defer c.epMu.Unlock()
	c.endpoints = eps

	c.resolver.SetEndpoints(eps...)
}

func (c *client) setEndpointsAfterPR22658(eps ...string) {
	c.epMu.Lock()
	defer c.epMu.Unlock()
	c.endpoints = eps

	if c.resolver != nil {
		c.resolver.SetEndpoints(eps...)
	}
}

func (c *client) Endpoints() []string {
	c.epMu.RLock()
	defer c.epMu.RUnlock()
	eps := make([]string, len(c.endpoints))
	copy(eps, c.endpoints)
	return eps
}

func TestBeforePR22658_SetEndpointsOnNewCtxClientPanics(t *testing.T) {
	c := newCtxClient()
	defer func() {
		r := recover()
		if r == nil {
			t.Fatal("expected setEndpointsBeforePR22658 on NewCtxClient to panic with nil pointer dereference")
		}
		t.Logf("Confirmed pre-PR #22658 panic on NewCtxClient.SetEndpoints: %v", r)
	}()
	c.setEndpointsBeforePR22658("http://254.0.0.1:12345")
}

func TestAfterPR22658_SetEndpointsOnNewCtxClientSucceeds(t *testing.T) {
	c := newCtxClient()
	c.setEndpointsAfterPR22658("http://254.0.0.1:12345")
	got := c.Endpoints()
	want := []string{"http://254.0.0.1:12345"}
	if !slices.Equal(got, want) {
		t.Fatalf("Endpoints() = %v, want %v", got, want)
	}
	t.Logf("Confirmed PR #22658 fix: NewCtxClient.SetEndpoints succeeded with resolver == nil; Endpoints() = %v", got)
}

func TestAfterPR22658_SetEndpointsWithNonNilResolverUpdatesBoth(t *testing.T) {
	c := &client{
		epMu:     new(sync.RWMutex),
		resolver: &etcdManualResolver{endpoints: []string{"http://127.0.0.1:2379"}},
	}
	want := []string{"http://127.0.0.1:2379", "http://127.0.0.2:2379"}
	c.setEndpointsAfterPR22658(want...)
	if !slices.Equal(c.Endpoints(), want) {
		t.Fatalf("c.Endpoints() = %v, want %v", c.Endpoints(), want)
	}
	if !slices.Equal(c.resolver.endpoints, want) {
		t.Fatalf("c.resolver.endpoints = %v, want %v", c.resolver.endpoints, want)
	}
	t.Logf("Confirmed PR #22658 preserves resolver update when resolver != nil: %v", c.resolver.endpoints)
}
