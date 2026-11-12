// Package concurrency holds the requirement snippets of etcd's client/v3/concurrency package
// (batch 1d, SpecPlan/Spec/go_etcd_io/etcd/client/v3/concurrency/): sessions, mutexes, elections and the
// STM as their users (v3lock, v3election, leasing, the grpc proxy, recipes, etcd's tests) rely on
// them, each reliance an explicit panic.
//
// Common assumptions (the proofs' setting): cli is a client of a cluster (isClient), the caller
// owns the cluster's state in an invariant and hands each call the permission etcdPerm for the
// transitions the call states (its invariant is stable under them); contexts carry no auth
// metadata of their own (ctxPrin). Time is not modelled: a lease may expire at any moment, so
// nothing here relies on a lease being alive.
package concurrency

import (
	"context"

	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/client/v3/concurrency"
)

// REQ concurrency/session-lease: a new session's lease was granted (a non-zero id), its client is
// the one given, and a key may be put with the lease.
// Users: server/proxy/grpcproxy/register.go:65,76 (endpoint key on ss.Lease()), recipes/key.go:142.
// Assumes: none (the put may fail with ErrLeaseNotFound: the lease may already have expired).
// Specs: NewSession.spec, WithTTL.spec, Session.Lease.spec, Session.Client.spec, Client.Put.spec.
func ReqSessionLease(ctx context.Context, cli *clientv3.Client, k string) {
	s, err := concurrency.NewSession(cli, concurrency.WithTTL(10))
	if err != nil {
		return
	}
	if s.Client() != cli {
		panic("session: another client")
	}
	if s.Lease() == clientv3.NoLease {
		panic("session: granted lease 0")
	}
	if _, err := cli.Put(ctx, k, "", clientv3.WithLease(s.Lease())); err != nil {
		return
	}
}

// REQ concurrency/session-resume: a session over a lease the caller names keeps that id, and
// Orphan returns (v3lock's and v3election's pattern: the remote client keeps the lease alive).
// Users: server/etcdserver/api/v3lock/lock.go:36-44, v3election/election.go:126-134.
// Assumes: none (the lease may not exist: the session is made anyway).
// Specs: NewSession.spec, WithLease.spec, WithContext.spec, Session.Orphan.spec,
// Session.Lease.spec.
func ReqSessionResumeLease(ctx context.Context, cli *clientv3.Client, id clientv3.LeaseID) {
	if id == clientv3.NoLease {
		return
	}
	s, err := concurrency.NewSession(cli, concurrency.WithLease(id), concurrency.WithContext(ctx))
	if err != nil {
		return
	}
	s.Orphan()
	if s.Lease() != id {
		panic("session: lease not the one named")
	}
}

// REQ concurrency/session-done: Done may be waited on in a select (leasing's monitor, the grpc
// proxy's re-registration); a receive from it never yields a value.
// Users: client/leasing/kv.go:133,484, server/proxy/grpcproxy/register.go:53.
// Assumes: none.
// Specs: NewSession.spec, Session.Done.spec (Perennial's broadcast channel), Context.Done.spec,
// Context.doneRecv.spec, Session.Close.spec.
func ReqSessionDone(ctx context.Context, cli *clientv3.Client) {
	s, err := concurrency.NewSession(cli)
	if err != nil {
		return
	}
	select {
	case _, ok := <-s.Done():
		if ok {
			panic("session: Done carried a value")
		}
	case <-ctx.Done():
	}
	_ = s.Close()
}

// REQ concurrency/session-close: Close returns (revoking the lease; any error is the caller's to
// ignore, as the grpc proxy does).
// Users: server/proxy/grpcproxy/register.go:50,72,77.
// Assumes: none.
// Specs: NewSession.spec, Session.Close.spec.
func ReqSessionClose(cli *clientv3.Client) {
	s, err := concurrency.NewSession(cli)
	if err != nil {
		return
	}
	_ = s.Close()
}

// REQ concurrency/session-ttl: WithTTL with any TTL, a non-positive one ignored (logged), not a
// panic.
// Users: server/proxy/grpcproxy/register.go:65 (a configured TTL).
// Assumes: none.
// Specs: WithTTL.spec, NewSession.spec.
func ReqSessionTTL(cli *clientv3.Client, ttl int) {
	s, err := concurrency.NewSession(cli, concurrency.WithTTL(ttl))
	if err != nil {
		return
	}
	s.Orphan()
}

// REQ concurrency/session-loop: sessions made again and again, each awaited with Done (leasing's
// monitor, the grpc proxy's re-registration): nothing once-only per session.
// Users: client/leasing/kv.go:129-157 (monitorSession), server/proxy/grpcproxy/register.go:42-58.
// Assumes: none.
// Specs: NewSession.spec, Session.Done.spec, Session.Close.spec.
func ReqSessionLoop(ctx context.Context, cli *clientv3.Client) {
	for ctx.Err() == nil {
		s, err := concurrency.NewSession(cli)
		if err != nil {
			continue
		}
		select {
		case <-s.Done():
		case <-ctx.Done():
			_ = s.Close()
			return
		}
	}
}
