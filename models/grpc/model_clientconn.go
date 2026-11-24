/*
 *
 * Copyright 2026 the etcd-grove authors.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 */

package grpc

// MODEL: the ClientConn's connection management, in place of grpc-go's resolver wrapper
// (resolver_wrapper.go), balancer wrapper and balancers (balancer_wrapper.go, balancer/...),
// picker (picker_wrapper.go), subchannels and their transports (addrConn, clientconn.go) and
// idleness manager (internal/idle).
//
// The resolver is the program's (the builder of the target's scheme, as grpc-go chooses it), built
// when the ClientConn leaves idleness (at its first RPC, at Connect, at DialContext) and closed
// when it enters idleness or closes; the resolver wrapper (resolver.ClientConn) records every
// address the resolver reports, in Addresses or Endpoints, since it was built. An attempt (a
// csAttempt's getTransport) waits until there is one, picks any (modelChooseN: grpc-go's
// round_robin picks among the READY subchannels of the latest update, and a subchannel of an
// address since removed may still serve a pick), dials it through the dial options' dialer (else a
// net.Dialer), runs the transport credentials' client handshake, and gets a fresh connection of
// its own: one stream per connection (model_transport.go). A fail-fast attempt (WaitForReady
// false) fails with Unavailable when the dial fails, when the resolver reported an error and no
// address, or at the model's choice (a fail-fast RPC fails whenever grpc-go's picker is in
// TRANSIENT_FAILURE); a wait-for-ready attempt waits and dials again (with the dial options'
// backoff) until its context is done.
//
// Idleness: after the last active RPC ends, the ClientConn may enter idleness (the model's choice:
// grpc-go's idleness manager does after the idle timeout, 30 minutes by default), closing the
// resolver; the next RPC (or Connect) builds it again, as grpc-go's ExitIdleMode does. So the
// resolver's Build and Close interleave with RPCs as in grpc-go
// (issues/etcd-client-resolver-build-race.md stays reachable).

import (
	"context"
	"errors"
	internalbackoff "google.golang.org/grpc/internal/backoff"
	"net"
	"strings"
	"sync"
	"time"

	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/connectivity"
	"google.golang.org/grpc/credentials"
	"google.golang.org/grpc/internal/transport/networktype"
	"google.golang.org/grpc/resolver"
	"google.golang.org/grpc/serviceconfig"
	"google.golang.org/grpc/status"
)

// ccResolverWrapper is the resolver.ClientConn the ClientConn gives its resolver: what the
// resolver reported since it was built.
type ccResolverWrapper struct {
	cc       *ClientConn
	resolver resolver.Resolver // set once built (under cc.idleMu)

	mu     sync.Mutex
	closed bool
	addrs  []resolver.Address // every address reported since the build
	err    error              // the resolver's error, while it reported no address
	notify chan struct{}      // closed and replaced at each update
}

func newCCResolverWrapper(cc *ClientConn) *ccResolverWrapper {
	return &ccResolverWrapper{cc: cc, notify: make(chan struct{})}
}

// update records an update's addresses (or the resolver's error) and wakes the waiting attempts.
func (ccr *ccResolverWrapper) update(addrs []resolver.Address, err error) {
	ccr.mu.Lock()
	defer ccr.mu.Unlock()
	if ccr.closed {
		return
	}
	for _, a := range addrs {
		known := false
		for _, b := range ccr.addrs {
			if a.Equal(b) {
				known = true
			}
		}
		if !known {
			ccr.addrs = append(ccr.addrs, a)
		}
	}
	if len(ccr.addrs) == 0 {
		ccr.err = err
	} else {
		ccr.err = nil
	}
	close(ccr.notify)
	ccr.notify = make(chan struct{})
}

// UpdateState is resolver.ClientConn.UpdateState: the state's addresses, in Addresses and in
// Endpoints, are recorded. A service config is checked to be the model's (parseServiceConfig's
// result); it changes nothing.
func (ccr *ccResolverWrapper) UpdateState(s resolver.State) error {
	if s.ServiceConfig != nil {
		if s.ServiceConfig.Err != nil {
			stuck() // MODEL: not modelled (stuck): grpc: a resolver's service config error
		}
		if _, ok := s.ServiceConfig.Config.(*ServiceConfig); !ok {
			stuck() // MODEL: not modelled (stuck): grpc: a service config not parsed by the ClientConn
		}
	}
	addrs := append([]resolver.Address(nil), s.Addresses...)
	for _, ep := range s.Endpoints {
		addrs = append(addrs, ep.Addresses...)
	}
	var err error
	if len(addrs) == 0 {
		// round_robin's response to an update without addresses (UpdateClientConnState).
		err = errors.New("produced zero addresses")
	}
	ccr.update(addrs, err)
	return nil
}

// ReportError is resolver.ClientConn.ReportError.
func (ccr *ccResolverWrapper) ReportError(err error) {
	ccr.update(nil, err)
}

// NewAddress is resolver.ClientConn.NewAddress.
func (ccr *ccResolverWrapper) NewAddress(addrs []resolver.Address) {
	ccr.update(addrs, errors.New("produced zero addresses"))
}

// ParseServiceConfig is resolver.ClientConn.ParseServiceConfig.
func (ccr *ccResolverWrapper) ParseServiceConfig(scJSON string) *serviceconfig.ParseResult {
	return parseServiceConfig(scJSON, ccr.cc.dopts.maxCallAttempts)
}

// resolveNow asks the resolver to resolve again (ccResolverWrapper.resolveNow), as grpc-go does
// when a connection attempt fails.
func (ccr *ccResolverWrapper) resolveNow() {
	ccr.cc.idleMu.Lock()
	r := ccr.resolver
	ccr.mu.Lock()
	closed := ccr.closed
	ccr.mu.Unlock()
	if r != nil && !closed {
		r.ResolveNow(resolver.ResolveNowOptions{})
	}
	ccr.cc.idleMu.Unlock()
}

// exitIdleMode builds the resolver if the ClientConn is idle (ClientConn.exitIdleMode, with the
// resolver wrapper's start). The resolver's Build may call the wrapper back.
func (cc *ClientConn) exitIdleMode() error {
	cc.idleMu.Lock()
	defer cc.idleMu.Unlock()
	cc.mu.Lock()
	if cc.streams == nil {
		cc.mu.Unlock()
		return errConnClosing
	}
	if !cc.idle {
		cc.mu.Unlock()
		return nil
	}
	cc.idle = false
	ccr := newCCResolverWrapper(cc)
	cc.resolverWrapper = ccr
	cc.mu.Unlock()

	// Set state to CONNECTING before building the name resolver
	// so the channel does not remain in IDLE.
	cc.csMgr.updateState(connectivity.Connecting)

	opts := resolver.BuildOptions{
		DisableServiceConfig: cc.dopts.disableServiceConfig,
		DialCreds:            cc.dopts.copts.TransportCredentials,
		CredsBundle:          cc.dopts.copts.CredsBundle,
		Dialer:               cc.dopts.copts.Dialer,
		Authority:            cc.authority,
	}
	r, err := cc.resolverBuilder.Build(cc.parsedTarget, ccr, opts)
	if err != nil {
		// As grpc-go: an error reported by the resolver before any valid update.
		cc.csMgr.updateState(connectivity.TransientFailure)
		ccr.update(nil, err)
		return errors.New("failed to start resolver: " + err.Error())
	}
	ccr.resolver = r
	return nil
}

// enterIdleMode closes the resolver (ClientConn.enterIdleMode); the next RPC builds a new one.
func (cc *ClientConn) enterIdleMode() {
	cc.idleMu.Lock()
	defer cc.idleMu.Unlock()
	cc.mu.Lock()
	if cc.streams == nil || cc.idle || cc.activeCalls != 0 {
		cc.mu.Unlock()
		return
	}
	cc.idle = true
	ccr := cc.resolverWrapper
	cc.resolverWrapper = nil
	cc.mu.Unlock()
	cc.csMgr.updateState(connectivity.Idle)
	ccr.close()
}

// close closes the resolver (ccResolverWrapper.close); called under cc.idleMu.
func (ccr *ccResolverWrapper) close() {
	if ccr == nil {
		return
	}
	ccr.mu.Lock()
	ccr.closed = true
	close(ccr.notify)
	ccr.notify = make(chan struct{})
	ccr.mu.Unlock()
	if ccr.resolver != nil {
		ccr.resolver.Close()
		ccr.resolver = nil
	}
}

// onCallBegin tracks an RPC's start (idle.Manager.OnCallBegin): the ClientConn leaves idleness.
func (cc *ClientConn) onCallBegin() error {
	cc.mu.Lock()
	if cc.streams == nil {
		cc.mu.Unlock()
		return ErrClientConnClosing
	}
	cc.activeCalls++
	cc.mu.Unlock()
	if err := cc.exitIdleMode(); err != nil && err == errConnClosing {
		return ErrClientConnClosing
	}
	return nil
}

// onCallEnd tracks an RPC's end (idle.Manager.OnCallEnd): when none is left, the ClientConn may
// enter idleness (the model's choice).
func (cc *ClientConn) onCallEnd() {
	cc.mu.Lock()
	cc.activeCalls--
	quiet := cc.activeCalls == 0
	cc.mu.Unlock()
	if quiet && modelChoose() {
		cc.enterIdleMode()
	}
}

// addStream registers an attempt's stream, whose connection Close closes; false if the
// ClientConn is closed.
func (cc *ClientConn) addStream(s *clientTransportStream) bool {
	cc.mu.Lock()
	defer cc.mu.Unlock()
	if cc.streams == nil {
		return false
	}
	cc.streams[s] = struct{}{}
	return true
}

func (cc *ClientConn) removeStream(s *clientTransportStream) {
	cc.mu.Lock()
	if cc.streams != nil {
		delete(cc.streams, s)
	}
	cc.mu.Unlock()
}

// getTransportConn is an attempt's pick and connection (pickerWrapper.pick, with the subchannel's
// connection attempt, addrConn.createTransport and NewHTTP2Client's dial and handshake).
func (cc *ClientConn) getTransportConn(ctx context.Context, failFast bool) (net.Conn, credentials.AuthInfo, error) {
	retries := 0
	for {
		cc.mu.Lock()
		closed := cc.streams == nil
		ccr := cc.resolverWrapper
		cc.mu.Unlock()
		if closed {
			return nil, nil, ErrClientConnClosing
		}
		if ccr == nil {
			// Idle (entered between this RPC's start and now, impossible while it is active).
			if err := cc.exitIdleMode(); err == errConnClosing {
				return nil, nil, ErrClientConnClosing
			}
			continue
		}
		ccr.mu.Lock()
		addrs := ccr.addrs
		rerr := ccr.err
		notify := ccr.notify
		rclosed := ccr.closed
		ccr.mu.Unlock()
		if rclosed {
			continue
		}
		if len(addrs) == 0 {
			if failFast && rerr != nil {
				return nil, nil, status.Errorf(codes.Unavailable, "name resolver error: %v", rerr)
			}
			select {
			case <-notify:
				continue
			case <-ctx.Done():
				return nil, nil, status.FromContextError(ctx.Err()).Err()
			case <-cc.ctx.Done():
				return nil, nil, ErrClientConnClosing
			}
		}
		if failFast && modelChoose() {
			// grpc-go's picker in TRANSIENT_FAILURE (every subchannel's last attempt failed).
			return nil, nil, status.Error(codes.Unavailable, "connection error: desc = \"transport: Error while dialing\"")
		}
		addr := addrs[modelChooseAddr(&cc.picks, addrs)]
		// The connection attempt is the subchannel's, not the RPC's: the RPC stops waiting for it
		// when its context is done (the connection, if made, is then closed: no later RPC is
		// sent on it, as none of this attempt's was).
		ch := make(chan dialResult, 1)
		go func() {
			done := modelNoteDial(&cc.picks, addr.Addr)
			conn, authInfo, err := cc.dialAddr(addr)
			done(err == nil)
			ch <- dialResult{conn, authInfo, err}
		}()
		var r dialResult
		select {
		case r = <-ch:
		case <-ctx.Done():
			go abandonDial(ch)
			return nil, nil, status.FromContextError(ctx.Err()).Err()
		case <-cc.ctx.Done():
			go abandonDial(ch)
			return nil, nil, ErrClientConnClosing
		}
		conn, authInfo, err := r.conn, r.authInfo, r.err
		if err == nil {
			cc.csMgr.updateState(connectivity.Ready)
			return conn, authInfo, nil
		}
		cc.updateConnectionError(err)
		cc.csMgr.updateState(connectivity.TransientFailure)
		ccr.resolveNow()
		if failFast {
			return nil, nil, status.Error(codes.Unavailable, err.Error())
		}
		t := time.NewTimer(internalbackoff.DefaultExponential.Backoff(retries)) // MODEL: dialOptions has no bs
		retries++
		select {
		case <-t.C:
		case <-ctx.Done():
			t.Stop()
			return nil, nil, status.FromContextError(ctx.Err()).Err()
		case <-cc.ctx.Done():
			t.Stop()
			return nil, nil, ErrClientConnClosing
		}
	}
}

// dialResult is a connection attempt's outcome.
type dialResult struct {
	conn     net.Conn
	authInfo credentials.AuthInfo
	err      error
}

// abandonDial closes the connection of an attempt nobody waits for any more.
func abandonDial(ch chan dialResult) {
	if r := <-ch; r.conn != nil {
		r.conn.Close()
	}
}

// dialAddr connects to addr (transport's dial and NewHTTP2Client's handshake): through the dial
// options' dialer, else a net.Dialer; then the transport credentials' client handshake, which the
// model supports only for insecure credentials; then the client's preface out and the server's
// in (HTTP/2's SETTINGS: grpc-go uses a connection only once the server's preface arrived, within
// the connect deadline), so that no stream is ever written on a connection the server has not
// accepted as gRPC.
func (cc *ClientConn) dialAddr(addr resolver.Address) (net.Conn, credentials.AuthInfo, error) {
	connectCtx, cancel := context.WithTimeout(cc.ctx, minConnectTimeout)
	defer cancel()
	address := addr.Addr
	networkType, ok := networktype.Get(addr)
	var conn net.Conn
	var err error
	if fn := cc.dopts.copts.Dialer; fn != nil {
		if networkType == "unix" && !strings.HasPrefix(address, "\x00") {
			stuck() // MODEL: not modelled (stuck): grpc: a unix address with a custom dialer
		}
		conn, err = fn(connectCtx, address)
	} else {
		if !ok {
			networkType = "tcp"
		}
		conn, err = (&net.Dialer{}).DialContext(connectCtx, networkType, address)
	}
	if err != nil {
		return nil, nil, connectionError{Desc: "transport: Error while dialing: " + err.Error()}
	}
	creds := cc.dopts.copts.TransportCredentials
	if creds == nil && cc.dopts.copts.CredsBundle != nil {
		creds = cc.dopts.copts.CredsBundle.TransportCredentials()
	}
	if creds.Info().SecurityProtocol != "insecure" {
		stuck() // MODEL: not modelled (stuck): grpc: transport credentials other than insecure
	}
	addr.ServerName = cc.getServerName(addr)
	conn, authInfo, err := creds.ClientHandshake(connectCtx, addr.ServerName, conn)
	if err != nil {
		conn.Close()
		return nil, nil, connectionError{Desc: "transport: authentication handshake failed: " + err.Error()}
	}
	if _, err := conn.Write([]byte(clientPreface)); err != nil {
		conn.Close()
		return nil, nil, connectionError{Desc: "transport: failed to write client preface: " + err.Error()}
	}
	dl, _ := connectCtx.Deadline()
	conn.SetReadDeadline(dl)
	kind, err := readFrameKind(conn)
	if err == nil && kind != frameSettings {
		err = errMalformedFrame
	}
	if err != nil {
		conn.Close()
		return nil, nil, connectionError{Desc: "error reading server preface: " + err.Error()}
	}
	conn.SetReadDeadline(time.Time{})
	return conn, authInfo, nil
}
