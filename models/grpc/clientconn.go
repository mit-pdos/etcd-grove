/*
 *
 * Copyright 2014 gRPC authors.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *
 */

package grpc

import (
	"context"
	"errors"
	"fmt"
	"math"
	"net/url"
	"strings"
	"sync"
	"time"

	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/connectivity"
	"google.golang.org/grpc/internal"
	"google.golang.org/grpc/keepalive"
	"google.golang.org/grpc/resolver"
	"google.golang.org/grpc/status"

	_ "google.golang.org/grpc/internal/resolver/passthrough" // To register passthrough resolver.
	_ "google.golang.org/grpc/internal/resolver/unix"        // To register unix resolver.
	_ "google.golang.org/grpc/resolver/dns"                  // To register dns resolver.
)

// MODEL: this file is grpc-go's clientconn.go with the balancer, the subchannels (addrConn), the
// picker, channelz, the metrics and the service config's application removed; what replaces them
// is in model_clientconn.go (the resolver wrapper, idleness, an attempt's connection). Kept as
// grpc-go's: the error values, NewClient's option handling, target parsing and authority, Dial
// and DialContext, the credentials' validation, the interceptor chaining, the connectivity state
// manager, Target, CanonicalTarget, GetMethodConfig. The round_robin balancer is no longer
// registered (the model has no balancer).

const (
	// minimum time to give a connection to complete
	minConnectTimeout = 20 * time.Second
)

var (
	// ErrClientConnClosing indicates that the operation is illegal because
	// the ClientConn is closing.
	//
	// Deprecated: this error should not be relied upon by users; use the status
	// code of Canceled instead.
	ErrClientConnClosing = status.Error(codes.Canceled, "grpc: the client connection is closing")
	// errConnDrain indicates that the connection starts to be drained and does not accept any new RPCs.
	errConnDrain = errors.New("grpc: the connection is drained")
	// errConnClosing indicates that the connection is closing.
	errConnClosing = errors.New("grpc: the connection is closing")
	// errConnIdling indicates the connection is being closed as the channel
	// is moving to an idle mode due to inactivity.
	errConnIdling = errors.New("grpc: the connection is closing due to channel idleness")
	// invalidDefaultServiceConfigErrPrefix is used to prefix the json parsing error for the default
	// service config.
	invalidDefaultServiceConfigErrPrefix = "grpc: the provided default service config is invalid"
	// PickFirstBalancerName is the name of the pick_first balancer.
	PickFirstBalancerName = "pick_first" // MODEL: pickfirst.Name (the balancer packages are not imported)
)

// The following errors are returned from Dial and DialContext
var (
	// errNoTransportSecurity indicates that there is no transport security
	// being set for ClientConn. Users should either set one or explicitly
	// call WithInsecure DialOption to disable security.
	errNoTransportSecurity = errors.New("grpc: no transport security set (use grpc.WithTransportCredentials(insecure.NewCredentials()) explicitly or set credentials)")
	// errTransportCredsAndBundle indicates that creds bundle is used together
	// with other individual Transport Credentials.
	errTransportCredsAndBundle = errors.New("grpc: credentials.Bundle may not be used with individual TransportCredentials")
	// errNoTransportCredsInBundle indicated that the configured creds bundle
	// returned a transport credentials which was nil.
	errNoTransportCredsInBundle = errors.New("grpc: credentials.Bundle must return non-nil transport credentials")
	// errTransportCredentialsMissing indicates that users want to transmit
	// security information (e.g., OAuth2 token) which requires secure
	// connection on an insecure connection.
	errTransportCredentialsMissing = errors.New("grpc: the credentials require transport level security (use grpc.WithTransportCredentials() to set)")
)

const (
	defaultClientMaxReceiveMessageSize = 1024 * 1024 * 4
	defaultClientMaxSendMessageSize    = math.MaxInt32
	// http2IOBufSize specifies the buffer size for sending frames.
	defaultWriteBufSize = 32 * 1024
	defaultReadBufSize  = 32 * 1024
)

// NewClient creates a new gRPC "channel" for the target URI provided.  No I/O
// is performed.  Use of the ClientConn for RPCs will automatically cause it to
// connect.  The Connect method may be called to manually create a connection,
// but for most users this should be unnecessary.
//
// The target name syntax is defined in
// https://github.com/grpc/grpc/blob/master/doc/naming.md.  E.g. to use the dns
// name resolver, a "dns:///" prefix may be applied to the target.  The default
// name resolver will be used if no scheme is detected, or if the parsed scheme
// is not a registered name resolver.  The default resolver is "dns" but can be
// overridden using the resolver package's SetDefaultScheme.
//
// The DialOptions returned by WithBlock, WithTimeout,
// WithReturnConnectionError, and FailOnNonTempDialError are ignored by this
// function.
//
// MODEL: grpc-go's NewClient, without channelz, the balancer, the picker and the idleness manager
// (model_clientconn.go). Outside the model (stuck): stats handlers, binary logging, a
// compressor or decompressor, a default service config other than round robin's.
func NewClient(target string, opts ...DialOption) (conn *ClientConn, err error) {
	cc := &ClientConn{
		target:  target,
		streams: make(map[*clientTransportStream]struct{}),
		dopts:   defaultDialOptions(),
		idle:    true,
	}

	cc.ctx, cc.cancel = context.WithCancel(context.Background())

	// Apply dial options.
	disableGlobalOpts := false
	for _, opt := range opts {
		if _, ok := opt.(*disableGlobalDialOptions); ok {
			disableGlobalOpts = true
			break
		}
	}

	if !disableGlobalOpts {
		for _, opt := range globalDialOptions {
			opt.apply(&cc.dopts)
		}
	}

	for _, opt := range opts {
		opt.apply(&cc.dopts)
	}

	// Determine the resolver to use.
	if err := cc.initParsedTargetAndResolverBuilder(); err != nil {
		return nil, err
	}

	for _, opt := range globalPerTargetDialOptions {
		opt.DialOptionForTarget(cc.parsedTarget.URL).apply(&cc.dopts)
	}

	chainUnaryClientInterceptors(cc)
	chainStreamClientInterceptors(cc)

	if err := cc.validateTransportCredentials(); err != nil {
		return nil, err
	}

	if cc.dopts.defaultServiceConfigRawJSON != nil {
		scpr := parseServiceConfig(*cc.dopts.defaultServiceConfigRawJSON, cc.dopts.maxCallAttempts)
		if scpr.Err != nil {
			return nil, fmt.Errorf("%s: %v", invalidDefaultServiceConfigErrPrefix, scpr.Err)
		}
		cc.dopts.defaultServiceConfig, _ = scpr.Config.(*ServiceConfig)
	}
	cc.keepaliveParams = cc.dopts.copts.KeepaliveParams

	if err = cc.initAuthority(); err != nil {
		return nil, err
	}

	if len(cc.dopts.copts.StatsHandlers) != 0 {
		stuck() // MODEL: not modelled (stuck): grpc: stats handlers
	}
	if cc.dopts.compressorV0 != nil || cc.dopts.dc != nil {
		stuck() // MODEL: not modelled (stuck): grpc: compression
	}

	cc.csMgr = newConnectivityStateManager(cc.ctx)

	return cc, nil
}

// Dial calls DialContext(context.Background(), target, opts...).
//
// Deprecated: use NewClient instead.  Will be supported throughout 1.x.
func Dial(target string, opts ...DialOption) (*ClientConn, error) {
	return DialContext(context.Background(), target, opts...)
}

// DialContext calls NewClient and then exits idle mode.  If WithBlock(true) is
// used, it calls Connect and WaitForStateChange until either the context
// expires or the state of the ClientConn is Ready.
//
// One subtle difference between NewClient and Dial and DialContext is that the
// former uses "dns" as the default name resolver, while the latter use
// "passthrough" for backward compatibility.  This distinction should not matter
// to most users, but could matter to legacy users that specify a custom dialer
// and expect it to receive the target string directly.
//
// Deprecated: use NewClient instead.  Will be supported throughout 1.x.
func DialContext(ctx context.Context, target string, opts ...DialOption) (conn *ClientConn, err error) {
	// At the end of this method, we kick the channel out of idle, rather than
	// waiting for the first rpc.
	//
	// WithLocalDNSResolution dial option in `grpc.Dial` ensures that it
	// preserves behavior: when default scheme passthrough is used, skip
	// hostname resolution, when "dns" is used for resolution, perform
	// resolution on the client.
	opts = append([]DialOption{withDefaultScheme("passthrough"), WithLocalDNSResolution()}, opts...)
	cc, err := NewClient(target, opts...)
	if err != nil {
		return nil, err
	}

	// We start the channel off in idle mode, but kick it out of idle now,
	// instead of waiting for the first RPC.  This is the legacy behavior of
	// Dial.
	defer func() {
		if err != nil {
			cc.Close()
		}
	}()

	// This creates the name resolver, load balancer, etc.
	if err := cc.exitIdleMode(); err != nil {
		return nil, fmt.Errorf("failed to exit idle mode: %w", err)
	}

	// Return now for non-blocking dials.
	if !cc.dopts.block {
		return cc, nil
	}

	if cc.dopts.timeout > 0 {
		var cancel context.CancelFunc
		ctx, cancel = context.WithTimeout(ctx, cc.dopts.timeout)
		defer cancel()
	}
	defer func() {
		select {
		case <-ctx.Done():
			switch {
			case ctx.Err() == err:
				conn = nil
			case err == nil || !cc.dopts.returnLastError:
				conn, err = nil, ctx.Err()
			default:
				conn, err = nil, fmt.Errorf("%v: %v", ctx.Err(), err)
			}
		default:
		}
	}()

	// A blocking dial blocks until the clientConn is ready.
	for {
		s := cc.GetState()
		if s == connectivity.Idle {
			cc.Connect()
		}
		if s == connectivity.Ready {
			return cc, nil
		} else if cc.dopts.copts.FailOnNonTempDialError && s == connectivity.TransientFailure {
			if err = cc.connectionError(); err != nil {
				terr, ok := err.(interface {
					Temporary() bool
				})
				if ok && !terr.Temporary() {
					return nil, err
				}
			}
		}
		if !cc.WaitForStateChange(ctx, s) {
			// ctx got timeout or canceled.
			if err = cc.connectionError(); err != nil && cc.dopts.returnLastError {
				return nil, err
			}
			return nil, ctx.Err()
		}
	}
}

// validateTransportCredentials performs a series of checks on the configured
// transport credentials. It returns a non-nil error if any of these conditions
// are met:
//   - no transport creds and no creds bundle is configured
//   - both transport creds and creds bundle are configured
//   - creds bundle is configured, but it lacks a transport credentials
//   - insecure transport creds configured alongside call creds that require
//     transport level security
//
// If none of the above conditions are met, the configured credentials are
// deemed valid and a nil error is returned.
func (cc *ClientConn) validateTransportCredentials() error {
	if cc.dopts.copts.TransportCredentials == nil && cc.dopts.copts.CredsBundle == nil {
		return errNoTransportSecurity
	}
	if cc.dopts.copts.TransportCredentials != nil && cc.dopts.copts.CredsBundle != nil {
		return errTransportCredsAndBundle
	}
	if cc.dopts.copts.CredsBundle != nil && cc.dopts.copts.CredsBundle.TransportCredentials() == nil {
		return errNoTransportCredsInBundle
	}
	transportCreds := cc.dopts.copts.TransportCredentials
	if transportCreds == nil {
		transportCreds = cc.dopts.copts.CredsBundle.TransportCredentials()
	}
	if transportCreds.Info().SecurityProtocol == "insecure" {
		for _, cd := range cc.dopts.copts.PerRPCCredentials {
			if cd.RequireTransportSecurity() {
				return errTransportCredentialsMissing
			}
		}
	}
	return nil
}

// chainUnaryClientInterceptors chains all unary client interceptors into one.
func chainUnaryClientInterceptors(cc *ClientConn) {
	interceptors := cc.dopts.chainUnaryInts
	// Prepend dopts.unaryInt to the chaining interceptors if it exists, since unaryInt will
	// be executed before any other chained interceptors.
	if cc.dopts.unaryInt != nil {
		interceptors = append([]UnaryClientInterceptor{cc.dopts.unaryInt}, interceptors...)
	}
	var chainedInt UnaryClientInterceptor
	if len(interceptors) == 0 {
		chainedInt = nil
	} else if len(interceptors) == 1 {
		chainedInt = interceptors[0]
	} else {
		chainedInt = func(ctx context.Context, method string, req, reply any, cc *ClientConn, invoker UnaryInvoker, opts ...CallOption) error {
			return interceptors[0](ctx, method, req, reply, cc, getChainUnaryInvoker(interceptors, 0, invoker), opts...)
		}
	}
	cc.dopts.unaryInt = chainedInt
}

// getChainUnaryInvoker recursively generate the chained unary invoker.
func getChainUnaryInvoker(interceptors []UnaryClientInterceptor, curr int, finalInvoker UnaryInvoker) UnaryInvoker {
	if curr == len(interceptors)-1 {
		return finalInvoker
	}
	return func(ctx context.Context, method string, req, reply any, cc *ClientConn, opts ...CallOption) error {
		return interceptors[curr+1](ctx, method, req, reply, cc, getChainUnaryInvoker(interceptors, curr+1, finalInvoker), opts...)
	}
}

// chainStreamClientInterceptors chains all stream client interceptors into one.
func chainStreamClientInterceptors(cc *ClientConn) {
	interceptors := cc.dopts.chainStreamInts
	// Prepend dopts.streamInt to the chaining interceptors if it exists, since streamInt will
	// be executed before any other chained interceptors.
	if cc.dopts.streamInt != nil {
		interceptors = append([]StreamClientInterceptor{cc.dopts.streamInt}, interceptors...)
	}
	interceptors = append(interceptors, defaultStreamInterceptor)
	var chainedInt StreamClientInterceptor
	if len(interceptors) == 0 {
		chainedInt = nil
	} else if len(interceptors) == 1 {
		chainedInt = interceptors[0]
	} else {
		chainedInt = func(ctx context.Context, desc *StreamDesc, cc *ClientConn, method string, streamer Streamer, opts ...CallOption) (ClientStream, error) {
			return interceptors[0](ctx, desc, cc, method, getChainStreamer(interceptors, 0, streamer), opts...)
		}
	}
	cc.dopts.streamInt = chainedInt
}

// getChainStreamer recursively generate the chained client stream constructor.
func getChainStreamer(interceptors []StreamClientInterceptor, curr int, finalStreamer Streamer) Streamer {
	if curr == len(interceptors)-1 {
		return finalStreamer
	}
	return func(ctx context.Context, desc *StreamDesc, cc *ClientConn, method string, opts ...CallOption) (ClientStream, error) {
		return interceptors[curr+1](ctx, desc, cc, method, getChainStreamer(interceptors, curr+1, finalStreamer), opts...)
	}
}

// newConnectivityStateManager creates an connectivityStateManager with
// the specified channel.
//
// MODEL: without channelz and the state's publication to subscribers (internal, for tests).
func newConnectivityStateManager(ctx context.Context) *connectivityStateManager {
	return &connectivityStateManager{}
}

// connectivityStateManager keeps the connectivity.State of ClientConn.
// This struct will eventually be exported so the balancers can access it.
//
// TODO: If possible, get rid of the `connectivityStateManager` type, and
// provide this functionality using the `PubSub`, to avoid keeping track of
// the connectivity state at two places.
type connectivityStateManager struct {
	mu         sync.Mutex
	state      connectivity.State
	notifyChan chan struct{}
}

// updateState updates the connectivity.State of ClientConn.
// If there's a change it notifies goroutines waiting on state change to
// happen.
func (csm *connectivityStateManager) updateState(state connectivity.State) {
	csm.mu.Lock()
	defer csm.mu.Unlock()
	if csm.state == connectivity.Shutdown {
		return
	}
	if csm.state == state {
		return
	}
	csm.state = state
	if csm.notifyChan != nil {
		// There are other goroutines waiting on this channel.
		close(csm.notifyChan)
		csm.notifyChan = nil
	}
}

func (csm *connectivityStateManager) getState() connectivity.State {
	csm.mu.Lock()
	defer csm.mu.Unlock()
	return csm.state
}

func (csm *connectivityStateManager) getNotifyChan() <-chan struct{} {
	csm.mu.Lock()
	defer csm.mu.Unlock()
	if csm.notifyChan == nil {
		csm.notifyChan = make(chan struct{})
	}
	return csm.notifyChan
}

// ClientConnInterface defines the functions clients need to perform unary and
// streaming RPCs.  It is implemented by *ClientConn, and is only intended to
// be referenced by generated code.
type ClientConnInterface interface {
	// Invoke performs a unary RPC and returns after the response is received
	// into reply.
	Invoke(ctx context.Context, method string, args any, reply any, opts ...CallOption) error
	// NewStream begins a streaming RPC.
	NewStream(ctx context.Context, desc *StreamDesc, method string, opts ...CallOption) (ClientStream, error)
}

// Assert *ClientConn implements ClientConnInterface.
var _ ClientConnInterface = (*ClientConn)(nil)

// ClientConn represents a virtual connection to a conceptual endpoint, to
// perform RPCs.
//
// A ClientConn is free to have zero or more actual connections to the endpoint
// based on configuration, load, etc. It is also free to determine which actual
// endpoints to use and may change it every RPC, permitting client-side load
// balancing.
//
// A ClientConn encapsulates a range of functionality including name
// resolution, TCP connection establishment (with retries and backoff) and TLS
// handshakes. It also handles errors on established connections by
// re-resolving the name and reconnecting.
//
// MODEL: the model's ClientConn (model_clientconn.go): no balancer, subchannels or picker; an
// attempt dials a connection of its own.
type ClientConn struct {
	ctx    context.Context    // Initialized using the background context at dial time.
	cancel context.CancelFunc // Cancelled on close.

	// The following are initialized at dial time, and are read-only after that.
	target          string           // User's dial target.
	parsedTarget    resolver.Target  // See initParsedTargetAndResolverBuilder().
	authority       string           // See initAuthority().
	dopts           dialOptions      // Default and user specified dial options.
	resolverBuilder resolver.Builder // See initParsedTargetAndResolverBuilder().

	// The following provide their own synchronization, and therefore don't
	// require cc.mu to be held to access them.
	csMgr *connectivityStateManager
	// picks is what the Go realization of the address choice remembers (model_choose.go).
	picks modelPicks

	// idleMu serializes the resolver's Build, ResolveNow and Close (grpc-go runs them on its
	// resolver wrapper's serializer).
	idleMu sync.Mutex

	// mu protects the following fields.
	mu              sync.RWMutex
	resolverWrapper *ccResolverWrapper                  // nil while idle; recreated when exiting idle.
	idle            bool                                // no resolver is built
	activeCalls     int                                 // RPCs begun and not ended
	sc              *ServiceConfig                      // the model applies no service config: nil.
	streams         map[*clientTransportStream]struct{} // the attempts' open streams; nil on close.
	keepaliveParams keepalive.ClientParameters

	lceMu               sync.Mutex // protects lastConnectionError
	lastConnectionError error
}

// WaitForStateChange waits until the connectivity.State of ClientConn changes from sourceState or
// ctx expires. A true value is returned in former case and false in latter.
func (cc *ClientConn) WaitForStateChange(ctx context.Context, sourceState connectivity.State) bool {
	ch := cc.csMgr.getNotifyChan()
	if cc.csMgr.getState() != sourceState {
		return true
	}
	select {
	case <-ctx.Done():
		return false
	case <-ch:
		return true
	}
}

// GetState returns the connectivity.State of ClientConn.
func (cc *ClientConn) GetState() connectivity.State {
	return cc.csMgr.getState()
}

// Connect causes all subchannels in the ClientConn to attempt to connect if
// the channel is idle.  Does not wait for the connection attempts to begin
// before returning.
//
// # Experimental
//
// Notice: This API is EXPERIMENTAL and may be changed or removed in a later
// release.
//
// MODEL: the ClientConn leaves idleness, and a connection to a reported address is made (and
// closed: the model's attempts make their own), so that the state may become Ready (what a
// blocking DialContext waits for).
func (cc *ClientConn) Connect() {
	if err := cc.exitIdleMode(); err != nil {
		return
	}
	go func() {
		conn, _, err := cc.getTransportConn(cc.ctx, false)
		if err == nil {
			conn.Close()
		}
	}()
}

// Target returns the target string of the ClientConn.
func (cc *ClientConn) Target() string {
	return cc.target
}

// CanonicalTarget returns the canonical target string used when creating cc.
//
// This always has the form "<scheme>://[authority]/<endpoint>".  For example:
//
//   - "dns:///example.com:42"
//   - "dns://8.8.8.8/example.com:42"
//   - "unix:///path/to/socket"
func (cc *ClientConn) CanonicalTarget() string {
	return cc.parsedTarget.String()
}

// resolvers can specify a per-address override for the serverName through the
// resolver.Address.ServerName field which is used only if the WithAuthority
// dial option was not used. The rationale is that per-address authority
// overrides specified by the name resolver can represent a security risk, while
// an override specified by the user is more dependable since they probably know
// what they are doing.
func (cc *ClientConn) getServerName(addr resolver.Address) string {
	if cc.dopts.authority != "" {
		return cc.dopts.authority
	}
	if addr.ServerName != "" {
		return addr.ServerName
	}
	return cc.authority
}

func getMethodConfig(sc *ServiceConfig, method string) MethodConfig {
	if sc == nil {
		return MethodConfig{}
	}
	if m, ok := sc.Methods[method]; ok {
		return m
	}
	i := strings.LastIndex(method, "/")
	if m, ok := sc.Methods[method[:i+1]]; ok {
		return m
	}
	return sc.Methods[""]
}

// GetMethodConfig gets the method config of the input method.
// If there's an exact match for input method (i.e. /service/method), we return
// the corresponding MethodConfig.
// If there isn't an exact match for the input method, we look for the service's default
// config under the service (i.e /service/) and then for the default for all services (empty string).
//
// If there is a default MethodConfig for the service, we return it.
// Otherwise, we return an empty MethodConfig.
func (cc *ClientConn) GetMethodConfig(method string) MethodConfig {
	// TODO: Avoid the locking here.
	cc.mu.RLock()
	defer cc.mu.RUnlock()
	return getMethodConfig(cc.sc, method)
}

// ResetConnectBackoff wakes up all subchannels in transient failure and causes
// them to attempt another connection immediately.  It also resets the backoff
// times used for subsequent attempts regardless of the current state.
//
// In general, this function should not be used.  Typical service or network
// outages result in a reasonable client reconnection strategy by default.
// However, if a previously unavailable network becomes available, this may be
// used to trigger an immediate reconnect.
//
// # Experimental
//
// Notice: This API is EXPERIMENTAL and may be changed or removed in a
// later release.
//
// MODEL: nothing to do (an attempt's backoff is its own).
func (cc *ClientConn) ResetConnectBackoff() {}

// Close tears down the ClientConn and all underlying connections.
//
// MODEL: the resolver is closed, and every attempt's connection (its stream ends with a transport
// failure); later RPCs fail with ErrClientConnClosing.
func (cc *ClientConn) Close() error {
	defer cc.cancel()

	cc.idleMu.Lock()
	cc.mu.Lock()
	if cc.streams == nil {
		cc.mu.Unlock()
		cc.idleMu.Unlock()
		return ErrClientConnClosing
	}

	streams := cc.streams
	cc.streams = nil
	ccr := cc.resolverWrapper
	cc.resolverWrapper = nil
	cc.csMgr.updateState(connectivity.Shutdown)
	cc.mu.Unlock()

	ccr.close()
	cc.idleMu.Unlock()
	for s := range streams {
		st := transportFailure(errConnClosing.Error())
		s.closeStream(st.Err(), false, st, nil)
	}
	return nil
}

// ErrClientConnTimeout indicates that the ClientConn cannot establish the
// underlying connections within the specified timeout.
//
// Deprecated: This error is never returned by grpc and should not be
// referenced by users.
var ErrClientConnTimeout = errors.New("grpc: timed out when dialing")

// getResolver finds the scheme in the cc's resolvers or the global registry.
// scheme should always be lowercase (typically by virtue of url.Parse()
// performing proper RFC3986 behavior).
func (cc *ClientConn) getResolver(scheme string) resolver.Builder {
	for _, rb := range cc.dopts.resolvers {
		if scheme == rb.Scheme() {
			return rb
		}
	}
	return resolver.Get(scheme)
}

func (cc *ClientConn) updateConnectionError(err error) {
	cc.lceMu.Lock()
	cc.lastConnectionError = err
	cc.lceMu.Unlock()
}

func (cc *ClientConn) connectionError() error {
	cc.lceMu.Lock()
	defer cc.lceMu.Unlock()
	return cc.lastConnectionError
}

// initParsedTargetAndResolverBuilder parses the user's dial target and stores
// the parsed target in `cc.parsedTarget`.
//
// The resolver to use is determined based on the scheme in the parsed target
// and the same is stored in `cc.resolverBuilder`.
//
// Doesn't grab cc.mu as this method is expected to be called only at Dial time.
func (cc *ClientConn) initParsedTargetAndResolverBuilder() error {
	logger.Infof("original dial target is: %q", cc.target)

	var rb resolver.Builder
	parsedTarget, err := parseTarget(cc.target)
	if err == nil {
		rb = cc.getResolver(parsedTarget.URL.Scheme)
		if rb != nil {
			cc.parsedTarget = parsedTarget
			cc.resolverBuilder = rb
			return nil
		}
	}

	// We are here because the user's dial target did not contain a scheme or
	// specified an unregistered scheme. We should fallback to the default
	// scheme, except when a custom dialer is specified in which case, we should
	// always use passthrough scheme. For either case, we need to respect any overridden
	// global defaults set by the user.
	defScheme := cc.dopts.defaultScheme
	if internal.UserSetDefaultScheme {
		defScheme = resolver.GetDefaultScheme()
	}

	canonicalTarget := defScheme + ":///" + cc.target

	parsedTarget, err = parseTarget(canonicalTarget)
	if err != nil {
		return err
	}
	rb = cc.getResolver(parsedTarget.URL.Scheme)
	if rb == nil {
		return fmt.Errorf("could not get resolver for default scheme: %q", parsedTarget.URL.Scheme)
	}
	cc.parsedTarget = parsedTarget
	cc.resolverBuilder = rb
	return nil
}

// parseTarget uses RFC 3986 semantics to parse the given target into a
// resolver.Target struct containing url. Query params are stripped from the
// endpoint.
func parseTarget(target string) (resolver.Target, error) {
	u, err := url.Parse(target)
	if err != nil {
		return resolver.Target{}, err
	}

	return resolver.Target{URL: *u}, nil
}

// encodeAuthority escapes the authority string based on valid chars defined in
// https://datatracker.ietf.org/doc/html/rfc3986#section-3.2.
func encodeAuthority(authority string) string {
	const upperhex = "0123456789ABCDEF"

	// Return for characters that must be escaped as per
	// Valid chars are mentioned here:
	// https://datatracker.ietf.org/doc/html/rfc3986#section-3.2
	shouldEscape := func(c byte) bool {
		// Alphanum are always allowed.
		if 'a' <= c && c <= 'z' || 'A' <= c && c <= 'Z' || '0' <= c && c <= '9' {
			return false
		}
		switch c {
		case '-', '_', '.', '~': // Unreserved characters
			return false
		case '!', '$', '&', '\'', '(', ')', '*', '+', ',', ';', '=': // Subdelim characters
			return false
		case ':', '[', ']', '@': // Authority related delimiters
			return false
		}
		// Everything else must be escaped.
		return true
	}

	hexCount := 0
	for i := 0; i < len(authority); i++ {
		c := authority[i]
		if shouldEscape(c) {
			hexCount++
		}
	}

	if hexCount == 0 {
		return authority
	}

	required := len(authority) + 2*hexCount
	t := make([]byte, required)

	j := 0
	// This logic is a barebones version of escape in the go net/url library.
	for i := 0; i < len(authority); i++ {
		switch c := authority[i]; {
		case shouldEscape(c):
			t[j] = '%'
			t[j+1] = upperhex[c>>4]
			t[j+2] = upperhex[c&15]
			j += 3
		default:
			t[j] = authority[i]
			j++
		}
	}
	return string(t)
}

// Determine channel authority. The order of precedence is as follows:
// - user specified authority override using `WithAuthority` dial option
// - creds' notion of server name for the authentication handshake
// - endpoint from dial target of the form "scheme://[authority]/endpoint"
//
// Stores the determined authority in `cc.authority`.
//
// Returns a non-nil error if the authority returned by the transport
// credentials do not match the authority configured through the dial option.
//
// Doesn't grab cc.mu as this method is expected to be called only at Dial time.
func (cc *ClientConn) initAuthority() error {
	dopts := cc.dopts
	// Historically, we had two options for users to specify the serverName or
	// authority for a channel. One was through the transport credentials
	// (either in its constructor, or through the OverrideServerName() method).
	// The other option (for cases where WithInsecure() dial option was used)
	// was to use the WithAuthority() dial option.
	//
	// A few things have changed since:
	// - `insecure` package with an implementation of the `TransportCredentials`
	//   interface for the insecure case
	// - WithAuthority() dial option support for secure credentials
	authorityFromCreds := ""
	if creds := dopts.copts.TransportCredentials; creds != nil && creds.Info().ServerName != "" {
		authorityFromCreds = creds.Info().ServerName
	}
	authorityFromDialOption := dopts.authority
	if (authorityFromCreds != "" && authorityFromDialOption != "") && authorityFromCreds != authorityFromDialOption {
		return fmt.Errorf("ClientConn's authority from transport creds %q and dial option %q don't match", authorityFromCreds, authorityFromDialOption)
	}

	endpoint := cc.parsedTarget.Endpoint()
	if authorityFromDialOption != "" {
		cc.authority = authorityFromDialOption
	} else if authorityFromCreds != "" {
		cc.authority = authorityFromCreds
	} else if auth, ok := cc.resolverBuilder.(resolver.AuthorityOverrider); ok {
		cc.authority = auth.OverrideAuthority(cc.parsedTarget)
	} else if strings.HasPrefix(endpoint, ":") {
		cc.authority = "localhost" + encodeAuthority(endpoint)
	} else {
		cc.authority = encodeAuthority(endpoint)
	}
	return nil
}
