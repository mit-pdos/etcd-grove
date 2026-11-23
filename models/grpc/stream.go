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
	"google.golang.org/grpc/stats"
	"io"
	"net"
	"strings"
	"sync"
	"sync/atomic"
	"time"

	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/credentials"
	"google.golang.org/grpc/encoding"
	"google.golang.org/grpc/internal"
	imetadata "google.golang.org/grpc/internal/metadata"
	"google.golang.org/grpc/internal/serviceconfig"
	"google.golang.org/grpc/mem"
	"google.golang.org/grpc/metadata"
	"google.golang.org/grpc/status"
)

// MODEL: this file is grpc-go's stream.go over the model's transport (model_transport.go): an
// attempt's transport is a connection of its own (model_clientconn.go's getTransportConn) and its
// stream a clientTransportStream; the server's stream a serverTransportStream. Removed: binary
// logging, stats handlers, tracing, channelz, the balancer's pick results and load reports, the
// config selector, retry policies and their throttling and hedging (the model applies no service
// config: grpc-go without one makes no retry but transparent ones), the subchannels' health-check
// streams. Kept as grpc-go's: the generic stream wrappers, NewStream and its interceptor, the
// client stream's attempts, commit, replay buffer and transparent retry (shouldRetry's
// unprocessed case), SendMsg, RecvMsg, Header, Trailer, CloseSend, finish, and the server
// stream.

var metadataFromOutgoingContextRaw = internal.FromOutgoingContextRaw.(func(context.Context) (metadata.MD, [][]string, bool))

// StreamHandler defines the handler called by gRPC server to complete the
// execution of a streaming RPC. srv is the service implementation on which the
// RPC was invoked.
//
// If a StreamHandler returns an error, it should either be produced by the
// status package, or be one of the context errors. Otherwise, gRPC will use
// codes.Unknown as the status code and err.Error() as the status message of the
// RPC.
type StreamHandler func(srv any, stream ServerStream) error

// StreamDesc represents a streaming RPC service's method specification.  Used
// on the server when registering services and on the client when initiating
// new streams.
type StreamDesc struct {
	// StreamName and Handler are only used when registering handlers on a
	// server.
	StreamName string        // the name of the method excluding the service
	Handler    StreamHandler // the handler called for the method

	// ServerStreams and ClientStreams are used for registering handlers on a
	// server as well as defining RPC behavior when passed to NewClientStream
	// and ClientConn.NewStream.  At least one must be true.
	ServerStreams bool // indicates the server can perform streaming sends
	ClientStreams bool // indicates the client can perform streaming sends
}

// Stream defines the common interface a client or server stream has to satisfy.
//
// Deprecated: See ClientStream and ServerStream documentation instead.
type Stream interface {
	// Deprecated: See ClientStream and ServerStream documentation instead.
	Context() context.Context
	// Deprecated: See ClientStream and ServerStream documentation instead.
	SendMsg(m any) error
	// Deprecated: See ClientStream and ServerStream documentation instead.
	RecvMsg(m any) error
}

// ClientStream defines the client-side behavior of a streaming RPC.
//
// All errors returned from ClientStream methods are compatible with the
// status package.
type ClientStream interface {
	// Header returns the header metadata received from the server if there
	// is any. It blocks if the metadata is not ready to read.  If the metadata
	// is nil and the error is also nil, then the stream was terminated without
	// headers, and the status can be discovered by calling RecvMsg.
	Header() (metadata.MD, error)
	// Trailer returns the trailer metadata from the server, if there is any.
	// It must only be called after stream.CloseAndRecv has returned, or
	// stream.Recv has returned a non-nil error (including io.EOF).
	Trailer() metadata.MD
	// CloseSend closes the send direction of the stream. This method always
	// returns a nil error. The status of the stream may be discovered using
	// RecvMsg. It is also not safe to call CloseSend concurrently with SendMsg.
	CloseSend() error
	// Context returns the context for this stream.
	//
	// It should not be called until after Header or RecvMsg has returned. Once
	// called, subsequent client-side retries are disabled.
	Context() context.Context
	// SendMsg is generally called by generated code. On error, SendMsg aborts
	// the stream. If the error was generated by the client, the status is
	// returned directly; otherwise, io.EOF is returned and the status of
	// the stream may be discovered using RecvMsg. For unary or server-streaming
	// RPCs (StreamDesc.ClientStreams is false), a nil error is returned
	// unconditionally.
	//
	// SendMsg blocks until:
	//   - There is sufficient flow control to schedule m with the transport, or
	//   - The stream is done, or
	//   - The stream breaks.
	//
	// SendMsg does not wait until the message is received by the server. An
	// untimely stream closure may result in lost messages. To ensure delivery,
	// users should ensure the RPC completed successfully using RecvMsg.
	//
	// It is safe to have a goroutine calling SendMsg and another goroutine
	// calling RecvMsg on the same stream at the same time, but it is not safe
	// to call SendMsg on the same stream in different goroutines. It is also
	// not safe to call CloseSend concurrently with SendMsg.
	//
	// It is not safe to modify the message after calling SendMsg. Tracing
	// libraries and stats handlers may use the message lazily.
	SendMsg(m any) error
	// RecvMsg blocks until it receives a message into m or the stream is
	// done. It returns io.EOF when the stream completes successfully. On
	// any other error, the stream is aborted and the error contains the RPC
	// status.
	//
	// It is safe to have a goroutine calling SendMsg and another goroutine
	// calling RecvMsg on the same stream at the same time, but it is not
	// safe to call RecvMsg on the same stream in different goroutines.
	RecvMsg(m any) error
}

// clientStreamWrapper wraps a ClientStream and handles SendMsg, CloseSend, and
// RecvMsg parities based on the nature of stream.
type clientStreamWrapper struct {
	ClientStream
	desc            *StreamDesc
	closeSendCalled atomic.Bool
}

// CloseSend closes the send direction of the stream. The implementation ensures
// that CloseSend is only called once on the underlying ClientStream, even if
// CloseSend is called multiple times on the wrapper.
func (w *clientStreamWrapper) CloseSend() error {
	if w.closeSendCalled.Swap(true) {
		return nil
	}
	return w.ClientStream.CloseSend()
}

// SendMsg sends message m across the stream. For RPCs where client can call
// SendMsg only once, i.e. only server-streaming RPCs, it converts io.EOF to nil
// and immediately calls CloseSend to trigger any interceptor hooks.
func (w *clientStreamWrapper) SendMsg(m any) error {
	err := w.ClientStream.SendMsg(m)
	// If the RPC is a client-streaming RPC, the client can send multiple
	// messages. In this case, the client should handle any type of
	// error,including io.EOF and call CloseSend once it is done sending messages.
	if w.desc.ClientStreams {
		return err
	}

	if err == io.EOF {
		// For non-client-streaming RPCs, we return nil instead of EOF on error
		// because the generated code requires it. finish is not called; RecvMsg()
		// will call it with the stream's status independently.
		return nil
	}
	if err != nil {
		return err
	}
	// In some scenarios (e.g., xDS), the same interceptors process both unary and
	// streaming RPCs, relying on CloseSend to signal that no more messages are on
	// the way. Although protobuf-generated stubs already invoke CloseSend for
	// server-streaming RPCs, it is explicitly called here to ensure downstream
	// interceptors are also notified when callers interact with the ClientStream
	// API directly.
	if err := w.CloseSend(); err != nil && err != io.EOF {
		return err
	}
	return nil

}

// RecvMsg receives message m from the stream. For RPCs that call RecvMsg only
// once i.e. only client streaming RPCs, it calls the underlying RecvMsg a
// second time after receiving the first message to get the trailers.
func (w *clientStreamWrapper) RecvMsg(m any) error {
	err := w.ClientStream.RecvMsg(m)
	if err != nil {
		return err
	}
	if w.desc.ServerStreams {
		return nil
	}
	// Call RecvMsg again for non-server streaming RPCs to get the trailers and
	// ensure RPC has completed successfully.
	err = w.ClientStream.RecvMsg(m)
	if err == io.EOF {
		return nil
	}
	if err == nil {
		return status.Error(codes.Internal, "cardinality violation: expected <EOF> for non server-streaming RPCs, but received another message")
	}
	return err
}

// defaultStreamInterceptor is a StreamClientInterceptor which wraps the
// ClientStream and is always invoked as the first interceptor. It consolidates
// behavior for different RPC types at the level closest to the application,
// which simplifies the underlying stream implementation and other interceptors
// by avoiding duplicate or scattered handling.
func defaultStreamInterceptor(ctx context.Context, desc *StreamDesc, cc *ClientConn, method string, streamer Streamer, opts ...CallOption) (ClientStream, error) {
	cs, err := streamer(ctx, desc, cc, method, opts...)
	if err != nil {
		return nil, err
	}
	return &clientStreamWrapper{ClientStream: cs, desc: desc}, nil
}

// NewStream creates a new Stream for the client side. This is typically
// called by generated code. ctx is used for the lifetime of the stream.
//
// To ensure resources are not leaked due to the stream returned, one of the following
// actions must be performed:
//
//  1. Call Close on the ClientConn.
//  2. Cancel the context provided.
//  3. Call RecvMsg until a non-nil error is returned. A protobuf-generated
//     client-streaming RPC, for instance, might use the helper function
//     CloseAndRecv (note that CloseSend does not Recv, therefore is not
//     guaranteed to release all resources).
//  4. Receive a non-nil, non-io.EOF error from Header or SendMsg.
//
// If none of the above happen, a goroutine and a context will be leaked, and grpc
// will not call the optionally-configured stats handler with a stats.End message.
func (cc *ClientConn) NewStream(ctx context.Context, desc *StreamDesc, method string, opts ...CallOption) (ClientStream, error) {
	// allow interceptor to see all applicable call options, which means those
	// configured as defaults from dial option as well as per-call options
	opts = combine(cc.dopts.callOptions, opts)

	if cc.dopts.streamInt != nil {
		return cc.dopts.streamInt(ctx, desc, cc, method, newClientStream, opts...)
	}
	return newClientStream(ctx, desc, cc, method, opts...)
}

// NewClientStream is a wrapper for ClientConn.NewStream.
func NewClientStream(ctx context.Context, desc *StreamDesc, cc *ClientConn, method string, opts ...CallOption) (ClientStream, error) {
	return cc.NewStream(ctx, desc, method, opts...)
}

var emptyMethodConfig = serviceconfig.MethodConfig{}

// endOfClientStream performs cleanup actions required for both successful and
// failed streams. This includes incrementing channelz stats and invoking all
// registered OnFinish call options.
func endOfClientStream(cc *ClientConn, err error, opts ...CallOption) {
	for _, o := range opts {
		if o, ok := o.(OnFinishCallOption); ok {
			o.OnFinish(err)
		}
	}
}

func newClientStream(ctx context.Context, desc *StreamDesc, cc *ClientConn, method string, opts ...CallOption) (_ ClientStream, err error) {
	defer func() {
		if err != nil {
			// Ensure cleanup when stream creation fails.
			endOfClientStream(cc, err, opts...)
		}
	}()

	// Start tracking the RPC for idleness purposes. This is where a stream is
	// created for both streaming and unary RPCs, and hence is a good place to
	// track active RPC count.
	//
	// MODEL: the model's idleness (model_clientconn.go) in place of the idleness manager.
	if err := cc.onCallBegin(); err != nil {
		cc.onCallEnd()
		return nil, err
	}

	// Add a calloption, to decrement the active call count, that gets executed
	// when the RPC completes.
	opts = append([]CallOption{OnFinish(func(error) { cc.onCallEnd() })}, opts...)

	if md, added, ok := metadataFromOutgoingContextRaw(ctx); ok {
		// validate md
		if err := imetadata.Validate(md); err != nil {
			return nil, status.Error(codes.Internal, err.Error())
		}
		// validate added
		for _, kvs := range added {
			for i := 0; i < len(kvs); i += 2 {
				if err := imetadata.ValidatePair(kvs[i], kvs[i+1]); err != nil {
					return nil, status.Error(codes.Internal, err.Error())
				}
			}
		}
	}
	// MODEL: no wait for the resolver's first update here (an attempt waits for an address), and
	// no config selector: the method config is empty (the model applies no service config).
	mc := &emptyMethodConfig
	return newClientStreamWithParams(ctx, desc, cc, method, mc, nil, false, opts...)
}

func newClientStreamWithParams(ctx context.Context, desc *StreamDesc, cc *ClientConn, method string, mc *serviceconfig.MethodConfig, onCommit func(), nameResolutionDelayed bool, opts ...CallOption) (_ ClientStream, err error) {
	callInfo := defaultCallInfo()
	if mc.WaitForReady != nil {
		callInfo.failFast = !*mc.WaitForReady
	}

	// Possible context leak:
	// The cancel function for the child context we create will only be called
	// when RecvMsg returns a non-nil error, if the ClientConn is closed, or if
	// an error is generated by SendMsg.
	// https://github.com/grpc/grpc-go/issues/1818.
	var cancel context.CancelFunc
	if mc.Timeout != nil && *mc.Timeout >= 0 {
		ctx, cancel = context.WithTimeout(ctx, *mc.Timeout)
	} else {
		ctx, cancel = context.WithCancel(ctx)
	}
	defer func() {
		if err != nil {
			cancel()
		}
	}()

	for _, o := range opts {
		if err := o.before(callInfo); err != nil {
			return nil, toRPCErr(err)
		}
	}
	callInfo.maxSendMessageSize = getMaxSize(mc.MaxReqSize, callInfo.maxSendMessageSize, defaultClientMaxSendMessageSize)
	callInfo.maxReceiveMessageSize = getMaxSize(mc.MaxRespSize, callInfo.maxReceiveMessageSize, defaultClientMaxReceiveMessageSize)
	if err := setCallInfoCodec(callInfo); err != nil {
		return nil, err
	}

	callHdr := &callHdr{
		Host:           cc.authority,
		Method:         method,
		ContentSubtype: callInfo.contentSubtype,
		Authority:      callInfo.authority,
	}
	if allowed := callInfo.acceptedResponseCompressors; len(allowed) > 0 {
		headerValue := strings.Join(allowed, ",")
		callHdr.AcceptedCompressors = &headerValue
	}

	// Set our outgoing compression according to the UseCompressor CallOption, if
	// set.  In that case, also find the compressor from the encoding package.
	// Otherwise, use the compressor configured by the WithCompressor DialOption,
	// if set.
	var compressorV0 Compressor
	var compressorV1 encoding.Compressor
	if ct := callInfo.compressorName; ct != "" {
		callHdr.SendCompress = ct
		if ct != encoding.Identity {
			compressorV1 = encoding.GetCompressor(ct)
			if compressorV1 == nil {
				return nil, status.Errorf(codes.Internal, "grpc: Compressor is not installed for requested grpc-encoding %q", ct)
			}
			select {} // MODEL: not modelled (stuck): grpc: compression
		}
	} else if cc.dopts.compressorV0 != nil {
		// MODEL: unreachable (NewClient blocks forever on a compressor).
		callHdr.SendCompress = cc.dopts.compressorV0.Type()
		compressorV0 = cc.dopts.compressorV0
	}
	if callInfo.creds != nil {
		callHdr.Creds = callInfo.creds
	}

	cs := &clientStream{
		callHdr:             callHdr,
		ctx:                 ctx,
		methodConfig:        mc,
		opts:                opts,
		callInfo:            callInfo,
		cc:                  cc,
		desc:                desc,
		codec:               callInfo.codec,
		compressorV0:        compressorV0,
		compressorV1:        compressorV1,
		cancel:              cancel,
		firstAttempt:        true,
		onCommit:            onCommit,
		nameResolutionDelay: nameResolutionDelayed,
	}

	// Pick the transport to use and create a new stream on the transport.
	// Assign cs.attempt upon success.
	op := func(a *csAttempt) error {
		if err := a.getTransport(); err != nil {
			return err
		}
		if err := a.newStream(); err != nil {
			return err
		}
		// Because this operation is always called either here (while creating
		// the clientStream) or by the retry code while locked when replaying
		// the operation, it is safe to access cs.attempt directly.
		cs.attempt = a
		return nil
	}
	if err := cs.withRetry(op, func() { cs.bufferForRetryLocked(0, op, nil) }); err != nil {
		return nil, err
	}

	if desc != unaryStreamDesc {
		// Listen on cc and stream contexts to cleanup when the user closes the
		// ClientConn or cancels the stream context.  In all other cases, an error
		// should already be injected into the recv buffer by the transport, which
		// the client will eventually receive, and then we will cancel the stream's
		// context in clientStream.finish.
		go func() {
			select {
			case <-cc.ctx.Done():
				cs.finish(ErrClientConnClosing)
			case <-ctx.Done():
				cs.finish(toRPCErr(ctx.Err()))
			}
		}()
	}
	return cs, nil
}

// newAttemptLocked creates a new csAttempt without a transport or stream.
func (cs *clientStream) newAttemptLocked(isTransparent bool) (*csAttempt, error) {
	if err := cs.ctx.Err(); err != nil {
		return nil, toRPCErr(err)
	}
	if err := cs.cc.ctx.Err(); err != nil {
		return nil, ErrClientConnClosing
	}

	ctx := newContextWithRPCInfo(cs.ctx, cs.callInfo.failFast, cs.callInfo.codec, cs.compressorV0, cs.compressorV1)
	return &csAttempt{
		ctx:            ctx,
		cs:             cs,
		decompressorV0: cs.cc.dopts.dc,
	}, nil
}

// MODEL: the pick is the model's (model_clientconn.go): any address reported by the resolver,
// dialed for this attempt alone.
func (a *csAttempt) getTransport() error {
	cs := a.cs

	conn, authInfo, err := cs.cc.getTransportConn(a.ctx, cs.callInfo.failFast)
	if err != nil {
		return err
	}
	a.conn, a.authInfo = conn, authInfo
	return nil
}

// MODEL: the stream is created on the attempt's connection (newClientTransportStream: the head goes
// out with the preface); a failure allows a transparent retry exactly when the head did not reach
// the server whole.
func (a *csAttempt) newStream() error {
	cs := a.cs
	cs.callHdr.PreviousAttempts = cs.numRetries
	s, err := newClientTransportStream(a.ctx, cs.cc, a.conn, a.authInfo, cs.callHdr, *cs.callInfo.maxReceiveMessageSize)
	if err != nil {
		nse, ok := err.(*newStreamError)
		if !ok {
			// Unexpected.
			return err
		}

		if nse.AllowTransparentRetry {
			a.allowTransparentRetry = true
		}

		// Unwrap and convert error.
		return toRPCErr(nse.Err)
	}
	a.transportStream = s
	a.ctx = s.Context()
	a.parser = parser{r: s, bufferPool: mem.DefaultBufferPool()} // MODEL: the default pool (connectOptions)
	return nil
}

// clientStream implements a client side Stream.
type clientStream struct {
	callHdr  *callHdr
	opts     []CallOption
	callInfo *callInfo
	cc       *ClientConn
	desc     *StreamDesc

	codec        baseCodec
	compressorV0 Compressor
	compressorV1 encoding.Compressor

	cancel context.CancelFunc // cancels all attempts

	sentLast bool // sent an end stream

	receivedFirstMsg bool // set after the first message is received

	methodConfig *MethodConfig

	ctx context.Context // the application's context, wrapped by stats/tracing

	mu                      sync.Mutex
	firstAttempt            bool // if true, transparent retry is valid
	numRetries              int  // exclusive of transparent retry attempt(s)
	numRetriesSincePushback int  // retries since pushback; to reset backoff
	finished                bool // TODO: replace with atomic cmpxchg or sync.Once?
	// attempt is the active client stream attempt.
	// The only place where it is written is the newAttemptLocked method and this method never writes nil.
	// So, attempt can be nil only inside newClientStream function when clientStream is first created.
	// One of the first things done after clientStream's creation, is to call newAttemptLocked which either
	// assigns a non nil value to the attempt or returns an error. If an error is returned from newAttemptLocked,
	// then newClientStream calls finish on the clientStream and returns. So, finish method is the only
	// place where we need to check if the attempt is nil.
	attempt *csAttempt
	// TODO(hedging): hedging will have multiple attempts simultaneously.
	committed        bool // active attempt committed for retry?
	onCommit         func()
	replayBuffer     []replayOp // operations to replay on retry
	replayBufferSize int        // current size of replayBuffer
	// nameResolutionDelay indicates if there was a delay in the name resolution.
	// This field is only valid on client side, it's always false on server side.
	nameResolutionDelay bool
}

type replayOp struct {
	op      func(a *csAttempt) error
	cleanup func()
}

// csAttempt implements a single transport stream attempt within a
// clientStream.
type csAttempt struct {
	ctx             context.Context
	cs              *clientStream
	conn            net.Conn             // MODEL: the attempt's connection (was transport)
	authInfo        credentials.AuthInfo // MODEL: its handshake's
	transportStream *clientTransportStream
	parser          parser

	finished        bool
	decompressorV0  Decompressor
	decompressorV1  encoding.Compressor
	decompressorSet bool

	mu sync.Mutex

	// set for newStream errors that may be transparently retried
	allowTransparentRetry bool
	// set for pick errors that are returned as a status
	drop bool
}

func (cs *clientStream) commitAttemptLocked() {
	if !cs.committed && cs.onCommit != nil {
		cs.onCommit()
	}
	cs.committed = true
	for _, op := range cs.replayBuffer {
		if op.cleanup != nil {
			op.cleanup()
		}
	}
	cs.replayBuffer = nil
}

func (cs *clientStream) commitAttempt() {
	cs.mu.Lock()
	cs.commitAttemptLocked()
	cs.mu.Unlock()
}

// shouldRetry returns nil if the RPC should be retried; otherwise it returns
// the error that should be returned by the operation.  If the RPC should be
// retried, the bool indicates whether it is being retried transparently.
func (a *csAttempt) shouldRetry(err error) (bool, error) {
	cs := a.cs

	if cs.finished || cs.committed || a.drop {
		// RPC is finished or committed or was dropped by the picker; cannot retry.
		return false, err
	}
	if a.transportStream == nil && a.allowTransparentRetry {
		return true, nil
	}
	// Wait for the trailers.
	unprocessed := false
	if a.transportStream != nil {
		<-a.transportStream.Done()
		unprocessed = a.transportStream.Unprocessed()
	}
	if cs.firstAttempt && unprocessed {
		// First attempt, stream unprocessed: transparently retry.
		return true, nil
	}
	// MODEL: no retry policy (the model applies no service config): no other retry.
	return false, err
}

// Returns nil if a retry was performed and succeeded; error otherwise.
func (cs *clientStream) retryLocked(attempt *csAttempt, lastErr error) error {
	for {
		attempt.finish(toRPCErr(lastErr))
		isTransparent, err := attempt.shouldRetry(lastErr)
		if err != nil {
			cs.commitAttemptLocked()
			return err
		}
		cs.firstAttempt = false
		attempt, err = cs.newAttemptLocked(isTransparent)
		if err != nil {
			// Only returns error if the clientconn is closed or the context of
			// the stream is canceled.
			return err
		}
		// Note that the first op in replayBuffer always sets cs.attempt
		// if it is able to pick a transport and create a stream.
		if lastErr = cs.replayBufferLocked(attempt); lastErr == nil {
			return nil
		}
	}
}

func (cs *clientStream) Context() context.Context {
	cs.commitAttempt()
	// No need to lock before using attempt, since we know it is committed and
	// cannot change.
	if cs.attempt.transportStream != nil {
		return cs.attempt.transportStream.Context()
	}
	return cs.ctx
}

func (cs *clientStream) withRetry(op func(a *csAttempt) error, onSuccess func()) error {
	cs.mu.Lock()
	for {
		if cs.committed {
			cs.mu.Unlock()
			// toRPCErr is used in case the error from the attempt comes from
			// NewClientStream, which intentionally doesn't return a status
			// error to allow for further inspection; all other errors should
			// already be status errors.
			return toRPCErr(op(cs.attempt))
		}
		if len(cs.replayBuffer) == 0 {
			// For the first op, which controls creation of the stream and
			// assigns cs.attempt, we need to create a new attempt inline
			// before executing the first op.  On subsequent ops, the attempt
			// is created immediately before replaying the ops.
			var err error
			if cs.attempt, err = cs.newAttemptLocked(false /* isTransparent */); err != nil {
				cs.mu.Unlock()
				cs.finish(err)
				return err
			}
		}
		a := cs.attempt
		cs.mu.Unlock()
		err := op(a)
		cs.mu.Lock()
		if a != cs.attempt {
			// We started another attempt already.
			continue
		}
		if err == io.EOF {
			<-a.transportStream.Done()
		}
		if err == nil || (err == io.EOF && a.transportStream.Status().Code() == codes.OK) {
			onSuccess()
			cs.mu.Unlock()
			return err
		}
		if err := cs.retryLocked(a, err); err != nil {
			cs.mu.Unlock()
			return err
		}
	}
}

func (cs *clientStream) Header() (metadata.MD, error) {
	var m metadata.MD
	err := cs.withRetry(func(a *csAttempt) error {
		var err error
		m, err = a.transportStream.Header()
		return toRPCErr(err)
	}, cs.commitAttemptLocked)

	if m == nil && err == nil {
		// The stream ended with success.  Finish the clientStream.
		err = io.EOF
	}

	if err != nil {
		cs.finish(err)
		// Do not return the error.  The user should get it by calling Recv().
		return nil, nil
	}

	return m, nil
}

func (cs *clientStream) Trailer() metadata.MD {
	// On RPC failure, we never need to retry, because usage requires that
	// RecvMsg() returned a non-nil error before calling this function is valid.
	// We would have retried earlier if necessary.
	//
	// Commit the attempt anyway, just in case users are not following those
	// directions -- it will prevent races and should not meaningfully impact
	// performance.
	cs.commitAttempt()
	if cs.attempt.transportStream == nil {
		return nil
	}
	return cs.attempt.transportStream.Trailer()
}

func (cs *clientStream) replayBufferLocked(attempt *csAttempt) error {
	for _, f := range cs.replayBuffer {
		if err := f.op(attempt); err != nil {
			return err
		}
	}
	return nil
}

func (cs *clientStream) bufferForRetryLocked(sz int, op func(a *csAttempt) error, cleanup func()) {
	// Note: we still will buffer if retry is disabled (for transparent retries).
	if cs.committed {
		return
	}
	cs.replayBufferSize += sz
	if cs.replayBufferSize > cs.callInfo.maxRetryRPCBufferSize {
		cs.commitAttemptLocked()
		cleanup()
		return
	}
	cs.replayBuffer = append(cs.replayBuffer, replayOp{op: op, cleanup: cleanup})
}

func (cs *clientStream) SendMsg(m any) (err error) {
	defer func() {
		if err != nil && err != io.EOF {
			// Call finish on the client stream for errors generated by this SendMsg
			// call, as these indicate problems created by this client.  (Transport
			// errors are converted to an io.EOF error in csAttempt.sendMsg; the real
			// error will be returned from RecvMsg eventually in that case, or be
			// retried.)
			cs.finish(err)
		}
	}()
	if cs.sentLast {
		return status.Errorf(codes.Internal, "SendMsg called after CloseSend")
	}
	if !cs.desc.ClientStreams {
		cs.sentLast = true
	}

	// load hdr, payload, data
	hdr, data, payload, pf, err := prepareMsg(m, cs.codec, cs.compressorV0, cs.compressorV1, mem.DefaultBufferPool()) // MODEL: the default pool
	if err != nil {
		return err
	}

	defer func() {
		data.Free()
		// only free payload if compression was made, and therefore it is a different set
		// of buffers from data.
		if pf.isCompressed() {
			payload.Free()
		}
	}()

	dataLen := data.Len()
	payloadLen := payload.Len()
	// TODO(dfawley): should we be checking len(data) instead?
	if payloadLen > *cs.callInfo.maxSendMessageSize {
		return status.Errorf(codes.ResourceExhausted, "trying to send message larger than max (%d vs. %d)", payloadLen, *cs.callInfo.maxSendMessageSize)
	}

	// always take an extra ref in case data == payload (i.e. when the data isn't
	// compressed). The original ref will always be freed by the deferred free above.
	payload.Ref()
	op := func(a *csAttempt) error {
		return a.sendMsg(m, hdr, payload, dataLen, payloadLen)
	}

	// onSuccess is invoked when the op is captured for a subsequent retry. If the
	// stream was established by a previous message and therefore retries are
	// disabled, onSuccess will not be invoked, and payloadRef can be freed
	// immediately.
	onSuccessCalled := false
	err = cs.withRetry(op, func() {
		cs.bufferForRetryLocked(len(hdr)+payloadLen, op, payload.Free)
		onSuccessCalled = true
	})
	if !onSuccessCalled {
		payload.Free()
	}
	return err
}

func (cs *clientStream) RecvMsg(m any) error {
	var recvInfo *payloadInfo
	err := cs.withRetry(func(a *csAttempt) error {
		return a.recvMsg(m, recvInfo)
	}, cs.commitAttemptLocked)
	if err != nil {
		// err != nil indicates end of stream.
		cs.finish(err)
	}
	return err
}

func (cs *clientStream) CloseSend() error {
	if cs.sentLast {
		// Return a nil error on repeated calls to this method.
		return nil
	}
	cs.sentLast = true
	op := func(a *csAttempt) error {
		a.transportStream.Write(nil, nil, &writeOptions{Last: true})
		// Always return nil; io.EOF is the only error that might make sense
		// instead, but there is no need to signal the client to call RecvMsg
		// as the only use left for the stream after CloseSend is to call
		// RecvMsg.  This also matches historical behavior.
		return nil
	}
	cs.withRetry(op, func() { cs.bufferForRetryLocked(0, op, nil) })
	// We don't return an error here as we expect users to read all messages
	// from the stream and get the RPC status from RecvMsg().  Note that
	// SendMsg() must return an error when one occurs so the application
	// knows to stop sending messages, but that does not apply here.
	return nil
}

func (cs *clientStream) finish(err error) {
	if err == io.EOF {
		// Ending a stream with EOF indicates a success.
		err = nil
	}
	cs.mu.Lock()
	if cs.finished {
		cs.mu.Unlock()
		return
	}
	cs.finished = true
	cs.commitAttemptLocked()
	attemptCreated := cs.attempt != nil
	if attemptCreated {
		cs.attempt.finish(err)
		// after functions all rely upon having a stream.
		if cs.attempt.transportStream != nil {
			for _, o := range cs.opts {
				o.after(cs.callInfo, cs.attempt)
			}
		}
	}

	cs.mu.Unlock()
	// If no attempt was ever created, stream creation has failed, and the
	// cleanup is left to newClientStream, whose deferred cleanup invokes
	// endOfClientStream if the call fails. Invoking it here as well would
	// run the cleanup twice for the same call.
	if attemptCreated {
		endOfClientStream(cs.cc, err, cs.opts...)
	}
	cs.cancel()
}

func (a *csAttempt) sendMsg(m any, hdr []byte, payld mem.BufferSlice, dataLength, payloadLength int) error {
	cs := a.cs
	if err := a.transportStream.Write(hdr, payld, &writeOptions{Last: !cs.desc.ClientStreams}); err != nil {
		return io.EOF
	}
	return nil
}

func (a *csAttempt) recvMsg(m any, payInfo *payloadInfo) (err error) {
	cs := a.cs
	if !a.decompressorSet {
		// Block until we receive headers containing received message encoding.
		if ct := a.transportStream.RecvCompress(); ct != "" && ct != encoding.Identity {
			if a.decompressorV0 == nil || a.decompressorV0.Type() != ct {
				// No configured decompressor, or it does not match the incoming
				// message encoding; attempt to find a registered compressor that does.
				a.decompressorV0 = nil
				a.decompressorV1 = encoding.GetCompressor(ct)
			}
			// Validate that the compression method is acceptable for this call.
			if !acceptedCompressorAllows(cs.callInfo.acceptedResponseCompressors, ct) {
				return status.Errorf(codes.Internal, "grpc: peer compressed the response with %q which is not allowed by AcceptCompressors", ct)
			}
		} else {
			// No compression is used; disable our decompressor.
			a.decompressorV0 = nil
		}
		// Only initialize this state once per stream.
		a.decompressorSet = true
	}
	if err := recv(&a.parser, cs.codec, a.transportStream, a.decompressorV0, m, *cs.callInfo.maxReceiveMessageSize, payInfo, a.decompressorV1, false); err != nil {
		if err == io.EOF {
			if statusErr := a.transportStream.Status().Err(); statusErr != nil {
				return statusErr
			}
			// Received no msg and status OK for non-server streaming rpcs.
			if !cs.desc.ServerStreams && !cs.receivedFirstMsg {
				return status.Error(codes.Internal, "cardinality violation: received no response message from non-server-streaming RPC")
			}
			return io.EOF // indicates successful end of stream.
		}

		return toRPCErr(err)
	}
	cs.receivedFirstMsg = true
	return nil
}

func (a *csAttempt) finish(err error) {
	a.mu.Lock()
	if a.finished {
		a.mu.Unlock()
		return
	}
	a.finished = true
	if err == io.EOF {
		// Ending a stream with EOF indicates a success.
		err = nil
	}
	if a.transportStream != nil {
		a.transportStream.Close(err)
	} else if a.conn != nil {
		// MODEL: an attempt whose stream was not created gives its connection up.
		a.conn.Close()
	}
	a.mu.Unlock()
}

// MODEL: newNonRetryClientStream and addrConnStream (the streams of a subchannel's health
// check) are removed: the model has no subchannels.

// ServerStream defines the server-side behavior of a streaming RPC.
//
// Errors returned from ServerStream methods are compatible with the status
// package.  However, the status code will often not match the RPC status as
// seen by the client application, and therefore, should not be relied upon for
// this purpose.
type ServerStream interface {
	// SetHeader sets the header metadata. It may be called multiple times.
	// When call multiple times, all the provided metadata will be merged.
	// All the metadata will be sent out when one of the following happens:
	//  - ServerStream.SendHeader() is called;
	//  - The first response is sent out;
	//  - An RPC status is sent out (error or success).
	SetHeader(metadata.MD) error
	// SendHeader sends the header metadata.
	// The provided md and headers set by SetHeader() will be sent.
	// It fails if called multiple times.
	SendHeader(metadata.MD) error
	// SetTrailer sets the trailer metadata which will be sent with the RPC status.
	// When called more than once, all the provided metadata will be merged.
	SetTrailer(metadata.MD)
	// Context returns the context for this stream.
	Context() context.Context
	// SendMsg sends a message. On error, SendMsg aborts the stream and the
	// error is returned directly.
	//
	// SendMsg blocks until:
	//   - There is sufficient flow control to schedule m with the transport, or
	//   - The stream is done, or
	//   - The stream breaks.
	//
	// SendMsg does not wait until the message is received by the client. An
	// untimely stream closure may result in lost messages.
	//
	// It is safe to have a goroutine calling SendMsg and another goroutine
	// calling RecvMsg on the same stream at the same time, but it is not safe
	// to call SendMsg on the same stream in different goroutines.
	//
	// It is not safe to modify the message after calling SendMsg. Tracing
	// libraries and stats handlers may use the message lazily.
	SendMsg(m any) error
	// RecvMsg blocks until it receives a message into m or the stream is
	// done. It returns io.EOF when the client has performed a CloseSend. On
	// any non-EOF error, the stream is aborted and the error contains the
	// RPC status.
	//
	// It is safe to have a goroutine calling SendMsg and another goroutine
	// calling RecvMsg on the same stream at the same time, but it is not
	// safe to call RecvMsg on the same stream in different goroutines.
	RecvMsg(m any) error
}

// serverStream implements a server side Stream.
type serverStream struct {
	ctx   context.Context
	s     *serverTransportStream
	p     parser
	codec baseCodec
	desc  *StreamDesc

	compressorV0   Compressor
	compressorV1   encoding.Compressor
	decompressorV0 Decompressor
	decompressorV1 encoding.Compressor

	sendCompressorName string

	recvFirstMsg bool // set after the first message is received

	maxReceiveMessageSize int
	maxSendMessageSize    int
	statsHandler          stats.Handler

	statusWritten atomic.Bool // True if status has been written to the transport.

	mu sync.Mutex // protects trInfo.tr after the service handler runs.
}

func (ss *serverStream) Context() context.Context {
	return ss.ctx
}

func (ss *serverStream) SetHeader(md metadata.MD) error {
	if md.Len() == 0 {
		return nil
	}
	err := imetadata.Validate(md)
	if err != nil {
		return status.Error(codes.Internal, err.Error())
	}
	return ss.s.SetHeader(md)
}

func (ss *serverStream) SendHeader(md metadata.MD) error {
	err := imetadata.Validate(md)
	if err != nil {
		return status.Error(codes.Internal, err.Error())
	}

	return ss.s.SendHeader(md)
}

func (ss *serverStream) SetTrailer(md metadata.MD) {
	if md.Len() == 0 {
		return
	}
	if err := imetadata.Validate(md); err != nil {
		logger.Errorf("stream: failed to validate md when setting trailer, err: %v", err)
	}
	ss.s.SetTrailer(md)
}

// writeStatus sends the status of a stream to the client. It uses an atomic
// CAS to guarantee that the status is written to the transport exactly once,
// even if called concurrently.
func (ss *serverStream) writeStatus(st *status.Status) error {
	if !ss.statusWritten.CompareAndSwap(false, true) {
		return nil
	}
	return ss.s.WriteStatus(st)
}

func (ss *serverStream) SendMsg(m any) (err error) {
	defer func() {
		if err != nil && err != io.EOF {
			st, _ := status.FromError(toRPCErr(err))
			ss.writeStatus(st)
			// Non-user specified status was sent out. This should be an error
			// case (as a server side Cancel maybe).
			//
			// This is not handled specifically now. User will return a final
			// status from the service handler, we will log that error instead.
			// This behavior is similar to an interceptor.
		}
	}()

	// Server handler could have set new compressor by calling SetSendCompressor.
	// In case it is set, we need to use it for compressing outbound message.
	if sendCompressorsName := ss.s.SendCompress(); sendCompressorsName != ss.sendCompressorName {
		ss.compressorV1 = encoding.GetCompressor(sendCompressorsName)
		ss.sendCompressorName = sendCompressorsName
	}

	// load hdr, payload, data
	hdr, data, payload, pf, err := prepareMsg(m, ss.codec, ss.compressorV0, ss.compressorV1, ss.p.bufferPool)
	if err != nil {
		return err
	}

	defer func() {
		data.Free()
		// only free payload if compression was made, and therefore it is a different set
		// of buffers from data.
		if pf.isCompressed() {
			payload.Free()
		}
	}()

	dataLen := data.Len()
	payloadLen := payload.Len()

	// TODO(dfawley): should we be checking len(data) instead?
	if payloadLen > ss.maxSendMessageSize {
		return status.Errorf(codes.ResourceExhausted, "trying to send message larger than max (%d vs. %d)", payloadLen, ss.maxSendMessageSize)
	}
	if err := ss.s.Write(hdr, payload, &writeOptions{Last: false}); err != nil {
		return toRPCErr(err)
	}
	if ss.statsHandler != nil {
		ss.statsHandler.HandleRPC(ss.s.Context(), outPayload(false, m, dataLen, payloadLen, time.Now()))
	}
	return nil
}

func (ss *serverStream) RecvMsg(m any) (err error) {
	defer func() {
		if err != nil && err != io.EOF {
			st, _ := status.FromError(toRPCErr(err))
			ss.writeStatus(st)
			// Non-user specified status was sent out. This should be an error
			// case (as a server side Cancel maybe).
			//
			// This is not handled specifically now. User will return a final
			// status from the service handler, we will log that error instead.
			// This behavior is similar to an interceptor.
		}
	}()
	var payInfo *payloadInfo
	if ss.statsHandler != nil {
		payInfo = &payloadInfo{}
		defer payInfo.free()
	}
	if err := recv(&ss.p, ss.codec, ss.s, ss.decompressorV0, m, ss.maxReceiveMessageSize, payInfo, ss.decompressorV1, true); err != nil {
		if err == io.EOF {
			// Received no request msg for non-client streaming rpcs.
			if !ss.desc.ClientStreams && !ss.recvFirstMsg {
				return status.Error(codes.Internal, "cardinality violation: received no request message from non-client-streaming RPC")
			}
			return err
		}
		if err == io.ErrUnexpectedEOF {
			err = status.Error(codes.Internal, io.ErrUnexpectedEOF.Error())
		}
		return toRPCErr(err)
	}
	ss.recvFirstMsg = true
	if ss.statsHandler != nil {
		ss.statsHandler.HandleRPC(ss.s.Context(), &stats.InPayload{
			RecvTime:         time.Now(),
			Payload:          m,
			Length:           payInfo.uncompressedBytes.Len(),
			WireLength:       payInfo.compressedLength + headerLen,
			CompressedLength: payInfo.compressedLength,
		})
	}

	if ss.desc.ClientStreams {
		// Subsequent messages should be received by subsequent RecvMsg calls.
		return nil
	}
	// Special handling for non-client-stream rpcs.
	// This recv expects EOF or errors, so we don't collect inPayload.
	if err := recv(&ss.p, ss.codec, ss.s, ss.decompressorV0, m, ss.maxReceiveMessageSize, nil, ss.decompressorV1, true); err == io.EOF {
		return nil
	} else if err != nil {
		return err
	}
	return status.Error(codes.Internal, "cardinality violation: received multiple request messages for non-client-streaming RPC")
}

// MethodFromServerStream returns the method string for the input stream.
// The returned string is in the format of "/service/method".
func MethodFromServerStream(stream ServerStream) (string, bool) {
	return Method(stream.Context())
}

// prepareMsg returns the hdr, payload and data using the compressors passed or
// using the passed preparedmsg. The returned boolean indicates whether
// compression was made and therefore whether the payload needs to be freed in
// addition to the returned data. Freeing the payload if the returned boolean is
// false can lead to undefined behavior.
func prepareMsg(m any, codec baseCodec, cp Compressor, comp encoding.Compressor, pool mem.BufferPool) (hdr []byte, data, payload mem.BufferSlice, pf payloadFormat, err error) {
	if preparedMsg, ok := m.(*PreparedMsg); ok {
		return preparedMsg.hdr, preparedMsg.encodedData, preparedMsg.payload, preparedMsg.pf, nil
	}
	// The input interface is not a prepared msg.
	// Marshal and Compress the data at this point
	data, err = encode(codec, m)
	if err != nil {
		return nil, nil, nil, 0, err
	}
	compData, pf, err := compress(data, cp, comp, pool)
	if err != nil {
		data.Free()
		return nil, nil, nil, 0, err
	}
	hdr, payload = msgHeader(data, compData, pf)
	return hdr, data, payload, pf, nil
}
