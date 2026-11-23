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

// MODEL: the transport, in place of grpc-go's HTTP/2 transport (internal/transport: http2_client.go,
// http2_server.go, controlbuf.go, flow control, keepalive): one stream per net.Conn, over the
// model's wire (model_wire.go). The two stream types play the roles of transport.ClientStream and
// transport.ServerStream for the real code of stream.go and server.go: the same methods, with
// grpc-go's semantics as the program observes them. The header processing (createHeaderFields,
// operateHeaders, writeHeaderLocked, writeStatus, writeEarlyAbort) is grpc-go's code, adapted from
// hpack fields to the model's; each function says where it comes from.
//
// What is not modeled, and why the program cannot tell: stream ids and multiplexing (one stream
// per connection; a connection's addresses are the only trace, and they are any address);
// flow control (a write is visible to the peer's reader at once, which buffers what the program
// has not read yet: only timing and memory differ); HPACK, settings, pings, keepalive, GOAWAY
// (a GOAWAY's effect on a stream, refusal before dispatch or the end of an idle connection, is
// kept: a REFUSED_STREAM reset, and a connection serves one stream); compression (a compressor is outside
// the model: setting one blocks forever).

import (
	"context"
	"encoding/binary"
	"errors"
	"fmt"
	"io"
	"net"
	"strconv"
	"strings"
	"sync"
	"time"

	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/credentials"
	"google.golang.org/grpc/internal/grpcutil"
	imetadata "google.golang.org/grpc/internal/metadata"
	istatus "google.golang.org/grpc/internal/status"
	"google.golang.org/grpc/keepalive"
	"google.golang.org/grpc/mem"
	"google.golang.org/grpc/metadata"
	"google.golang.org/grpc/peer"
	"google.golang.org/grpc/stats"
	"google.golang.org/grpc/status"
	"google.golang.org/protobuf/proto"
)

// streamState is a stream's state (transport's streamState).
type streamState uint32

const (
	streamActive    streamState = iota
	streamWriteDone             // EndStream sent
	streamReadDone              // EndStream received
	streamDone                  // the entire stream is finished.
)

// writeOptions is transport.WriteOptions.
type writeOptions struct {
	// Last indicates whether this write is the last piece for this stream.
	Last bool
}

// connectOptions is transport.ConnectOptions: what the dial options set for the transport. The
// model uses UserAgent, Dialer, PerRPCCredentials, TransportCredentials and CredsBundle; it checks
// that StatsHandlers is empty; the others (keepalive, windows, buffers) change nothing the program
// observes.
type connectOptions struct {
	UserAgent              string
	Dialer                 func(context.Context, string) (net.Conn, error)
	FailOnNonTempDialError bool
	PerRPCCredentials      []credentials.PerRPCCredentials
	TransportCredentials   credentials.TransportCredentials
	CredsBundle            credentials.Bundle
	KeepaliveParams        keepalive.ClientParameters
	StatsHandlers          []stats.Handler
	InitialWindowSize      int32
	InitialConnWindowSize  int32
	WriteBufferSize        int
	ReadBufferSize         int
	SharedWriteBuffer      bool
	MaxHeaderListSize      *uint32
	// MODEL: no BufferPool field (the default pool; withBufferPool blocks forever)
	StaticWindowSize bool
}

// callHdr is transport.CallHdr: what a client stream's header fields are made from.
type callHdr struct {
	Host                string
	Method              string
	SendCompress        string
	AcceptedCompressors *string
	Creds               credentials.PerRPCCredentials
	ContentSubtype      string
	PreviousAttempts    int
	Authority           string
}

// connectionError is transport.ConnectionError: an error of the connection a stream runs on
// (toRPCErr makes it Unavailable with its description).
type connectionError struct {
	Desc string
}

func (e connectionError) Error() string {
	return fmt.Sprintf("connection error: desc = %q", e.Desc)
}

// newStreamError is transport.NewStreamError: a client stream that could not be created; it may
// be retried transparently when nothing of it reached the server.
type newStreamError struct {
	Err                   error
	AllowTransparentRetry bool
}

func (e *newStreamError) Error() string {
	return e.Err.Error()
}

var (
	// errStreamDone is transport's: a write on a stream that is done.
	errStreamDone = errors.New("the stream is done")
	// errIllegalHeaderWrite is transport.ErrIllegalHeaderWrite.
	errIllegalHeaderWrite = status.Error(codes.Internal, "transport: SendHeader called multiple times")
	// errConnClosing is transport.ErrConnClosing.
	errTransportClosing = connectionError{Desc: "transport is closing"}
)

// contextErr is transport.ContextErr.
func contextErr(err error) error {
	switch err {
	case context.DeadlineExceeded:
		return status.Error(codes.DeadlineExceeded, err.Error())
	case context.Canceled:
		return status.Error(codes.Canceled, err.Error())
	}
	return status.Errorf(codes.Internal, "Unexpected error from context packet: %v", err)
}

// transportFailureCodes are the codes a stream may end with when its connection fails before its
// status arrives. grpc-go reports Unavailable in most cases (a ConnectionError, "transport is
// closing", "error reading from server"), and other codes in others (a RST_STREAM's code, Internal
// for a protocol error, Canceled when the ClientConn closes); the model allows any non-OK code
// (modelChooseN; in Go, the first, Unavailable).
var transportFailureCodes = []codes.Code{
	codes.Unavailable, codes.Canceled, codes.Unknown, codes.InvalidArgument,
	codes.DeadlineExceeded, codes.NotFound, codes.AlreadyExists, codes.PermissionDenied,
	codes.ResourceExhausted, codes.FailedPrecondition, codes.Aborted, codes.OutOfRange,
	codes.Unimplemented, codes.Internal, codes.DataLoss, codes.Unauthenticated,
}

// transportFailure is the status of a stream whose connection failed (desc: grpc-go's description
// of the failure).
func transportFailure(desc string) *status.Status {
	return status.New(transportFailureCodes[modelChooseN(len(transportFailureCodes))], desc)
}

// recvQueue is a stream's receive buffer (transport's recvBuffer): the messages its connection's
// reader has read and the stream's end, in order.
type recvQueue struct {
	mu     sync.Mutex
	items  []recvMsg
	signal chan struct{} // closed and replaced when an item is added
}

func newRecvQueue() *recvQueue {
	return &recvQueue{signal: make(chan struct{})}
}

func (q *recvQueue) put(m recvMsg) {
	q.mu.Lock()
	q.items = append(q.items, m)
	close(q.signal)
	q.signal = make(chan struct{})
	q.mu.Unlock()
}

// peek returns the first item, if any, and a channel closed when the queue changes. An end
// (err set) stays in the queue: every later read sees it.
func (q *recvQueue) take() (recvMsg, bool, <-chan struct{}) {
	q.mu.Lock()
	defer q.mu.Unlock()
	if len(q.items) == 0 {
		return recvMsg{}, false, q.signal
	}
	m := q.items[0]
	if m.err == nil {
		q.items = q.items[1:]
	}
	return m, true, nil
}

// ---------------------------------------------------------------------------------------------
// The client side.

// clientTransportStream is a client stream on its own connection: transport.ClientStream, with
// the connection's reader (http2Client.reader) as a goroutine of its own.
type clientTransportStream struct {
	cc      *ClientConn
	conn    net.Conn
	ctx     context.Context // the attempt's context, with the peer
	method  string
	maxRecv int // the call's receive limit (checked by the reader before reading a message)

	wmu         sync.Mutex // serializes the writes on conn
	recv        *recvQueue
	pending     recvMsg // the message whose header the parser read, its payload not yet
	havePending bool

	mu               sync.Mutex
	state            streamState
	headerChan       chan struct{} // closed when the header arrives or the stream ends
	headerChanClosed bool
	headerValid      bool
	noHeaders        bool // the stream ended without a header (trailers-only, or a failure)
	header           metadata.MD
	recvCompress     string
	trailer          metadata.MD
	status           *status.Status
	bytesReceived    bool
	unprocessed      bool          // the server refused the stream: it was never dispatched
	done             chan struct{} // closed when the stream ends
}

// newClientTransportStream creates the stream of an attempt on conn (a fresh connection, just
// dialed, handshaken and its prefaces exchanged): http2Client.NewStream's work, with the header
// fields made by createHeaderFields, sent in one write. A newStreamError if it fails; it allows
// a transparent retry exactly when the server cannot have read the head (the write that carried
// it failed before writing all of it).
func newClientTransportStream(ctx context.Context, cc *ClientConn, conn net.Conn, authInfo credentials.AuthInfo, hdr *callHdr, maxRecv int) (*clientTransportStream, error) {
	pr := &peer.Peer{Addr: conn.RemoteAddr(), LocalAddr: conn.LocalAddr(), AuthInfo: authInfo}
	ctx = peer.NewContext(ctx, pr)
	fields, err := createHeaderFields(ctx, cc, authInfo, hdr)
	if err != nil {
		conn.Close()
		return nil, &newStreamError{Err: err, AllowTransparentRetry: false}
	}
	s := &clientTransportStream{
		cc:         cc,
		conn:       conn,
		ctx:        ctx,
		method:     hdr.Method,
		maxRecv:    maxRecv,
		recv:       newRecvQueue(),
		headerChan: make(chan struct{}),
		done:       make(chan struct{}),
	}
	if !cc.addStream(s) {
		conn.Close()
		return nil, &newStreamError{Err: ErrClientConnClosing, AllowTransparentRetry: false}
	}
	b := appendHeaderBlock(nil, frameHead, fields)
	s.wmu.Lock()
	n, werr := conn.Write(b)
	s.wmu.Unlock()
	if werr != nil && n < len(b) {
		// Nothing the server can have dispatched: the head is not whole.
		cc.removeStream(s)
		conn.Close()
		return nil, &newStreamError{Err: connectionError{Desc: "transport: " + werr.Error()}, AllowTransparentRetry: true}
	}
	go s.reader()
	return s, nil
}

// createHeaderFields is http2Client.createHeaderFields (with getTrAuthData and getCallAuthData
// inlined from http2_client.go): the request's header fields.
func createHeaderFields(ctx context.Context, cc *ClientConn, authInfo credentials.AuthInfo, callHdr *callHdr) ([]headerField, error) {
	perRPCCreds := cc.dopts.copts.PerRPCCredentials
	aud := ""
	if len(perRPCCreds) != 0 || callHdr.Creds != nil {
		// createAudience: omit port if it is the default one.
		host := strings.TrimSuffix(callHdr.Host, ":443")
		pos := strings.LastIndex(callHdr.Method, "/")
		if pos == -1 {
			pos = len(callHdr.Method)
		}
		aud = "https://" + host + callHdr.Method[:pos]
	}
	ri := credentials.RequestInfo{
		Method:   callHdr.Method,
		AuthInfo: authInfo,
	}
	ctxWithRequestInfo := credentials.NewContextWithRequestInfo(ctx, ri)
	// getTrAuthData
	var authData map[string]string
	if len(perRPCCreds) != 0 {
		authData = map[string]string{}
		for _, c := range perRPCCreds {
			data, err := c.GetRequestMetadata(ctxWithRequestInfo, aud)
			if err != nil {
				if st, ok := status.FromError(err); ok {
					// Restrict the code to the list allowed by gRFC A54.
					if istatus.IsRestrictedControlPlaneCode(st) {
						err = status.Errorf(codes.Internal, "transport: received per-RPC creds error with illegal status: %v", err)
					}
					return nil, err
				}
				return nil, status.Errorf(codes.Unauthenticated, "transport: per-RPC creds failed due to error: %v", err)
			}
			for k, v := range data {
				// Capital header names are illegal in HTTP/2.
				k = strings.ToLower(k)
				if err := imetadata.ValidatePair(k, v); err != nil {
					return nil, status.Error(codes.Internal, err.Error())
				}
				authData[k] = v
			}
		}
	}
	// getCallAuthData
	var callAuthData map[string]string
	if callCreds := callHdr.Creds; callCreds != nil {
		if callCreds.RequireTransportSecurity() {
			// The model's connections are insecure (isSecure is false).
			return nil, status.Error(codes.Unauthenticated, "transport: cannot send secure credentials on an insecure connection")
		}
		data, err := callCreds.GetRequestMetadata(ctxWithRequestInfo, aud)
		if err != nil {
			if st, ok := status.FromError(err); ok {
				// Restrict the code to the list allowed by gRFC A54.
				if istatus.IsRestrictedControlPlaneCode(st) {
					err = status.Errorf(codes.Internal, "transport: received per-RPC creds error with illegal status: %v", err)
				}
				return nil, err
			}
			return nil, status.Errorf(codes.Internal, "transport: per-RPC creds failed due to error: %v", err)
		}
		callAuthData = make(map[string]string, len(data))
		for k, v := range data {
			// Capital header names are illegal in HTTP/2
			k = strings.ToLower(k)
			if err := imetadata.ValidatePair(k, v); err != nil {
				return nil, status.Error(codes.Internal, err.Error())
			}
			callAuthData[k] = v
		}
	}
	registeredCompressors := grpcutil.RegisteredCompressors()
	if callHdr.AcceptedCompressors != nil {
		registeredCompressors = *callHdr.AcceptedCompressors
	}
	var headerFields []headerField
	headerFields = append(headerFields, headerField{Name: ":method", Value: "POST"})
	headerFields = append(headerFields, headerField{Name: ":scheme", Value: "http"})
	headerFields = append(headerFields, headerField{Name: ":path", Value: callHdr.Method})
	headerFields = append(headerFields, headerField{Name: ":authority", Value: callHdr.Host})
	headerFields = append(headerFields, headerField{Name: "content-type", Value: grpcutil.ContentType(callHdr.ContentSubtype)})
	headerFields = append(headerFields, headerField{Name: "user-agent", Value: cc.dopts.copts.UserAgent})
	headerFields = append(headerFields, headerField{Name: "te", Value: "trailers"})
	if callHdr.PreviousAttempts > 0 {
		headerFields = append(headerFields, headerField{Name: "grpc-previous-rpc-attempts", Value: strconv.Itoa(callHdr.PreviousAttempts)})
	}
	if callHdr.SendCompress != "" {
		headerFields = append(headerFields, headerField{Name: "grpc-encoding", Value: callHdr.SendCompress})
		if !grpcutil.IsCompressorNameRegistered(callHdr.SendCompress) {
			if registeredCompressors != "" {
				registeredCompressors += ","
			}
			registeredCompressors += callHdr.SendCompress
		}
	}
	if registeredCompressors != "" {
		headerFields = append(headerFields, headerField{Name: "grpc-accept-encoding", Value: registeredCompressors})
	}
	if dl, ok := ctx.Deadline(); ok {
		// Send out timeout regardless its value. The server can detect timeout context by itself.
		timeout := time.Until(dl)
		if timeout <= 0 {
			return nil, status.Error(codes.DeadlineExceeded, context.DeadlineExceeded.Error())
		}
		headerFields = append(headerFields, headerField{Name: "grpc-timeout", Value: grpcutil.EncodeDuration(timeout)})
	}
	for k, v := range authData {
		headerFields = append(headerFields, headerField{Name: k, Value: encodeMetadataHeader(k, v)})
	}
	for k, v := range callAuthData {
		headerFields = append(headerFields, headerField{Name: k, Value: encodeMetadataHeader(k, v)})
	}
	if md, added, ok := metadataFromOutgoingContextRaw(ctx); ok {
		var k string
		for k, vv := range md {
			// HTTP doesn't allow you to set pseudoheaders after non pseudoheaders were set.
			if isReservedHeader(k) {
				continue
			}
			for _, v := range vv {
				headerFields = append(headerFields, headerField{Name: k, Value: encodeMetadataHeader(k, v)})
			}
		}
		for _, vv := range added {
			for i, v := range vv {
				if i%2 == 0 {
					k = strings.ToLower(v)
					continue
				}
				// HTTP doesn't allow you to set pseudoheaders after non pseudoheaders were set.
				if isReservedHeader(k) {
					continue
				}
				headerFields = append(headerFields, headerField{Name: k, Value: encodeMetadataHeader(k, v)})
			}
		}
	}
	return headerFields, nil
}

// reader reads the server's frames until the stream ends (http2Client.reader with handleData,
// handleRSTStream and operateHeaders).
func (s *clientTransportStream) reader() {
	for {
		kind, err := readFrameKind(s.conn)
		if err != nil {
			s.readFailed(err)
			return
		}
		switch kind {
		case frameHeader, frameTrailer:
			fields, err := readHeaderBlock(s.conn)
			if err != nil {
				s.readFailed(err)
				return
			}
			if s.operateHeaders(fields, kind == frameTrailer) {
				return
			}
		case frameData:
			m, err := readData(s.conn, s.maxRecv)
			if err != nil {
				s.readFailed(err)
				return
			}
			s.mu.Lock()
			s.bytesReceived = true
			ok := s.state != streamDone
			s.mu.Unlock()
			if ok {
				s.recv.put(m)
			}
		case frameReset:
			var cb [4]byte
			if err := readFull(s.conn, cb[:]); err != nil {
				s.readFailed(err)
				return
			}
			s.handleRSTStream(binary.BigEndian.Uint32(cb[:]))
			return
		default:
			s.readFailed(errMalformedFrame)
			return
		}
	}
}

// handleRSTStream is http2Client.handleRSTStream.
func (s *clientTransportStream) handleRSTStream(errCode uint32) {
	if errCode == errCodeRefusedStream {
		// The stream was unprocessed by the server.
		s.mu.Lock()
		s.unprocessed = true
		s.mu.Unlock()
	}
	statusCode := codes.Unknown
	if errCode < uint32(len(http2ErrConvTab)) {
		statusCode = http2ErrConvTab[errCode]
	}
	if statusCode == codes.Canceled {
		if d, ok := s.ctx.Deadline(); ok && !d.After(time.Now()) {
			// Our deadline was already exceeded, and that was likely the cause
			// of this cancellation.  Alter the status code accordingly.
			statusCode = codes.DeadlineExceeded
		}
	}
	st := status.Newf(statusCode, "stream terminated by RST_STREAM with error code: %v", errCodeString(errCode))
	s.closeStream(st.Err(), false, st, nil)
}

// readFailed ends the stream after its connection failed (http2Client.Close on a reader error).
func (s *clientTransportStream) readFailed(err error) {
	st := transportFailure(fmt.Sprintf("error reading from server: %v", err))
	s.closeStream(st.Err(), false, st, nil)
}

// operateHeaders is http2Client.operateHeaders on a header block; true if it ended the stream.
func (s *clientTransportStream) operateHeaders(fields []headerField, endStream bool) bool {
	s.mu.Lock()
	s.bytesReceived = true
	initialHeader := !s.headerChanClosed
	s.mu.Unlock()

	if !initialHeader && !endStream {
		// As specified by gRPC over HTTP2, a HEADERS frame (and associated CONTINUATION frames) can only appear at the start or end of a stream. Therefore, second HEADERS frame must have EOS bit set.
		st := status.New(codes.Internal, "a HEADERS frame cannot appear in the middle of a stream")
		s.closeStream(st.Err(), true, st, nil)
		return true
	}

	var (
		isGRPC         = !initialHeader
		mdata          = make(map[string][]string)
		contentTypeErr = "malformed header: missing HTTP content-type"
		grpcMessage    string
		recvCompress   string
		grpcStatusCode = codes.Unknown
		headerError    string
	)

	for _, hf := range fields {
		switch hf.Name {
		case "content-type":
			if _, validContentType := grpcutil.ContentSubtype(hf.Value); !validContentType {
				contentTypeErr = fmt.Sprintf("transport: received unexpected content-type %q", hf.Value)
				break
			}
			contentTypeErr = ""
			mdata[hf.Name] = append(mdata[hf.Name], hf.Value)
			isGRPC = true
		case "grpc-encoding":
			recvCompress = hf.Value
		case "grpc-status":
			code, err := strconv.ParseInt(hf.Value, 10, 32)
			if err != nil {
				se := status.New(codes.Unknown, fmt.Sprintf("transport: malformed grpc-status: %v", err))
				s.closeStream(se.Err(), true, se, nil)
				return true
			}
			grpcStatusCode = codes.Code(uint32(code))
		case "grpc-message":
			grpcMessage = decodeGrpcMessage(hf.Value)
		case ":status":
		default:
			if isReservedHeader(hf.Name) && !isWhitelistedHeader(hf.Name) {
				break
			}
			v, err := decodeMetadataHeader(hf.Name, hf.Value)
			if err != nil {
				headerError = fmt.Sprintf("transport: malformed %s: %v", hf.Name, err)
				break
			}
			mdata[hf.Name] = append(mdata[hf.Name], v)
		}
	}

	if !isGRPC {
		// The model's servers always send a gRPC content-type; a peer that does not is not one.
		se := status.New(codes.Internal, contentTypeErr)
		s.closeStream(se.Err(), true, se, nil)
		return true
	}

	if headerError != "" {
		se := status.New(codes.Internal, headerError)
		s.closeStream(se.Err(), true, se, nil)
		return true
	}

	if !endStream {
		s.mu.Lock()
		if !s.headerChanClosed {
			s.headerChanClosed = true
			s.headerValid = true
			s.recvCompress = recvCompress
			if len(mdata) > 0 {
				s.header = mdata
			}
			close(s.headerChan)
		}
		s.mu.Unlock()
		return false
	}

	st := istatus.NewWithProto(grpcStatusCode, grpcMessage, mdata[grpcStatusDetailsBinHeader])
	s.closeStream(io.EOF, false, st, mdata)
	return true
}

// closeStream ends the stream (http2Client.closeStream): its status and trailer, its end in the
// receive queue, the header channel closed if it was not. With rst, the server is told the client
// gave the stream up (RST_STREAM). The stream's connection is closed: it carries nothing else.
func (s *clientTransportStream) closeStream(err error, rst bool, st *status.Status, mdata map[string][]string) {
	s.mu.Lock()
	if s.state == streamDone {
		s.mu.Unlock()
		return
	}
	s.state = streamDone
	s.status = st
	if len(mdata) > 0 {
		s.trailer = mdata
	}
	if err != nil {
		s.recv.put(recvMsg{err: err})
	}
	if !s.headerChanClosed {
		s.headerChanClosed = true
		s.noHeaders = true
		close(s.headerChan)
	}
	close(s.done)
	s.mu.Unlock()
	if rst {
		s.wmu.Lock()
		s.conn.Write([]byte{frameCancel})
		s.wmu.Unlock()
	}
	s.conn.Close()
	s.cc.removeStream(s)
}

// Close ends the stream from the client's side (ClientStream.Close): if it is not done yet, with
// err's status and a RST_STREAM (err != nil) or none.
func (s *clientTransportStream) Close(err error) {
	s.closeStream(err, err != nil, status.Convert(err), nil)
}

// Write sends a message (hdr and data, if any) and, with opts.Last, the end of the request
// (http2Client.write). A failed write ends the stream, as the connection's failure does in
// grpc-go.
func (s *clientTransportStream) Write(hdr []byte, data mem.BufferSlice, opts *writeOptions) error {
	s.mu.Lock()
	if opts.Last {
		if s.state != streamActive {
			s.mu.Unlock()
			return errStreamDone
		}
		s.state = streamWriteDone
	} else if s.state != streamActive {
		s.mu.Unlock()
		return errStreamDone
	}
	s.mu.Unlock()
	var b []byte
	if hdr != nil || data.Len() != 0 {
		b = appendData(b, hdr, data.Materialize())
	}
	if opts.Last {
		b = append(b, frameClose)
	}
	s.wmu.Lock()
	_, err := s.conn.Write(b)
	s.wmu.Unlock()
	if err != nil {
		st := transportFailure(fmt.Sprintf("transport: %v", err))
		s.closeStream(st.Err(), false, st, nil)
		return err
	}
	return nil
}

// waitOnHeader waits for the header or the stream's end (ClientStream.waitOnHeader).
func (s *clientTransportStream) waitOnHeader() {
	select {
	case <-s.ctx.Done():
		s.Close(contextErr(s.ctx.Err()))
		<-s.headerChan
	case <-s.headerChan:
	}
}

// RecvCompress is ClientStream.RecvCompress.
func (s *clientTransportStream) RecvCompress() string {
	s.waitOnHeader()
	return s.recvCompress
}

// Done is ClientStream.Done.
func (s *clientTransportStream) Done() <-chan struct{} {
	return s.done
}

// Header is ClientStream.Header.
func (s *clientTransportStream) Header() (metadata.MD, error) {
	s.waitOnHeader()
	s.mu.Lock()
	defer s.mu.Unlock()
	if !s.headerValid || s.noHeaders {
		return nil, s.status.Err()
	}
	return metadata.MD(s.header).Copy(), nil
}

// TrailersOnly is ClientStream.TrailersOnly.
func (s *clientTransportStream) TrailersOnly() bool {
	s.waitOnHeader()
	s.mu.Lock()
	defer s.mu.Unlock()
	return s.noHeaders
}

// Trailer is Stream.Trailer: the trailer metadata, once the stream is done.
func (s *clientTransportStream) Trailer() metadata.MD {
	s.mu.Lock()
	defer s.mu.Unlock()
	return metadata.MD(s.trailer).Copy()
}

// Status is ClientStream.Status.
func (s *clientTransportStream) Status() *status.Status {
	s.mu.Lock()
	defer s.mu.Unlock()
	return s.status
}

// Context is Stream.Context.
func (s *clientTransportStream) Context() context.Context {
	return s.ctx
}

// Unprocessed is ClientStream.Unprocessed.
func (s *clientTransportStream) Unprocessed() bool {
	s.mu.Lock()
	defer s.mu.Unlock()
	return s.unprocessed
}

// BytesReceived is ClientStream.BytesReceived.
func (s *clientTransportStream) BytesReceived() bool {
	s.mu.Lock()
	defer s.mu.Unlock()
	return s.bytesReceived
}

// ReadMessageHeader reads the next message's 5-byte header (recvBufferReader.readMessageHeader for
// the client: a done context ends the stream first, and its error is read after what is queued).
func (s *clientTransportStream) ReadMessageHeader(header []byte) error {
	for {
		m, ok, ch := s.recv.take()
		if ok {
			return s.gotMessage(m, header)
		}
		select {
		case <-s.ctx.Done():
			s.closeStream(contextErr(s.ctx.Err()), true, status.Convert(contextErr(s.ctx.Err())), nil)
		case <-ch:
		}
	}
}

func (s *clientTransportStream) gotMessage(m recvMsg, header []byte) error {
	if m.err != nil {
		return m.err
	}
	copy(header, m.hdr[:])
	s.pending = m
	s.havePending = true
	return nil
}

// Read returns the payload of the message whose header ReadMessageHeader read.
func (s *clientTransportStream) Read(n int) (mem.BufferSlice, error) {
	if !s.havePending || len(s.pending.data) != n {
		return nil, io.ErrUnexpectedEOF
	}
	d := s.pending.data
	s.pending = recvMsg{}
	s.havePending = false
	return mem.BufferSlice{mem.SliceBuffer(d)}, nil
}

// ---------------------------------------------------------------------------------------------
// The server side.

// serverTransport is a served connection (transport.ServerTransport, http2Server): one stream.
type serverTransport struct {
	stats    stats.Handler // the server's stats handler (http2Server.stats), or nil
	conn     net.Conn
	peer     *peer.Peer
	maxRecv  int
	wmu      sync.Mutex // serializes the writes on conn
	done     chan struct{}
	mu       sync.Mutex
	draining bool
	closed   bool
	stream   *serverTransportStream // the dispatched stream, if any
}

func newServerTransport(conn net.Conn, maxRecv int, sh stats.Handler) *serverTransport {
	return &serverTransport{
		conn:    conn,
		peer:    &peer.Peer{Addr: conn.RemoteAddr(), LocalAddr: conn.LocalAddr()},
		maxRecv: maxRecv,
		stats:   sh,
		done:    make(chan struct{}),
	}
}

// Peer is ServerTransport.Peer.
func (t *serverTransport) Peer() *peer.Peer {
	return t.peer
}

// Drain is ServerTransport.Drain (GracefulStop's GOAWAY): a stream not yet dispatched is refused.
func (t *serverTransport) Drain(debugData string) {
	t.mu.Lock()
	t.draining = true
	t.mu.Unlock()
}

// Close is ServerTransport.Close: the connection is closed, its stream (if any) ends and its
// context is canceled.
func (t *serverTransport) Close(err error) {
	t.mu.Lock()
	if t.closed {
		t.mu.Unlock()
		return
	}
	t.closed = true
	s := t.stream
	close(t.done)
	t.mu.Unlock()
	t.conn.Close()
	if s != nil {
		s.closeStream(connectionError{Desc: err.Error()})
	}
}

func (t *serverTransport) write(b []byte) error {
	t.wmu.Lock()
	_, err := t.conn.Write(b)
	t.wmu.Unlock()
	if err != nil {
		t.conn.Close()
		return connectionError{Desc: fmt.Sprintf("transport: %v", err)}
	}
	return nil
}

// drainReads reads and drops what the client still sends, until it closes the connection (so
// that what the server wrote last is not lost to a reset when the server closes with unread data).
func (t *serverTransport) drainReads() {
	var b [4096]byte
	for {
		if _, err := t.conn.Read(b[:]); err != nil {
			return
		}
	}
}

// HandleStreams reads the connection's one stream (http2Server.HandleStreams and operateHeaders):
// its head; then it refuses the stream (GracefulStop's drain, or the model's choice: a stream of a
// connection over MaxConcurrentStreams, or above a GOAWAY's last stream id, is never dispatched)
// or dispatches it at most once, calling handle; then it reads the stream's messages, its end and
// its cancellation until the connection ends.
func (t *serverTransport) HandleStreams(ctx context.Context, handle func(*serverTransportStream)) {
	kind, err := readFrameKind(t.conn)
	if err != nil || kind != frameHead {
		return
	}
	fields, err := readHeaderBlock(t.conn)
	if err != nil {
		return
	}
	s, ok := t.operateHeaders(ctx, fields)
	if !ok {
		t.drainReads()
		return
	}
	handle(s)
	for {
		kind, err := readFrameKind(t.conn)
		if err != nil {
			s.closeStream(connectionError{Desc: err.Error()})
			return
		}
		switch kind {
		case frameData:
			m, err := readData(t.conn, t.maxRecv)
			if err != nil {
				s.closeStream(connectionError{Desc: err.Error()})
				return
			}
			s.mu.Lock()
			if s.state == streamReadDone {
				// handleData on a half-closed stream: RST_STREAM STREAM_CLOSED.
				s.mu.Unlock()
				s.closeStream(contextErr(context.Canceled))
				t.write(appendReset(nil, errCodeStreamClosed))
				continue
			}
			ok := s.state != streamDone
			s.mu.Unlock()
			if ok {
				s.recv.put(m)
			}
		case frameClose:
			s.mu.Lock()
			if s.state == streamActive {
				s.state = streamReadDone
				s.recv.put(recvMsg{err: io.EOF})
			}
			s.mu.Unlock()
		case frameCancel:
			// handleRSTStream: the stream ends and its context is canceled.
			s.closeStream(contextErr(context.Canceled))
		default:
			s.closeStream(connectionError{Desc: errMalformedFrame.Error()})
			return
		}
	}
}

// operateHeaders is http2Server.operateHeaders on the stream's head: the stream, dispatched (true),
// or refused or answered at once (false: an early abort, written here).
func (t *serverTransport) operateHeaders(ctx context.Context, fields []headerField) (*serverTransportStream, bool) {
	wireLen := 0
	for _, hf := range fields {
		wireLen += len(hf.Name) + len(hf.Value)
	}
	s := &serverTransportStream{
		st:               t,
		recv:             newRecvQueue(),
		headerWireLength: modelChooseLength(wireLen),
	}
	var (
		// if false, content-type was missing or invalid
		isGRPC      = false
		contentType = ""
		mdata       = make(metadata.MD, len(fields))
		httpMethod  string
		// these are set if an error is encountered while parsing the headers
		protocolError bool
		headerError   *status.Status

		timeoutSet bool
		timeout    time.Duration
	)

	for _, hf := range fields {
		switch hf.Name {
		case "content-type":
			contentSubtype, validContentType := grpcutil.ContentSubtype(hf.Value)
			if !validContentType {
				contentType = hf.Value
				break
			}
			mdata[hf.Name] = append(mdata[hf.Name], hf.Value)
			s.contentSubtype = contentSubtype
			isGRPC = true

		case "grpc-accept-encoding":
			mdata[hf.Name] = append(mdata[hf.Name], hf.Value)
			if hf.Value == "" {
				continue
			}
			compressors := hf.Value
			if s.clientAdvertisedCompressors != "" {
				compressors = s.clientAdvertisedCompressors + "," + compressors
			}
			s.clientAdvertisedCompressors = compressors
		case "grpc-encoding":
			s.recvCompress = hf.Value
		case ":method":
			httpMethod = hf.Value
		case ":path":
			s.method = hf.Value
		case "grpc-timeout":
			timeoutSet = true
			var err error
			if timeout, err = decodeTimeout(hf.Value); err != nil {
				headerError = status.Newf(codes.Internal, "malformed grpc-timeout: %v", err)
			}
		// "Transports must consider requests containing the Connection header
		// as malformed." - A41
		case "connection":
			protocolError = true
		default:
			if isReservedHeader(hf.Name) && !isWhitelistedHeader(hf.Name) {
				break
			}
			v, err := decodeMetadataHeader(hf.Name, hf.Value)
			if err != nil {
				headerError = status.Newf(codes.Internal, "malformed binary metadata %q in header %q: %v", hf.Value, hf.Name, err)
				break
			}
			mdata[hf.Name] = append(mdata[hf.Name], v)
		}
	}

	if len(mdata[":authority"]) > 1 || len(mdata["host"]) > 1 {
		errMsg := fmt.Sprintf("num values of :authority: %v, num values of host: %v, both must only have 1 value as per HTTP/2 spec", len(mdata[":authority"]), len(mdata["host"]))
		t.writeEarlyAbort(s.contentSubtype, status.New(codes.Internal, errMsg), 400)
		return nil, false
	}
	if protocolError {
		t.write(appendReset(nil, errCodeProtocol))
		return nil, false
	}
	if !isGRPC {
		t.writeEarlyAbort(s.contentSubtype, status.Newf(codes.InvalidArgument, "invalid gRPC request content-type %q", contentType), 415)
		return nil, false
	}
	if headerError != nil {
		t.writeEarlyAbort(s.contentSubtype, headerError, 400)
		return nil, false
	}

	// "If :authority is missing, Host must be renamed to :authority." - A41
	if len(mdata[":authority"]) == 0 {
		if host, ok := mdata["host"]; ok {
			mdata[":authority"] = host
			delete(mdata, "host")
		}
	} else {
		// "If :authority is present, Host must be discarded" - A41
		delete(mdata, "host")
	}
	if len(mdata[":authority"]) == 0 {
		t.writeEarlyAbort(s.contentSubtype, status.New(codes.Internal, "no host or :authority header present"), 400)
		return nil, false
	}

	if timeoutSet {
		s.ctx, s.cancel = context.WithTimeout(ctx, timeout)
	} else {
		s.ctx, s.cancel = context.WithCancel(ctx)
	}
	// Attach the received metadata to the context.
	if len(mdata) > 0 {
		s.ctx = metadata.NewIncomingContext(s.ctx, mdata)
	}

	t.mu.Lock()
	if t.closed {
		t.mu.Unlock()
		s.cancel()
		return nil, false
	}
	// The refusal: a stream of a draining connection, or (the model's choice) any stream not yet
	// dispatched (over MaxConcurrentStreams, or above a GOAWAY's last stream id).
	if t.draining || modelChoose() {
		t.mu.Unlock()
		s.cancel()
		t.write(appendReset(nil, errCodeRefusedStream))
		return nil, false
	}
	if httpMethod != "POST" {
		t.mu.Unlock()
		errMsg := fmt.Sprintf("Received a HEADERS frame with :method %q which should be POST", httpMethod)
		t.writeEarlyAbort(s.contentSubtype, status.New(codes.Internal, errMsg), 405)
		s.cancel()
		return nil, false
	}
	if s.ctx.Err() != nil {
		t.mu.Unlock()
		st := status.New(codes.DeadlineExceeded, context.DeadlineExceeded.Error())
		// Early abort in case the timeout was zero or so low it already fired.
		t.writeEarlyAbort(s.contentSubtype, st, 200)
		s.cancel()
		return nil, false
	}
	// Dispatched: final.
	t.stream = s
	t.mu.Unlock()
	if timeoutSet {
		// The stream ends when its deadline passes (operateHeaders' timer): RST_STREAM CANCEL.
		timer := time.AfterFunc(timeout, func() {
			s.closeStream(contextErr(context.DeadlineExceeded))
			t.write(appendReset(nil, errCodeCancel))
		})
		cancel := s.cancel
		s.cancel = func() {
			cancel()
			timer.Stop()
		}
	}
	return s, true
}

// writeEarlyAbort is http2Server.writeEarlyAbort: a trailers-only response for a stream that is
// not dispatched.
func (t *serverTransport) writeEarlyAbort(contentSubtype string, stat *status.Status, httpStatus uint32) {
	hf := []headerField{
		{Name: ":status", Value: strconv.Itoa(int(httpStatus))},
		{Name: "content-type", Value: grpcutil.ContentType(contentSubtype)},
		{Name: "grpc-status", Value: strconv.Itoa(int(stat.Code()))},
		{Name: "grpc-message", Value: encodeGrpcMessage(stat.Message())},
	}
	if p := istatus.RawStatusProto(stat); len(p.GetDetails()) > 0 {
		stBytes, err := proto.Marshal(p)
		if err == nil {
			hf = append(hf, headerField{Name: grpcStatusDetailsBinHeader, Value: encodeBinHeader(stBytes)})
		}
	}
	t.write(appendHeaderBlock(nil, frameTrailer, hf))
}

// serverTransportStream is a dispatched server stream (transport.ServerStream).
type serverTransportStream struct {
	st     *serverTransport
	ctx    context.Context
	cancel context.CancelFunc
	method string

	contentSubtype              string
	recvCompress                string
	sendCompress                string
	clientAdvertisedCompressors string

	recv        *recvQueue
	pending     recvMsg
	havePending bool

	hdrMu      sync.Mutex // guards header, trailer, headerSent
	header     metadata.MD
	trailer    metadata.MD
	headerSent bool

	// headerWireLength is the header block's wire length as stats.InHeader reports it (grpc-go's
	// HEADERS frame length; the model's choice, modelChooseLength).
	headerWireLength int

	mu    sync.Mutex
	state streamState
}

// closeStream ends the stream (http2Server.closeStream): its context is canceled, and readers see
// err after what is queued.
func (s *serverTransportStream) closeStream(err error) {
	s.mu.Lock()
	if s.state == streamDone {
		s.mu.Unlock()
		return
	}
	s.state = streamDone
	s.recv.put(recvMsg{err: err})
	s.mu.Unlock()
	s.cancel()
}

func (s *serverTransportStream) getState() streamState {
	s.mu.Lock()
	defer s.mu.Unlock()
	return s.state
}

// streamContextErr is http2Server.streamContextErr.
func (s *serverTransportStream) streamContextErr() error {
	select {
	case <-s.st.done:
		return errTransportClosing
	default:
	}
	return contextErr(s.ctx.Err())
}

// Method is ServerStream.Method.
func (s *serverTransportStream) Method() string {
	return s.method
}

// Context is Stream.Context.
func (s *serverTransportStream) Context() context.Context {
	return s.ctx
}

// SetContext is ServerStream.SetContext.
func (s *serverTransportStream) SetContext(ctx context.Context) {
	s.ctx = ctx
}

// HeaderWireLength is ServerStream.HeaderWireLength: the header block's wire length, the model's
// choice (headerWireLength).
func (s *serverTransportStream) HeaderWireLength() int {
	return s.headerWireLength
}

// RecvCompress is ServerStream.RecvCompress.
func (s *serverTransportStream) RecvCompress() string {
	return s.recvCompress
}

// SendCompress is ServerStream.SendCompress.
func (s *serverTransportStream) SendCompress() string {
	return s.sendCompress
}

// ContentSubtype is ServerStream.ContentSubtype.
func (s *serverTransportStream) ContentSubtype() string {
	return s.contentSubtype
}

// SetSendCompress is ServerStream.SetSendCompress.
func (s *serverTransportStream) SetSendCompress(name string) error {
	s.hdrMu.Lock()
	sent := s.headerSent
	s.hdrMu.Unlock()
	if sent || s.getState() == streamDone {
		return errors.New("transport: set send compressor called after headers sent or stream done")
	}
	s.sendCompress = name
	return nil
}

// ClientAdvertisedCompressors is ServerStream.ClientAdvertisedCompressors.
func (s *serverTransportStream) ClientAdvertisedCompressors() []string {
	values := strings.Split(s.clientAdvertisedCompressors, ",")
	for i, v := range values {
		values[i] = strings.TrimSpace(v)
	}
	return values
}

// Header is ServerStream.Header.
func (s *serverTransportStream) Header() (metadata.MD, error) {
	s.hdrMu.Lock()
	defer s.hdrMu.Unlock()
	return s.header.Copy(), nil
}

// SetHeader is ServerStream.SetHeader.
func (s *serverTransportStream) SetHeader(md metadata.MD) error {
	if md.Len() == 0 {
		return nil
	}
	s.hdrMu.Lock()
	defer s.hdrMu.Unlock()
	if s.headerSent || s.getState() == streamDone {
		return errIllegalHeaderWrite
	}
	s.header = metadata.Join(s.header, md)
	return nil
}

// SetTrailer is ServerStream.SetTrailer.
func (s *serverTransportStream) SetTrailer(md metadata.MD) error {
	if md.Len() == 0 {
		return nil
	}
	if s.getState() == streamDone {
		return errIllegalHeaderWrite
	}
	s.hdrMu.Lock()
	s.trailer = metadata.Join(s.trailer, md)
	s.hdrMu.Unlock()
	return nil
}

// SendHeader is ServerStream.SendHeader (http2Server.writeHeader).
func (s *serverTransportStream) SendHeader(md metadata.MD) error {
	s.hdrMu.Lock()
	defer s.hdrMu.Unlock()
	if s.getState() == streamDone {
		return s.streamContextErr()
	}
	if s.headerSent {
		return errIllegalHeaderWrite
	}
	s.headerSent = true
	if md.Len() > 0 {
		if s.header.Len() > 0 {
			s.header = metadata.Join(s.header, md)
		} else {
			s.header = md
		}
	}
	if err := s.writeHeaderLocked(); err != nil {
		switch e := err.(type) {
		case connectionError:
			return status.Error(codes.Unavailable, e.Desc)
		default:
			return status.Convert(err).Err()
		}
	}
	return nil
}

// writeHeaderLocked is http2Server.writeHeaderLocked.
func (s *serverTransportStream) writeHeaderLocked() error {
	headerFields := make([]headerField, 0, 2)
	headerFields = append(headerFields, headerField{Name: ":status", Value: "200"})
	headerFields = append(headerFields, headerField{Name: "content-type", Value: grpcutil.ContentType(s.contentSubtype)})
	if s.sendCompress != "" {
		headerFields = append(headerFields, headerField{Name: "grpc-encoding", Value: s.sendCompress})
	}
	headerFields = appendHeaderFieldsFromMD(headerFields, s.header)
	if err := s.st.write(appendHeaderBlock(nil, frameHeader, headerFields)); err != nil {
		s.closeStream(err)
		return err
	}
	if s.st.stats != nil {
		// Note: Headers are compressed with hpack after this call returns.
		// No WireLength field is set here.
		s.st.stats.HandleRPC(s.Context(), &stats.OutHeader{
			Header:      s.header.Copy(),
			Compression: s.sendCompress,
		})
	}
	return nil
}

// WriteStatus is ServerStream.WriteStatus (http2Server.writeStatus): the trailer, after the header
// if it was not sent; the stream is then done (and its context canceled).
func (s *serverTransportStream) WriteStatus(st *status.Status) error {
	s.hdrMu.Lock()
	defer s.hdrMu.Unlock()

	if s.getState() == streamDone {
		return nil
	}

	headerFields := make([]headerField, 0, 2)
	if !s.headerSent { // No headers have been sent.
		s.headerSent = true
		if len(s.header) > 0 { // Send a separate header frame.
			if err := s.writeHeaderLocked(); err != nil {
				return err
			}
		} else { // Send a trailer only response.
			headerFields = append(headerFields, headerField{Name: ":status", Value: "200"})
			headerFields = append(headerFields, headerField{Name: "content-type", Value: grpcutil.ContentType(s.contentSubtype)})
		}
	}
	headerFields = append(headerFields, headerField{Name: "grpc-status", Value: strconv.Itoa(int(st.Code()))})
	headerFields = append(headerFields, headerField{Name: "grpc-message", Value: encodeGrpcMessage(st.Message())})

	if p := istatus.RawStatusProto(st); len(p.GetDetails()) > 0 {
		// Do not use the user's grpc-status-details-bin (if present) if we are
		// even attempting to set our own.
		delete(s.trailer, grpcStatusDetailsBinHeader)
		stBytes, err := proto.Marshal(p)
		if err == nil {
			headerFields = append(headerFields, headerField{Name: grpcStatusDetailsBinHeader, Value: encodeBinHeader(stBytes)})
		}
	}

	// Attach the trailer metadata.
	headerFields = appendHeaderFieldsFromMD(headerFields, s.trailer)
	err := s.st.write(appendHeaderBlock(nil, frameTrailer, headerFields))
	s.closeStream(contextErr(context.Canceled))
	if err == nil && s.st.stats != nil {
		// Note: The trailer fields are compressed with hpack after this call returns.
		// No WireLength field is set here.
		s.st.stats.HandleRPC(s.Context(), &stats.OutTrailer{
			Trailer: s.trailer.Copy(),
		})
	}
	return err
}

// Write is ServerStream.Write (http2Server.write): the header first if it was not sent.
func (s *serverTransportStream) Write(hdr []byte, data mem.BufferSlice, _ *writeOptions) error {
	s.hdrMu.Lock()
	if !s.headerSent {
		s.hdrMu.Unlock()
		if err := s.SendHeader(nil); err != nil {
			return err
		}
	} else {
		s.hdrMu.Unlock()
		if s.getState() == streamDone {
			return s.streamContextErr()
		}
	}
	if s.getState() == streamDone {
		return s.streamContextErr()
	}
	if err := s.st.write(appendData(nil, hdr, data.Materialize())); err != nil {
		s.closeStream(err)
		return err
	}
	return nil
}

// ReadMessageHeader reads the next message's 5-byte header (recvBufferReader.readMessageHeader for
// the server: a done context's error at once).
func (s *serverTransportStream) ReadMessageHeader(header []byte) error {
	for {
		m, ok, ch := s.recv.take()
		if ok {
			if m.err != nil {
				return m.err
			}
			copy(header, m.hdr[:])
			s.pending = m
			s.havePending = true
			return nil
		}
		select {
		case <-s.ctx.Done():
			return contextErr(s.ctx.Err())
		case <-ch:
		}
	}
}

// Read returns the payload of the message whose header ReadMessageHeader read.
func (s *serverTransportStream) Read(n int) (mem.BufferSlice, error) {
	if !s.havePending || len(s.pending.data) != n {
		return nil, io.ErrUnexpectedEOF
	}
	d := s.pending.data
	s.pending = recvMsg{}
	s.havePending = false
	return mem.BufferSlice{mem.SliceBuffer(d)}, nil
}
