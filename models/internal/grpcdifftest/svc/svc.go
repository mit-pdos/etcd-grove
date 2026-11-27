// Package svc is the differential test's service: the four kinds of RPC (unary, server streaming,
// client streaming, bidirectional) over protobuf's StringValue, written as protoc-gen-go-grpc
// v1.5 generates a service (the generic stream wrappers, StaticMethod, the ServiceDesc), and a
// server whose behavior each request names, which records what each handler saw.
package svc

import (
	"context"
	"fmt"
	"io"
	"strconv"
	"strings"
	"sync"
	"time"

	"google.golang.org/grpc"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/metadata"
	"google.golang.org/grpc/peer"
	"google.golang.org/grpc/status"
	"google.golang.org/protobuf/types/known/wrapperspb"
)

// Msg is the service's message type.
type Msg = wrapperspb.StringValue

// M makes a message.
func M(s string) *Msg { return wrapperspb.String(s) }

const (
	Echo_Unary_FullMethodName        = "/difftest.Echo/Unary"
	Echo_ServerStream_FullMethodName = "/difftest.Echo/ServerStream"
	Echo_ClientStream_FullMethodName = "/difftest.Echo/ClientStream"
	Echo_Bidi_FullMethodName         = "/difftest.Echo/Bidi"
)

// EchoClient is the client API.
type EchoClient interface {
	Unary(ctx context.Context, in *Msg, opts ...grpc.CallOption) (*Msg, error)
	ServerStream(ctx context.Context, in *Msg, opts ...grpc.CallOption) (grpc.ServerStreamingClient[Msg], error)
	ClientStream(ctx context.Context, opts ...grpc.CallOption) (grpc.ClientStreamingClient[Msg, Msg], error)
	Bidi(ctx context.Context, opts ...grpc.CallOption) (grpc.BidiStreamingClient[Msg, Msg], error)
}

type echoClient struct {
	cc grpc.ClientConnInterface
}

// NewEchoClient is the generated constructor.
func NewEchoClient(cc grpc.ClientConnInterface) EchoClient {
	return &echoClient{cc}
}

func (c *echoClient) Unary(ctx context.Context, in *Msg, opts ...grpc.CallOption) (*Msg, error) {
	cOpts := append([]grpc.CallOption{grpc.StaticMethod()}, opts...)
	out := new(Msg)
	err := c.cc.Invoke(ctx, Echo_Unary_FullMethodName, in, out, cOpts...)
	if err != nil {
		return nil, err
	}
	return out, nil
}

func (c *echoClient) ServerStream(ctx context.Context, in *Msg, opts ...grpc.CallOption) (grpc.ServerStreamingClient[Msg], error) {
	cOpts := append([]grpc.CallOption{grpc.StaticMethod()}, opts...)
	stream, err := c.cc.NewStream(ctx, &Echo_ServiceDesc.Streams[0], Echo_ServerStream_FullMethodName, cOpts...)
	if err != nil {
		return nil, err
	}
	x := &grpc.GenericClientStream[Msg, Msg]{ClientStream: stream}
	if err := x.ClientStream.SendMsg(in); err != nil {
		return nil, err
	}
	if err := x.ClientStream.CloseSend(); err != nil {
		return nil, err
	}
	return x, nil
}

func (c *echoClient) ClientStream(ctx context.Context, opts ...grpc.CallOption) (grpc.ClientStreamingClient[Msg, Msg], error) {
	cOpts := append([]grpc.CallOption{grpc.StaticMethod()}, opts...)
	stream, err := c.cc.NewStream(ctx, &Echo_ServiceDesc.Streams[1], Echo_ClientStream_FullMethodName, cOpts...)
	if err != nil {
		return nil, err
	}
	x := &grpc.GenericClientStream[Msg, Msg]{ClientStream: stream}
	return x, nil
}

func (c *echoClient) Bidi(ctx context.Context, opts ...grpc.CallOption) (grpc.BidiStreamingClient[Msg, Msg], error) {
	cOpts := append([]grpc.CallOption{grpc.StaticMethod()}, opts...)
	stream, err := c.cc.NewStream(ctx, &Echo_ServiceDesc.Streams[2], Echo_Bidi_FullMethodName, cOpts...)
	if err != nil {
		return nil, err
	}
	x := &grpc.GenericClientStream[Msg, Msg]{ClientStream: stream}
	return x, nil
}

// EchoServer is the server API.
type EchoServer interface {
	Unary(context.Context, *Msg) (*Msg, error)
	ServerStream(*Msg, grpc.ServerStreamingServer[Msg]) error
	ClientStream(grpc.ClientStreamingServer[Msg, Msg]) error
	Bidi(grpc.BidiStreamingServer[Msg, Msg]) error
}

// RegisterEchoServer is the generated registration.
func RegisterEchoServer(s grpc.ServiceRegistrar, srv EchoServer) {
	s.RegisterService(&Echo_ServiceDesc, srv)
}

func _Echo_Unary_Handler(srv interface{}, ctx context.Context, dec func(interface{}) error, interceptor grpc.UnaryServerInterceptor) (interface{}, error) {
	in := new(Msg)
	if err := dec(in); err != nil {
		return nil, err
	}
	if interceptor == nil {
		return srv.(EchoServer).Unary(ctx, in)
	}
	info := &grpc.UnaryServerInfo{
		Server:     srv,
		FullMethod: Echo_Unary_FullMethodName,
	}
	handler := func(ctx context.Context, req interface{}) (interface{}, error) {
		return srv.(EchoServer).Unary(ctx, req.(*Msg))
	}
	return interceptor(ctx, in, info, handler)
}

func _Echo_ServerStream_Handler(srv interface{}, stream grpc.ServerStream) error {
	m := new(Msg)
	if err := stream.RecvMsg(m); err != nil {
		return err
	}
	return srv.(EchoServer).ServerStream(m, &grpc.GenericServerStream[Msg, Msg]{ServerStream: stream})
}

func _Echo_ClientStream_Handler(srv interface{}, stream grpc.ServerStream) error {
	return srv.(EchoServer).ClientStream(&grpc.GenericServerStream[Msg, Msg]{ServerStream: stream})
}

func _Echo_Bidi_Handler(srv interface{}, stream grpc.ServerStream) error {
	return srv.(EchoServer).Bidi(&grpc.GenericServerStream[Msg, Msg]{ServerStream: stream})
}

// Echo_ServiceDesc is the service's descriptor.
var Echo_ServiceDesc = grpc.ServiceDesc{
	ServiceName: "difftest.Echo",
	HandlerType: (*EchoServer)(nil),
	Methods: []grpc.MethodDesc{
		{MethodName: "Unary", Handler: _Echo_Unary_Handler},
	},
	Streams: []grpc.StreamDesc{
		{StreamName: "ServerStream", Handler: _Echo_ServerStream_Handler, ServerStreams: true},
		{StreamName: "ClientStream", Handler: _Echo_ClientStream_Handler, ClientStreams: true},
		{StreamName: "Bidi", Handler: _Echo_Bidi_Handler, ServerStreams: true, ClientStreams: true},
	},
	Metadata: "difftest.proto",
}

// Seen is what a handler saw of its call.
type Seen struct {
	Runs        int
	MD          metadata.MD // the incoming metadata (user-agent's version part removed)
	HasDeadline bool
	HasPeer     bool
	PeerLocal   string
	CtxErr      error // the context's error when the handler returned
	Method      string
}

// Server is the test server. A request's value is a command: its first word is its id (each
// call's is fresh), the rest what the handler does:
//
//	echo X            reply X
//	err CODE MSG      return status.Error(CODE, MSG)
//	plain MSG         return errors.New(MSG)
//	ctxerr            return ctx.Err() after the context is done
//	block             wait for the context to be done, then return its status
//	md                set header k=h and trailer k=t (SetHeader/SetTrailer), reply "md"
//	sendheader        SendHeader twice (the second's error code is the reply)
//	big N             reply N bytes
//	slow D X          sleep D (a duration), reply X
//	hdronly CODE      set a header, then fail with CODE (header frame, then trailer)
//	bighdr N          SendHeader with a header of N bytes (its error is the reply)
//	bigtrl N          set a trailer of N bytes, reply "bigtrl"
//
// Streams: ServerStream sends "1".."N" for "stream N" (then the status of the rest, as above);
// ClientStream replies with the received values joined by ","; Bidi echoes each message until the
// client closes, and fails as "err" does when a message is "err CODE MSG".
type Server struct {
	mu   sync.Mutex
	seen map[string]*Seen
	// Started is signaled with a call's id when its handler starts.
	Started chan string
}

// New makes a test server.
func New() *Server {
	return &Server{seen: make(map[string]*Seen), Started: make(chan string, 1000)}
}

// Seen returns what the handler of id saw (nil if it never ran).
func (s *Server) Seen(id string) *Seen {
	s.mu.Lock()
	defer s.mu.Unlock()
	if x, ok := s.seen[id]; ok {
		c := *x
		return &c
	}
	return nil
}

// Runs is how many times id's handler ran.
func (s *Server) Runs(id string) int {
	if x := s.Seen(id); x != nil {
		return x.Runs
	}
	return 0
}

func (s *Server) record(ctx context.Context, id string) func() {
	md, _ := metadata.FromIncomingContext(ctx)
	md = md.Copy()
	if ua := md.Get("user-agent"); len(ua) == 1 {
		md.Set("user-agent", ua[0])
	}
	_, hasDL := ctx.Deadline()
	p, hasPeer := peer.FromContext(ctx)
	local := ""
	if hasPeer && p.LocalAddr != nil {
		local = p.LocalAddr.String()
	}
	method, _ := grpc.Method(ctx)
	s.mu.Lock()
	x, ok := s.seen[id]
	if !ok {
		x = &Seen{}
		s.seen[id] = x
	}
	x.Runs++
	x.MD = md
	x.HasDeadline = hasDL
	x.HasPeer = hasPeer && p.Addr != nil
	x.PeerLocal = local
	x.Method = method
	s.mu.Unlock()
	select {
	case s.Started <- id:
	default:
	}
	return func() {
		s.mu.Lock()
		x.CtxErr = ctx.Err()
		s.mu.Unlock()
	}
}

func split(v string) (string, string, string) {
	f := strings.SplitN(v, " ", 3)
	for len(f) < 3 {
		f = append(f, "")
	}
	return f[0], f[1], f[2]
}

// run performs a command; ok false if the command is not one of the reply commands.
func run(ctx context.Context, cmd, arg string) (*Msg, error) {
	switch cmd {
	case "echo":
		return M(arg), nil
	case "err":
		c, rest, _ := strings.Cut(arg, " ")
		n, _ := strconv.Atoi(c)
		return nil, status.Error(codes.Code(n), rest)
	case "plain":
		return nil, fmt.Errorf("%s", arg)
	case "ctxerr":
		<-ctx.Done()
		return nil, ctx.Err()
	case "block":
		<-ctx.Done()
		return nil, status.FromContextError(ctx.Err()).Err()
	case "md":
		grpc.SetHeader(ctx, metadata.Pairs("k", "h", "k-bin", "\x00\xff"))
		grpc.SetTrailer(ctx, metadata.Pairs("k", "t"))
		return M("md"), nil
	case "sendheader":
		if err := grpc.SendHeader(ctx, metadata.Pairs("k", "1")); err != nil {
			return nil, err
		}
		err := grpc.SendHeader(ctx, metadata.Pairs("k", "2"))
		return M(fmt.Sprintf("%v|%v", status.Code(err), err)), nil
	case "big":
		n, _ := strconv.Atoi(arg)
		return M(strings.Repeat("x", n)), nil
	case "slow":
		d, x, _ := strings.Cut(arg, " ")
		dd, _ := time.ParseDuration(d)
		select {
		case <-time.After(dd):
		case <-ctx.Done():
		}
		return M(x), nil
	case "bighdr":
		n, _ := strconv.Atoi(arg)
		err := grpc.SendHeader(ctx, metadata.Pairs("h", strings.Repeat("v", n)))
		return M(fmt.Sprintf("%v", err)), nil
	case "bigtrl":
		n, _ := strconv.Atoi(arg)
		grpc.SetTrailer(ctx, metadata.Pairs("t", strings.Repeat("v", n)))
		return M("bigtrl"), nil
	case "hdronly":
		grpc.SetHeader(ctx, metadata.Pairs("k", "h"))
		n, _ := strconv.Atoi(arg)
		return nil, status.Error(codes.Code(n), "after header")
	}
	return nil, status.Error(codes.InvalidArgument, "unknown command "+cmd)
}

// Unary runs the request's command.
func (s *Server) Unary(ctx context.Context, in *Msg) (*Msg, error) {
	id, cmd, arg := split(in.GetValue())
	defer s.record(ctx, id)()
	return run(ctx, cmd, arg)
}

// ServerStream sends "1".."N" for "stream N", then runs "then" commands.
func (s *Server) ServerStream(in *Msg, stream grpc.ServerStreamingServer[Msg]) error {
	id, cmd, arg := split(in.GetValue())
	defer s.record(stream.Context(), id)()
	if cmd == "stream" {
		n, _ := strconv.Atoi(arg)
		stream.SetHeader(metadata.Pairs("sh", "1"))
		for i := 1; i <= n; i++ {
			if err := stream.Send(M(strconv.Itoa(i))); err != nil {
				return err
			}
		}
		stream.SetTrailer(metadata.Pairs("st", "1"))
		return nil
	}
	if cmd == "forever" {
		for i := 1; ; i++ {
			if err := stream.Send(M(strconv.Itoa(i))); err != nil {
				return err
			}
			time.Sleep(time.Millisecond)
		}
	}
	r, err := run(stream.Context(), cmd, arg)
	if err != nil {
		return err
	}
	return stream.Send(r)
}

// ClientStream joins what it receives.
func (s *Server) ClientStream(stream grpc.ClientStreamingServer[Msg, Msg]) error {
	var got []string
	var done func()
	for {
		m, err := stream.Recv()
		if err == io.EOF {
			break
		}
		if err != nil {
			if done != nil {
				done()
			}
			return err
		}
		if done == nil {
			id, _, _ := split(m.GetValue())
			done = s.record(stream.Context(), id)
		}
		got = append(got, m.GetValue())
		if _, cmd, arg := split(m.GetValue()); cmd == "err" {
			done()
			_, err := run(stream.Context(), cmd, arg)
			return err
		}
	}
	if done != nil {
		done()
	}
	return stream.SendAndClose(M(strings.Join(got, ",")))
}

// Bidi echoes.
func (s *Server) Bidi(stream grpc.BidiStreamingServer[Msg, Msg]) error {
	var done func()
	defer func() {
		if done != nil {
			done()
		}
	}()
	for {
		m, err := stream.Recv()
		if err == io.EOF {
			return nil
		}
		if err != nil {
			return err
		}
		id, cmd, arg := split(m.GetValue())
		if done == nil {
			done = s.record(stream.Context(), id)
		}
		if cmd == "err" {
			_, err := run(stream.Context(), cmd, arg)
			return err
		}
		if err := stream.Send(M(arg)); err != nil {
			return err
		}
	}
}
