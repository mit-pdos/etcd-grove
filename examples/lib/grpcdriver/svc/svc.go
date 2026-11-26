// Package svc is grpcdriver's service, written as protoc-gen-go-grpc v1.5 generates one (the
// generic stream wrappers, StaticMethod, the ServiceDesc), over protobuf's StringValue: the
// unary methods Echo, Fail and Meta, and one method of each stream kind.
package svc

import (
	"context"

	"google.golang.org/grpc"
	"google.golang.org/protobuf/types/known/wrapperspb"
)

// Msg is the service's message type.
type Msg = wrapperspb.StringValue

const (
	Driver_Echo_FullMethodName         = "/grpcdriver.Driver/Echo"
	Driver_Fail_FullMethodName         = "/grpcdriver.Driver/Fail"
	Driver_Meta_FullMethodName         = "/grpcdriver.Driver/Meta"
	Driver_ServerStream_FullMethodName = "/grpcdriver.Driver/ServerStream"
	Driver_ClientStream_FullMethodName = "/grpcdriver.Driver/ClientStream"
	Driver_Bidi_FullMethodName         = "/grpcdriver.Driver/Bidi"
)

// DriverClient is the client API.
type DriverClient interface {
	Echo(ctx context.Context, in *Msg, opts ...grpc.CallOption) (*Msg, error)
	Fail(ctx context.Context, in *Msg, opts ...grpc.CallOption) (*Msg, error)
	Meta(ctx context.Context, in *Msg, opts ...grpc.CallOption) (*Msg, error)
	ServerStream(ctx context.Context, in *Msg, opts ...grpc.CallOption) (grpc.ServerStreamingClient[Msg], error)
	ClientStream(ctx context.Context, opts ...grpc.CallOption) (grpc.ClientStreamingClient[Msg, Msg], error)
	Bidi(ctx context.Context, opts ...grpc.CallOption) (grpc.BidiStreamingClient[Msg, Msg], error)
}

type driverClient struct {
	cc grpc.ClientConnInterface
}

// NewDriverClient is the generated constructor.
func NewDriverClient(cc grpc.ClientConnInterface) DriverClient {
	return &driverClient{cc}
}

func (c *driverClient) unary(ctx context.Context, method string, in *Msg, opts []grpc.CallOption) (*Msg, error) {
	cOpts := append([]grpc.CallOption{grpc.StaticMethod()}, opts...)
	out := new(Msg)
	err := c.cc.Invoke(ctx, method, in, out, cOpts...)
	if err != nil {
		return nil, err
	}
	return out, nil
}

func (c *driverClient) Echo(ctx context.Context, in *Msg, opts ...grpc.CallOption) (*Msg, error) {
	return c.unary(ctx, Driver_Echo_FullMethodName, in, opts)
}

func (c *driverClient) Fail(ctx context.Context, in *Msg, opts ...grpc.CallOption) (*Msg, error) {
	return c.unary(ctx, Driver_Fail_FullMethodName, in, opts)
}

func (c *driverClient) Meta(ctx context.Context, in *Msg, opts ...grpc.CallOption) (*Msg, error) {
	return c.unary(ctx, Driver_Meta_FullMethodName, in, opts)
}

func (c *driverClient) ServerStream(ctx context.Context, in *Msg, opts ...grpc.CallOption) (grpc.ServerStreamingClient[Msg], error) {
	cOpts := append([]grpc.CallOption{grpc.StaticMethod()}, opts...)
	stream, err := c.cc.NewStream(ctx, &Driver_ServiceDesc.Streams[0], Driver_ServerStream_FullMethodName, cOpts...)
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

func (c *driverClient) ClientStream(ctx context.Context, opts ...grpc.CallOption) (grpc.ClientStreamingClient[Msg, Msg], error) {
	cOpts := append([]grpc.CallOption{grpc.StaticMethod()}, opts...)
	stream, err := c.cc.NewStream(ctx, &Driver_ServiceDesc.Streams[1], Driver_ClientStream_FullMethodName, cOpts...)
	if err != nil {
		return nil, err
	}
	return &grpc.GenericClientStream[Msg, Msg]{ClientStream: stream}, nil
}

func (c *driverClient) Bidi(ctx context.Context, opts ...grpc.CallOption) (grpc.BidiStreamingClient[Msg, Msg], error) {
	cOpts := append([]grpc.CallOption{grpc.StaticMethod()}, opts...)
	stream, err := c.cc.NewStream(ctx, &Driver_ServiceDesc.Streams[2], Driver_Bidi_FullMethodName, cOpts...)
	if err != nil {
		return nil, err
	}
	return &grpc.GenericClientStream[Msg, Msg]{ClientStream: stream}, nil
}

// DriverServer is the server API.
type DriverServer interface {
	Echo(context.Context, *Msg) (*Msg, error)
	Fail(context.Context, *Msg) (*Msg, error)
	Meta(context.Context, *Msg) (*Msg, error)
	ServerStream(*Msg, grpc.ServerStreamingServer[Msg]) error
	ClientStream(grpc.ClientStreamingServer[Msg, Msg]) error
	Bidi(grpc.BidiStreamingServer[Msg, Msg]) error
}

// RegisterDriverServer is the generated registration.
func RegisterDriverServer(s grpc.ServiceRegistrar, srv DriverServer) {
	s.RegisterService(&Driver_ServiceDesc, srv)
}

func _Driver_Echo_Handler(srv interface{}, ctx context.Context, dec func(interface{}) error, interceptor grpc.UnaryServerInterceptor) (interface{}, error) {
	in := new(Msg)
	if err := dec(in); err != nil {
		return nil, err
	}
	if interceptor == nil {
		return srv.(DriverServer).Echo(ctx, in)
	}
	info := &grpc.UnaryServerInfo{Server: srv, FullMethod: Driver_Echo_FullMethodName}
	handler := func(ctx context.Context, req interface{}) (interface{}, error) {
		return srv.(DriverServer).Echo(ctx, req.(*Msg))
	}
	return interceptor(ctx, in, info, handler)
}

func _Driver_Fail_Handler(srv interface{}, ctx context.Context, dec func(interface{}) error, interceptor grpc.UnaryServerInterceptor) (interface{}, error) {
	in := new(Msg)
	if err := dec(in); err != nil {
		return nil, err
	}
	if interceptor == nil {
		return srv.(DriverServer).Fail(ctx, in)
	}
	info := &grpc.UnaryServerInfo{Server: srv, FullMethod: Driver_Fail_FullMethodName}
	handler := func(ctx context.Context, req interface{}) (interface{}, error) {
		return srv.(DriverServer).Fail(ctx, req.(*Msg))
	}
	return interceptor(ctx, in, info, handler)
}

func _Driver_Meta_Handler(srv interface{}, ctx context.Context, dec func(interface{}) error, interceptor grpc.UnaryServerInterceptor) (interface{}, error) {
	in := new(Msg)
	if err := dec(in); err != nil {
		return nil, err
	}
	if interceptor == nil {
		return srv.(DriverServer).Meta(ctx, in)
	}
	info := &grpc.UnaryServerInfo{Server: srv, FullMethod: Driver_Meta_FullMethodName}
	handler := func(ctx context.Context, req interface{}) (interface{}, error) {
		return srv.(DriverServer).Meta(ctx, req.(*Msg))
	}
	return interceptor(ctx, in, info, handler)
}

func _Driver_ServerStream_Handler(srv interface{}, stream grpc.ServerStream) error {
	m := new(Msg)
	if err := stream.RecvMsg(m); err != nil {
		return err
	}
	return srv.(DriverServer).ServerStream(m, &grpc.GenericServerStream[Msg, Msg]{ServerStream: stream})
}

func _Driver_ClientStream_Handler(srv interface{}, stream grpc.ServerStream) error {
	return srv.(DriverServer).ClientStream(&grpc.GenericServerStream[Msg, Msg]{ServerStream: stream})
}

func _Driver_Bidi_Handler(srv interface{}, stream grpc.ServerStream) error {
	return srv.(DriverServer).Bidi(&grpc.GenericServerStream[Msg, Msg]{ServerStream: stream})
}

// Driver_ServiceDesc is the service's descriptor.
var Driver_ServiceDesc = grpc.ServiceDesc{
	ServiceName: "grpcdriver.Driver",
	HandlerType: (*DriverServer)(nil),
	Methods: []grpc.MethodDesc{
		{MethodName: "Echo", Handler: _Driver_Echo_Handler},
		{MethodName: "Fail", Handler: _Driver_Fail_Handler},
		{MethodName: "Meta", Handler: _Driver_Meta_Handler},
	},
	Streams: []grpc.StreamDesc{
		{StreamName: "ServerStream", Handler: _Driver_ServerStream_Handler, ServerStreams: true},
		{StreamName: "ClientStream", Handler: _Driver_ClientStream_Handler, ClientStreams: true},
		{StreamName: "Bidi", Handler: _Driver_Bidi_Handler, ServerStreams: true, ClientStreams: true},
	},
	Metadata: "grpcdriver.proto",
}
