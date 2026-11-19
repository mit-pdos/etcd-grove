package grpc

import (
	"context"

	"google.golang.org/grpc/credentials"
)

// The SupportPackageIsVersion constants are referenced from generated code (as the real ones).
const (
	SupportPackageIsVersion3 = true
	SupportPackageIsVersion4 = true
	SupportPackageIsVersion5 = true
	SupportPackageIsVersion6 = true
	SupportPackageIsVersion7 = true
	SupportPackageIsVersion8 = true
	SupportPackageIsVersion9 = true
)

// A DialOption configures how a connection is set up (the real one is an interface; the model's
// values are the options of the subset).
type DialOption struct {
	creds bool // transport credentials were set (the model's are insecure's)
}

// WithInsecure returns a DialOption which disables transport security (deprecated in the real
// module, equivalent to WithTransportCredentials(insecure.NewCredentials())).
func WithInsecure() DialOption {
	return DialOption{creds: true}
}

// WithTransportCredentials returns a DialOption which configures transport credentials; the
// model's only credentials are insecure.NewCredentials()'s.
func WithTransportCredentials(creds credentials.TransportCredentials) DialOption {
	return DialOption{creds: true}
}

// WithBlock is accepted and ignored: the model's Dial connects lazily (a real blocking Dial
// returns once connected, or fails with its context; the model's first call connects instead).
func WithBlock() DialOption {
	return DialOption{creds: false}
}

// A CallOption configures a call (the real one is an interface). The model ignores call
// options: the subset's (StaticMethod, WaitForReady) do not change what a call can return.
type CallOption struct{}

// StaticMethod is the call option newer generated code passes (ignored).
func StaticMethod() CallOption {
	return CallOption{}
}

// WaitForReady is accepted and ignored (the model's calls fail fast, a subset-of-behaviors
// difference only in timing: a real call waiting for the connection may then fail or succeed).
func WaitForReady(waitForReady bool) CallOption {
	return CallOption{}
}

// A ServerOption sets options of a server; the model has none.
type ServerOption struct{}

// ClientConnInterface defines the functions clients need to perform unary RPCs (the real one
// also has NewStream; streaming generated code does not build against the model).
type ClientConnInterface interface {
	Invoke(ctx context.Context, method string, args interface{}, reply interface{}, opts ...CallOption) error
}

// ServiceRegistrar wraps a single method that supports service registration.
type ServiceRegistrar interface {
	RegisterService(desc *ServiceDesc, impl interface{})
}

// UnaryServerInfo consists of various information about a unary RPC on server side.
type UnaryServerInfo struct {
	Server     interface{}
	FullMethod string
}

// UnaryHandler defines the handler invoked by UnaryServerInterceptor to complete the normal
// execution of a unary RPC.
type UnaryHandler func(ctx context.Context, req interface{}) (interface{}, error)

// UnaryServerInterceptor provides a hook to intercept the execution of a unary RPC on the
// server (the model's servers have none: handlers are called with a nil interceptor).
type UnaryServerInterceptor func(ctx context.Context, req interface{}, info *UnaryServerInfo, handler UnaryHandler) (interface{}, error)

// MethodHandler is a function type that processes a unary RPC method call.
type MethodHandler func(srv interface{}, ctx context.Context, dec func(interface{}) error, interceptor UnaryServerInterceptor) (interface{}, error)

// MethodDesc represents an RPC service's method specification.
type MethodDesc struct {
	MethodName string
	Handler    MethodHandler
}

// ServerStream is the server side of a stream (declared for StreamHandler; the model serves no
// streams).
type ServerStream interface {
	Context() context.Context
	SendMsg(m interface{}) error
	RecvMsg(m interface{}) error
}

// StreamHandler defines the handler called by gRPC server to complete the execution of a
// streaming RPC (declared for StreamDesc; never called by the model).
type StreamHandler func(srv interface{}, stream ServerStream) error

// StreamDesc represents a streaming RPC service's method specification (a ServiceDesc with any
// makes RegisterService panic: the model serves unary methods only).
type StreamDesc struct {
	StreamName    string
	Handler       StreamHandler
	ServerStreams bool
	ClientStreams bool
}

// ServiceDesc represents an RPC service's specification.
type ServiceDesc struct {
	ServiceName string
	HandlerType interface{}
	Methods     []MethodDesc
	Streams     []StreamDesc
	Metadata    interface{}
}
