package unsafereflect

// Example 5: grpc's service registration and dispatch.
//
// Mirrors google.golang.org/grpc@v1.84.0/server.go:778-818
// (RegisterService: reflect.TypeOf(sd.HandlerType).Elem() is the service's
// interface type, and the server fails with logger.Fatalf unless
// reflect.TypeOf(ss).Implements(ht); register fails on a duplicate service)
// and a generated *_grpc.pb.go handler (etcd's api/v3/etcdserverpb/
// rpc_grpc.pb.go: _KV_Range_Handler does `srv.(KVServer).Range(ctx, in)`).
// etcd registers its services in server/etcdserver/api/v3rpc/grpc.go
// (pb.RegisterKVServer(grpcServer, NewQuotaKVServer(s)), ...).
//
// To prove: RegisterService does not fail, and later every handler's type
// assertion `srv.(KVServer)` succeeds: the check by reflection at
// registration and the assertion at dispatch are about the same method set.
// The fact "*quotaKVServer implements KVServer" is fixed at compile time; a
// proof should get it from the translation's method sets.
//
// Needs R1: reflect.Type of a nil pointer to an interface, Elem, Implements
// (method sets of interface and concrete types, compared by reflection the
// way the type assertion compares them).

import (
	"context"
	"reflect"
	"sync"
)

type RangeRequest struct{ Key []byte }
type RangeResponse struct{ Count int64 }

type KVServer interface {
	Range(context.Context, *RangeRequest) (*RangeResponse, error)
}

type methodHandler func(srv any, ctx context.Context, in any) (any, error)

type ServiceDesc struct {
	ServiceName string
	HandlerType any // (*KVServer)(nil)
	Methods     map[string]methodHandler
}

type serviceInfo struct {
	serviceImpl any
	methods     map[string]methodHandler
}

type Server struct {
	mu       sync.Mutex
	services map[string]*serviceInfo
}

func NewServer() *Server { return &Server{services: map[string]*serviceInfo{}} }

func (s *Server) RegisterService(sd *ServiceDesc, ss any) {
	if ss != nil {
		ht := reflect.TypeOf(sd.HandlerType).Elem()
		st := reflect.TypeOf(ss)
		if !st.Implements(ht) {
			panic("grpc: Server.RegisterService found the handler of type " + st.String() + " that does not satisfy " + ht.String())
		}
	}
	s.mu.Lock()
	defer s.mu.Unlock()
	if _, ok := s.services[sd.ServiceName]; ok {
		panic("grpc: Server.RegisterService found duplicate service registration for " + sd.ServiceName)
	}
	s.services[sd.ServiceName] = &serviceInfo{serviceImpl: ss, methods: sd.Methods}
}

func (s *Server) handle(service, method string, in any) (any, error) {
	s.mu.Lock()
	si := s.services[service]
	s.mu.Unlock()
	if si == nil {
		return nil, context.Canceled // stands for status.Errorf(codes.Unimplemented, ...)
	}
	h, ok := si.methods[method]
	if !ok {
		return nil, context.Canceled
	}
	return h(si.serviceImpl, context.Background(), in)
}

// _KV_Range_Handler is the generated handler.
func _KV_Range_Handler(srv any, ctx context.Context, in any) (any, error) {
	return srv.(KVServer).Range(ctx, in.(*RangeRequest))
}

var KV_ServiceDesc = ServiceDesc{
	ServiceName: "etcdserverpb.KV",
	HandlerType: (*KVServer)(nil),
	Methods:     map[string]methodHandler{"Range": _KV_Range_Handler},
}

type quotaKVServer struct{}

func (*quotaKVServer) Range(_ context.Context, r *RangeRequest) (*RangeResponse, error) {
	return &RangeResponse{Count: int64(len(r.Key))}, nil
}

// REQ unsafereflect/register-service: registering etcd's KV service with its server does not fail
// (the handler implements the service interface, by reflection), and a Range dispatched by name
// reaches the handler (the generated handler's assertion srv.(KVServer) succeeds).
// Users: etcd's v3rpc.Server (server/etcdserver/api/v3rpc/grpc.go: pb.RegisterKVServer, ...);
// grpc@v1.84.0/server.go:778-818; every *_grpc.pb.go handler.
// Assumes: each service is registered once.
// Specs: none yet; needs R1: Elem, Implements, agreeing with the type assertion (doc.go).
func ReqRegisterService() *RangeResponse {
	s := NewServer()
	s.RegisterService(&KV_ServiceDesc, &quotaKVServer{})
	r, err := s.handle("etcdserverpb.KV", "Range", &RangeRequest{Key: []byte("foo")})
	if err != nil {
		panic("register-service: not dispatched")
	}
	return r.(*RangeResponse)
}
