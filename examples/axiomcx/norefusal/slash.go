package norefusal

// MainSlash: the route the second fix (152b805937) left open, found by an independent review. The
// server is etcd's own (v3rpc.Server(s, nil, nil): etcdUnaryIcs s, kvRegs q among its registrations),
// to which the program adds one more service, named "etcdserverpb.KV/Evil", before serving it.
// kvMethod was a prefix test on the full method name, so "/etcdserverpb.KV/Evil/Put" was a kvMethod;
// grpc dispatches it (at the last "/") to the extra service's Put, behind etcd's chain, which passes
// it at a voter, and its handler answers with the learner refusal. MainSlash panics. kvMethod is now
// the five exact names of etcd's KV methods, so the attempt contract no longer reads noRefusalAt for
// this call.

import (
	"context"
	"net"
	"time"

	"go.uber.org/zap"
	"google.golang.org/grpc"
	"google.golang.org/grpc/credentials/insecure"
	"google.golang.org/grpc/status"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/api/v3/v3rpc/rpctypes"
	"go.etcd.io/etcd/server/v3/etcdserver/api/v3rpc"

	"github.com/mit-pdos/etcd-grove/examples/lib/etcdstart"
)

const (
	peerS   = "127.0.0.1:24200"
	clientS = "127.0.0.1:24201"
	addrS   = "127.0.0.1:24202"
)

type EvilServer interface {
	Put(context.Context, *pb.PutRequest) (*pb.PutResponse, error)
}

type evil struct{}

func (evil) Put(context.Context, *pb.PutRequest) (*pb.PutResponse, error) {
	return nil, rpctypes.ErrGRPCNotSupportedForLearner
}

func evilPutHandler(srv any, ctx context.Context, dec func(any) error, ic grpc.UnaryServerInterceptor) (any, error) {
	in := new(pb.PutRequest)
	if err := dec(in); err != nil {
		return nil, err
	}
	info := &grpc.UnaryServerInfo{Server: srv, FullMethod: "/etcdserverpb.KV/Evil/Put"}
	h := func(ctx context.Context, req any) (any, error) {
		return srv.(EvilServer).Put(ctx, req.(*pb.PutRequest))
	}
	return ic(ctx, in, info, h)
}

var evilDesc = grpc.ServiceDesc{
	ServiceName: "etcdserverpb.KV/Evil",
	HandlerType: (*EvilServer)(nil),
	Methods:     []grpc.MethodDesc{{MethodName: "Put", Handler: evilPutHandler}},
}

func MainSlash() {
	s, err := etcdstart.StartServer("norefusal", peerS, clientS, zap.NewNop())
	if err != nil {
		return
	}
	defer s.Stop()
	gs := v3rpc.Server(s, nil, nil) // etcd's chain over s, etcd's KV over s
	gs.RegisterService(&evilDesc, evil{})
	l, err := net.Listen("tcp", addrS)
	if err != nil {
		return
	}
	go gs.Serve(l) // grpc.start': grpcAddrIs addr γ, grpcSrvCfg γ c; etcd_noRefusal: noRefusalAt addr
	defer gs.Stop()
	conn, err := grpc.NewClient(addrS, grpc.WithTransportCredentials(insecure.NewCredentials()))
	if err != nil {
		return
	}
	defer conn.Close()
	for i := 0; i < 100; i++ {
		out := new(pb.PutResponse)
		err = conn.Invoke(context.Background(), "/etcdserverpb.KV/Evil/Put",
			&pb.PutRequest{Key: []byte("k"), Value: []byte("v")}, out)
		if err == nil {
			return
		}
		// grpcInvokerOk: kvMethod "/etcdserverpb.KV/Evil/Put" ∧ noRefusalAt addr → d ∉ refusalDescs
		if status.Convert(err).Message() == learnerDesc {
			panic("norefusal: a refusal at an address etcd_noRefusal said refusal-free (slash)")
		}
		time.Sleep(50 * time.Millisecond) // e.g. "not capable" before the cluster version is set
	}
}
