package grpc

import (
	"context"
	"net"

	clientv3 "go.etcd.io/etcd/client/v3"
	grpcgo "google.golang.org/grpc"
	"google.golang.org/grpc/stats"
)

// REQ grpc/kube-dial-opts: a client built with Kubernetes' dial options (chained pass-through
// interceptors, an observing stats handler, a context dialer that dials the address it is given)
// is an etcd client like any other: its calls keep the client's contract.
// Users: Kubernetes' newETCD3Client (k8s.io/apiserver/pkg/storage/storagebackend/factory/
// etcd3.go:309-339: grpc-prometheus's chained interceptors, otelgrpc's stats handler, the egress
// dialer); the gRPC proxy's client (grpc_proxy.go:344-349).
// Assumes: eps are client URLs of members of one cluster (servesAt); auth off.
// Specs: WithChainUnaryInterceptor.spec, WithChainStreamInterceptor.spec, WithStatsHandler.spec,
// WithContextDialer.spec (each a dialOptAt v id, under cliIcPass/cliSicPass/statsOk/ctxDialerOk:
// the snippet's own interceptors, handler and dialer meet them by their bodies); 1c's
// dialOptsOk_neutral, New.spec, Client.Get's spec.
// (verify-round, A6-completeness F2 / A2-completeness F2.)
func ReqKubeDialOpts(ctx context.Context, eps []string) {
	var d net.Dialer
	cli, err := clientv3.New(clientv3.Config{
		Endpoints: eps,
		DialOptions: []grpcgo.DialOption{
			grpcgo.WithChainUnaryInterceptor(passUnary),
			grpcgo.WithChainStreamInterceptor(passStream),
			grpcgo.WithStatsHandler(observer{}),
			grpcgo.WithContextDialer(func(ctx context.Context, addr string) (net.Conn, error) {
				return d.DialContext(ctx, "tcp", addr)
			}),
		},
	})
	if err != nil {
		return
	}
	defer cli.Close()
	if _, err := cli.Get(ctx, "k"); err != nil {
		return
	}
}

// passUnary calls its invoker once with its own arguments and returns its result (cliIcPass).
func passUnary(ctx context.Context, method string, req, reply any, cc *grpcgo.ClientConn,
	invoker grpcgo.UnaryInvoker, opts ...grpcgo.CallOption) error {
	return invoker(ctx, method, req, reply, cc, opts...)
}

// passStream calls its streamer once with its own arguments and returns its result (cliSicPass).
func passStream(ctx context.Context, desc *grpcgo.StreamDesc, cc *grpcgo.ClientConn, method string,
	streamer grpcgo.Streamer, opts ...grpcgo.CallOption) (grpcgo.ClientStream, error) {
	return streamer(ctx, desc, cc, method, opts...)
}

// observer is a stats handler that only observes (statsOk).
type observer struct{}

func (observer) TagRPC(ctx context.Context, _ *stats.RPCTagInfo) context.Context   { return ctx }
func (observer) HandleRPC(context.Context, stats.RPCStats)                         {}
func (observer) TagConn(ctx context.Context, _ *stats.ConnTagInfo) context.Context { return ctx }
func (observer) HandleConn(context.Context, stats.ConnStats)                       {}
