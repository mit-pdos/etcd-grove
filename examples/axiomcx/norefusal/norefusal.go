// Package norefusal: counterexamples to etcd_noRefusal (Proof/go_etcd_io/etcd/server/v3/etcdserver/
// api/v3rpc/NoRefusal.lean) as it stood until 2026-11-24 (notes/axiom-review/norefusal-link.md).
//
// Main: the route the fix closes. The old axiom derived the pure, global noRefusalAt addrA from etcd's
// gRPC server gs (built by v3rpc.Server over a started member, authentication off) and a listener at
// addrA, and handed the listener back: nothing tied the address to gs. The program never serves gs; it
// serves addrA with another gRPC server gs2 whose KV Put handler answers with the learner refusal
// (grpc.start' with netListenerAt + netAddrLeft, Serve's axiom), and calls Put at addrA directly over
// grpc. grpcInvokerOk's post (kvMethod ∧ noRefusalAt addrA → d ∉ refusalDescs) says the error's
// description is no refusal; it is one. Main panics. The fixed axiom takes the server listening at the
// address (grpcAddrIs addrA γ, grpcSrvCfg γ c with etcd's KV registrations among c's), which here is
// gs2, without them: it does not apply.
//
// MainInterceptor: the route the first fix (665f2f1efa) left open. The server at addrB is a grpc
// server gs3 with etcd's own KV service over the member (v3rpc.NewQuotaKVServer(s): quotaKVServerAt q
// ... s, kvRegs q among its registrations) and a unary interceptor of the program's that answers every
// call with the learner refusal. The old axiom and the first fix applied to it (they read the
// registrations, not the interceptor chain), and the call is refused: MainInterceptor panics. The
// final axiom requires the chain to be etcd's by identity (v3rpc.etcdUnaryIcs s c.ics: the closures
// newLogUnaryInterceptor(s) and newUnaryInterceptor(s) return and grpc-prometheus's), which
// [refuseAll] is not: it does not apply.
package norefusal

import (
	"context"
	"net"

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
	peerB   = "127.0.0.1:24100"
	clientB = "127.0.0.1:24101" // the member's client URL; gs is built for it but served nowhere
	addrA   = "127.0.0.1:24102" // the old etcd_noRefusal's address: served by gs2
	peerC   = "127.0.0.1:24103"
	clientC = "127.0.0.1:24104"
	addrB   = "127.0.0.1:24105" // served by gs3: etcd's KV service behind a refusing interceptor
)

const learnerDesc = "etcdserver: rpc not supported for learner"

// refuser: gs2's KV service, whose Put answers with the learner refusal.
type refuser struct{ pb.UnimplementedKVServer }

func (refuser) Put(context.Context, *pb.PutRequest) (*pb.PutResponse, error) {
	return nil, rpctypes.ErrGRPCNotSupportedForLearner
}

func put(addr string) error {
	conn, err := grpc.NewClient(addr, grpc.WithTransportCredentials(insecure.NewCredentials()))
	if err != nil {
		return nil
	}
	defer conn.Close()
	_, err = pb.NewKVClient(conn).Put(context.Background(), &pb.PutRequest{Key: []byte("k"), Value: []byte("v")})
	return err
}

func Main() {
	lg := zap.NewNop()
	s, err := etcdstart.StartServer("norefusal", peerB, clientB, lg)
	if err != nil {
		return
	}
	defer s.Stop()
	// gs: etcd's gRPC server over s (grpcSrvNew gs ... with kvRegs q; quotaKVServerAt q ... s)
	gs := v3rpc.Server(s, nil, nil)
	_ = gs
	// netListenerAt l addrA ∗ netAddrLeft addrA; the old etcd_noRefusal addrA gs ... l: noRefusalAt
	// addrA, netListenerAt l addrA back
	l, err := net.Listen("tcp", addrA)
	if err != nil {
		return
	}
	gs2 := grpc.NewServer()
	pb.RegisterKVServer(gs2, refuser{})
	go gs2.Serve(l) // grpc.start' gs2 l addrA (netListenerAt, netAddrLeft); Serve's axiom
	defer gs2.Stop()
	err = put(addrA)
	if err == nil {
		return
	}
	// grpcInvokerOk: kvMethod "/etcdserverpb.KV/Put" ∧ noRefusalAt addrA → d ∉ refusalDescs
	if status.Convert(err).Message() == learnerDesc {
		panic("norefusal: a refusal at an address etcd_noRefusal said refusal-free")
	}
}

// refuseAll: a unary interceptor that answers every call with the learner refusal, without calling
// the handler (srvInterceptorOk allows it: a non-nil error that is not a handler's).
func refuseAll(context.Context, any, *grpc.UnaryServerInfo, grpc.UnaryHandler) (any, error) {
	return nil, rpctypes.ErrGRPCNotSupportedForLearner
}

func MainInterceptor() {
	lg := zap.NewNop()
	s, err := etcdstart.StartServer("norefusal", peerC, clientC, lg)
	if err != nil {
		return
	}
	defer s.Stop()
	// gs3: etcd's KV service over s (NewQuotaKVServer: quotaKVServerAt q ... s; RegisterKVServer:
	// kvRegs q among the registrations), behind the program's interceptor
	gs3 := grpc.NewServer(grpc.ChainUnaryInterceptor(refuseAll))
	pb.RegisterKVServer(gs3, v3rpc.NewQuotaKVServer(s))
	l, err := net.Listen("tcp", addrB)
	if err != nil {
		return
	}
	// grpc.start' gs3 l addrB: grpcAddrIs addrB γ ∗ grpcSrvCfg γ c, kvRegs q ⊆ c.regs; the first
	// fix's etcd_noRefusal: noRefusalAt addrB (the final one also needs etcdUnaryIcs s c.ics: false here)
	go gs3.Serve(l)
	defer gs3.Stop()
	err = put(addrB)
	if err == nil {
		return
	}
	if status.Convert(err).Message() == learnerDesc {
		panic("norefusal: a refusal at an address etcd_noRefusal said refusal-free (interceptor)")
	}
}
