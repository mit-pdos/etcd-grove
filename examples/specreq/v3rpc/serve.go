package v3rpc

import (
	"net"

	"go.etcd.io/etcd/server/v3/etcdserver"
	"go.etcd.io/etcd/server/v3/etcdserver/api/v3rpc"
)

// REQ v3rpc/serve: a started member's gRPC server is built with every service registered and
// served on its client address; from then on the address serves etcd (servesAt), whatever the
// mode (auth on or off, TLS or not, restarted at the same address).
// Users: server/embed (serveClients: v3rpc.Server then Serve), examples/lib/etcdstart (Serve).
// Assumes: s is a started member of a cluster (EtcdServer.isServer, 2e) serving the client address
// ep (EtcdServer.srvAt s γ ep, from the serving start, 2e); lis is net.Listen's at ep, which the
// program reserved for etcd's contracts (Http.reserve to
// Http.protoAt ep (Grpc.grpcOver (etcdContract γ ep) P), i.e. Grpc.addrAt; a restart reuses it); a
// pool of the program's thread tokens (Http.handlerPool); the program's messages fit (Grpc.msgsFit).
// Specs: Server.spec, Grpc.srvBuild_ne_null, Grpc.start.spec, Grpc.Server.Serve.spec; laws:
// servesAt_addr.
func ReqServe(s *etcdserver.EtcdServer, lis net.Listener) {
	gs := v3rpc.Server(s, nil, nil)
	if gs == nil {
		panic("serve: no server")
	}
	err := gs.Serve(lis)
	_ = err // Serve returns only when the listener fails or the server stops
}
