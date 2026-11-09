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
// Assumes: s is a started member of a cluster (EtcdServer.isServer, 2e); lis listens at the
// member's client address, which the program bound to etcd's contracts (Grpc.addrAt, from its
// addrFree, once; a restart reuses the binding); the program's messages fit (Grpc.msgsFit).
// Specs: Server.spec, Grpc.start.spec, Grpc.Server.Serve.spec; laws: servesAt_addr.
func ReqServe(s *etcdserver.EtcdServer, lis net.Listener) {
	gs := v3rpc.Server(s, nil, nil)
	if gs == nil {
		panic("serve: no server")
	}
	err := gs.Serve(lis)
	_ = err // Serve returns only when the listener fails or the server stops
}
