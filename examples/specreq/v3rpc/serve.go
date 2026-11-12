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
// ep (EtcdServer.srvAt s γ ep: s's srvFields and srvEp γ ep id); lis is net.Listen's at ep, which
// the program reserved once for etcd's contracts and member id (2e's srvEp_reserve with srvNet:
// Http.addrFree ep to the family Http.protoFam ep F, F L := Grpc.grpcOver (etcdContract γ ep at
// generation L) (P L), and srvEp γ ep id); in this generation Http.protoFam_at gives Grpc.addrAt ep
// (etcdContract γ ep). A restart after a stop reuses both as they are; after a crash, the next
// generation's: srvEp_gen, Http.protoFam_gen, then protoFam_at at the new generation, whose
// contract names the new generation's lease views (the old generation's clients died with it); a
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
