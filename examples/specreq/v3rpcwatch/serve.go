package v3rpcwatch

import (
	"time"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/server/v3/etcdserver"
	"go.etcd.io/etcd/server/v3/etcdserver/api/v3rpc"
	"google.golang.org/grpc"
)

// REQ v3rpcwatch/serve: a started member's watch service can be built and registered with a gRPC
// server (the service's contract is what the registration carries).
// Users: server/etcdserver/api/v3rpc/grpc.go:81 (Server), server/embed (through Server).
// Assumes: s is a started member of a cluster (watchMemberAt, from 2e's NewServer/Start, its
// configured progress interval within watchIntervalCfgOk); gs is a server being built (grpc's
// srvBuild gs B, from grpc.NewServer) on which the Watch service is not registered yet (what
// Server.RegisterService.spec takes; verify-round A6 F10: the Assumes said nothing of gs).
// Specs: NewWatchServer.spec, RegisterWatchServer.spec, Grpc's Server.RegisterService.spec; laws: watchServerAt_service, watchServiceAt_methods (2a's
// registration takes watchServiceAt).
func ReqServeWatch(s *etcdserver.EtcdServer, gs *grpc.Server) {
	ws := v3rpc.NewWatchServer(s)
	if ws == nil {
		panic("serve: a watch server")
	}
	pb.RegisterWatchServer(gs, ws)
}

// REQ v3rpcwatch/interval: the progress interval set by a test is used: every later stream's
// ticker gets a positive period.
// Users: tests/integration (SetProgressReportInterval before starting members), NewWatchServer.
// Assumes: none.
// Specs: SetProgressReportInterval.spec (progressIntervalOk), GetProgressReportInterval.spec.
func ReqInterval() {
	v3rpc.SetProgressReportInterval(200 * time.Millisecond)
	if v3rpc.GetProgressReportInterval() <= 0 {
		panic("interval: positive")
	}
}
