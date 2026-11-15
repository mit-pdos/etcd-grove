package clientv3client

import (
	"context"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	clientv3 "go.etcd.io/etcd/client/v3"
	"go.uber.org/zap"
)

// REQ clientv3client/inproc-client: the in-process client v3client.New builds (v3lock's and
// v3election's): a NewCtxClient whose fields are set from adapters over the server, then used as any
// client (a put through its KV, its context and logger). Each call's principal is its context's
// (the forwarded gRPC caller's token).
// Users: server/etcdserver/api/v3client/v3client.go:29-50, v3lock/lock.go:35-46,
// v3election/election.go.
// Assumes: each adapter meets its wire contract (remoteKVAt, remoteLeaseAt, ...: the server batch's
// introductions, requested in req/); the watcher's from 1b.
// Specs: NewCtxClient.spec, WithZapLogger.spec, NewKVFromKVClient.spec (W0),
// NewLeaseFromLeaseClient.spec, NewAuthFromAuthClient.spec, NewClusterFromClusterClient.spec,
// NewMaintenanceFromMaintenanceClient.spec, clientBare_assemble, Client.Put.spec (W0),
// Client.Ctx.spec.
func ReqInProcClient(ctx context.Context, lg *zap.Logger, kvc pb.KVClient, lc pb.LeaseClient,
	ac pb.AuthClient, cc pb.ClusterClient, mc pb.MaintenanceClient, w clientv3.Watcher) {
	c := clientv3.NewCtxClient(ctx, clientv3.WithZapLogger(lg))
	c.KV = clientv3.NewKVFromKVClient(kvc, c)
	c.Lease = clientv3.NewLeaseFromLeaseClient(lc, c, 0)
	c.Watcher = w
	c.Auth = clientv3.NewAuthFromAuthClient(ac, c)
	c.Cluster = clientv3.NewClusterFromClusterClient(cc, c)
	c.Maintenance = clientv3.NewMaintenanceFromMaintenanceClient(mc, c)
	_, _ = c.Put(c.Ctx(), "k", "v")
	if c.GetLogger() == nil {
		panic("inproc-client: no logger")
	}
}
