package clientv3lease

import (
	"context"

	"go.etcd.io/etcd/api/v3/v3rpc/rpctypes"
	clientv3 "go.etcd.io/etcd/client/v3"
)

// REQ clientv3lease/session-lifecycle: concurrency's Session: grant, keep the lease alive by
// draining the keep-alive channel until it closes, then cancel and revoke. KeepAlive with a
// cancellable context returns a non-nil channel when it returns no error; ranging over it never
// panics; Revoke answers success or ErrLeaseNotFound (possibly for this very lease, after a resend)
// or an indefinite error.
// Users: client/v3/concurrency/session.go:41-115 (NewSession, Orphan, Close), leasing (its
// session), recipes (through concurrency).
// Assumes: none (the lease may expire at any time).
// Specs: lessor.Grant.spec, lessor.KeepAlive.spec, kaChan_recv.spec, lessor.Revoke.spec,
// Context.WithCancel.spec (W0).
func ReqSessionLifecycle(cli *clientv3.Client, ttl int64) {
	resp, err := cli.Lease.Grant(cli.Ctx(), ttl)
	if err != nil {
		return
	}
	ctx, cancel := context.WithCancel(cli.Ctx())
	ka, err := cli.Lease.KeepAlive(ctx, resp.ID)
	if err != nil || ka == nil {
		cancel()
		return
	}
	donec := make(chan struct{})
	go func() {
		defer close(donec)
		for range ka {
		}
	}()
	cancel()
	<-donec
	_, err = cli.Lease.Revoke(context.Background(), resp.ID)
	if err != nil && err != rpctypes.ErrLeaseNotFound {
		return
	}
}

// REQ clientv3lease/keepalive-values: every response a keep-alive channel delivers is about the
// lease asked for, with a positive TTL; nothing more (it says nothing about the lease's state).
// Users: client/v3/concurrency/session.go (drains; a caller of Session.Done relies on the channel
// closing, liveness), etcdctl's lease keep-alive (prints the TTL).
// Assumes: none.
// Specs: lessor.KeepAlive.spec, kaChan_recv.spec (kaRespAt).
func ReqKeepAliveValues(ctx context.Context, cli *clientv3.Client, id clientv3.LeaseID) {
	ka, err := cli.Lease.KeepAlive(ctx, id)
	if err != nil {
		return
	}
	for r := range ka {
		if r.ID != id {
			panic("keepalive-values: response about another lease")
		}
		if r.TTL <= 0 {
			panic("keepalive-values: non-positive TTL delivered")
		}
	}
}
