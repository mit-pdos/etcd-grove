// Package clientv3client holds the requirement snippets of etcd's Go client lifecycle, auth,
// cluster and maintenance APIs and the Kubernetes interface (batch 1c,
// Spec/go_etcd_io/etcd/client/v3/ApiClient.lean, .../kubernetes/Api.lean), each reliance an
// explicit panic.
//
// Common assumptions (the proofs' setting): the caller owns the cluster's state etcdState in an
// invariant of its own and gives the client the identity update idUpd (cfgOk); every endpoint
// named serves the cluster (servesAt); contexts carry no auth token metadata of their own
// (ctxPrin).
package clientv3client

import (
	"context"

	clientv3 "go.etcd.io/etcd/client/v3"
	"go.uber.org/zap"
)

// REQ clientv3client/new-wrap-close: New returns a usable client or an error and nil; the KV field
// may be replaced by a wrapper meeting the KV contract before the client is shared; Close never
// panics, and calls after Close fail (an indefinite error), never panic.
// Users: examples/lib/etcdstart (NewClient), Kubernetes' storagebackend/factory/etcd3.go
// (kubernetes.New, then client.KV = NewETCDLatencyTracker(client.KV), destroy: client.Close()),
// newClient's own error paths.
// Assumes: ep serves the cluster; lg a logger.
// Specs: New.spec (clientMut), clientMut_KV, clientMut_freeze (W0), Client.Close.spec,
// Client.Put.spec (W0: an indefinite error after Close).
func ReqNewWrapClose(ep string, lg *zap.Logger) {
	cli, err := clientv3.New(clientv3.Config{Endpoints: []string{ep}, Logger: lg})
	if err != nil {
		if cli != nil {
			panic("new-wrap-close: client with an error")
		}
		return
	}
	cli.KV = wrapKV{cli.KV}
	_ = cli.Close()
	// a call after Close: an error that settles nothing (or, racing the close, an answer)
	_, _ = cli.Put(context.Background(), "k", "v")
}

// wrapKV is a pass-through KV wrapper (Kubernetes' latency tracker's shape).
type wrapKV struct{ clientv3.KV }

// REQ clientv3client/new-no-endpoints: New with no endpoint returns an error and nil.
// Users: callers' configuration errors (Kubernetes' factory reports them).
// Assumes: lg a logger or nil.
// Specs: New.spec (its post: no endpoint, an error and nil).
func ReqNewNoEndpoints(lg *zap.Logger) {
	cli, err := clientv3.New(clientv3.Config{Logger: lg})
	if err == nil || cli != nil {
		panic("new-no-endpoints: a client without endpoints")
	}
}

// REQ clientv3client/endpoints: the client's endpoints are a copy the caller owns, each serving the
// cluster; Status of each never panics.
// Users: Kubernetes' compact.go (the compactor's endpoint key), feature_support_checker.go (Status
// of each endpoint).
// Assumes: auto-sync off and no SetEndpoints concurrent with Status, the list non-empty (the caller
// holds a fraction of New's endpoints token: Client.dial reads c.endpoints[0] unlocked,
// issues/etcd-client-dial-empty-endpoints.md).
// Specs: Client.Endpoints.spec, Client.Status.spec (Maint.StatusTriple).
func ReqEndpoints(ctx context.Context, cli *clientv3.Client) {
	eps := cli.Endpoints()
	for _, ep := range eps {
		if _, err := cli.Status(ctx, ep); err != nil {
			continue
		}
	}
	if len(eps) > 0 {
		eps[0] = "overwritten" // the copy is the caller's
	}
}

// REQ clientv3client/ctx-put: the client's context is a context the KV contract accepts as the
// client's principal's.
// Users: client/v3/concurrency (NewSession's default context, mutex.go:92, stm.go:91),
// leasing.NewKV, Kubernetes' store.go:243.
// Specs: Client.Ctx.spec (ctxOk, ctxPrin), Client.Put.spec (W0).
func ReqCtxPut(cli *clientv3.Client) {
	ctx, cancel := context.WithCancel(cli.Ctx())
	defer cancel()
	_, _ = cli.Put(ctx, "k", "v")
}

// REQ clientv3client/new-from-url: NewFromURL's client has no principal.
// Users: tools and tests.
// Specs: NewFromURL.spec.
func ReqNewFromURL(url string) {
	cli, err := clientv3.NewFromURL(url)
	if err != nil {
		return
	}
	_ = cli.Close()
}
