package clientv3kv

import (
	"context"
	"errors"

	"go.etcd.io/etcd/api/v3/v3rpc/rpctypes"
	clientv3 "go.etcd.io/etcd/client/v3"
)

// REQ clientv3kv/put-errors: a failed call returns no reply; a put never fails with a read's
// errors (ErrCompacted, ErrFutureRev); an error that is one of etcd's definite errors is the
// cluster's answer (the put was linearized and changed nothing); an error of a done context
// settles nothing.
// Users: every user checks err before the reply (txnlin's call*, Kubernetes' store,
// concurrency); Kubernetes' lease manager and concurrency's Session test for ErrLeaseNotFound
// (a put with a lease that expired); txnlin treats every error as "maybe applied" (its prophecy).
// Assumes: none.
// Specs: Client.Put.spec (the error disjuncts: putReply's .err e, indefCall); laws:
// indefCall_pure, errVal_inj, errVal_ty; rpctypes' init law (2a: rpctypes.ErrCompacted holds
// errVal .compacted, ...).
func ReqPutErrors(ctx context.Context, cli *clientv3.Client, k string, lease clientv3.LeaseID) {
	resp, err := cli.Put(ctx, k, "v", clientv3.WithLease(lease))
	if err == nil {
		if resp == nil {
			panic("put: no error, a reply")
		}
		return
	}
	if resp != nil {
		panic("put: an error and a reply")
	}
	if errors.Is(err, rpctypes.ErrCompacted) || errors.Is(err, rpctypes.ErrFutureRev) {
		panic("put: a read's error")
	}
	if errors.Is(err, rpctypes.ErrLeaseNotFound) {
		// the cluster's answer: the lease was not live when the put was linearized (granted
		// leases may expire at any time: an environment step)
		return
	}
}

// REQ clientv3kv/get-errors: a linearizable get at a revision the caller saw never fails with
// ErrFutureRev; ErrCompacted is the only revision error left.
// Users: Kubernetes' store (Get at a resourceVersion: ErrCompacted becomes "too old resource
// version"), the cache (cache.go: ErrCompacted on a revision below its window), the examples
// (examples/etcd/compacted).
// Assumes: rev is the header revision of an earlier reply of this client (the caller holds the
// etcdLb its update took then).
// Specs: Client.Get.spec, WithRev.spec; the model's RangeReq.revErr; laws: etcdLb_reach.
func ReqGetErrors(ctx context.Context, cli *clientv3.Client, k string, rev int64) {
	_, err := cli.Get(ctx, k, clientv3.WithRev(rev))
	if err == rpctypes.ErrFutureRev {
		panic("get: a revision reached is not in the future")
	}
}

// REQ clientv3kv/auth-refusal: with auth on, a linearizable read outside the principal's
// permissions never succeeds, and a read inside them returns only permitted keys.
// Users: examples/etcd/auth/authkv.go:163-234 (its "good" and "bad" principals), every client
// of a cluster with auth on.
// Assumes: auth is on and stays on, cli authenticates as user u (not of the root role) whose only
// role grants read on [pfx, end) and nothing else, and no administrator changes u or its roles
// during the calls (the owner's invariant); pfx < end, end neither "" nor "\x00" (a half-open
// range); outside is not in [pfx, end). Each read passes authLb γ lo at an auth index lo where
// auth is already on with u's roles as above (from an etcdLb the caller holds of such a state:
// at lo = 0 permittedSince would admit the initial auth-off table).
// Specs: Client.Get.spec (State.permits at the firing state); laws: errorsIs_errVal.
func ReqAuthRefusal(ctx context.Context, cli *clientv3.Client, pfx, end, outside string) {
	if _, err := cli.Get(ctx, outside); err == nil {
		panic("auth: a read outside the permission succeeded")
	}
	resp, err := cli.Get(ctx, pfx, clientv3.WithRange(end))
	if err != nil {
		return
	}
	for _, kv := range resp.Kvs {
		if string(kv.Key) < pfx || string(kv.Key) >= end {
			panic("auth: a key outside the permitted range")
		}
	}
}

// REQ clientv3kv/ctx-errors: a call whose context is done returns an error, which settles
// nothing.
// Users: every user passes a context with a deadline (txnlin: etcdstart.RequestTimeout;
// Kubernetes: the request's context).
// Assumes: none.
// Specs: Client.Get.spec (indefCall), ContextError.spec; Context.ctxOk (any context).
func ReqCtxErrors(ctx context.Context, cli *clientv3.Client, k string) {
	cctx, cancel := context.WithCancel(ctx)
	cancel()
	resp, err := cli.Get(cctx, k)
	if err != nil && resp != nil {
		panic("get: an error and a reply")
	}
	if err == rpctypes.ErrCompacted {
		panic("get: a current read is never compacted")
	}
}
