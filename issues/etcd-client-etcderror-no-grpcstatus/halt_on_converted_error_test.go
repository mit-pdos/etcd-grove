// Reproduction of issues/etcd-client-etcderror-no-grpcstatus.md.
//
// Package clientv3, file client/v3/halt_on_converted_error_test.go of go.etcd.io/etcd (module
// go.etcd.io/etcd/client/v3), at the etcd pin of etc/goose.py: 107edf7e4 (branch goose-lean of
// upamanyus/etcd).
//
// Run, in client/v3:
//
//	GOTOOLCHAIN=go1.27.1 go test . -run '^TestHaltOnConvertedLeaderChanged$' -count=1
//
// Fails at the pin (shows the bug): logs "converted: rpctypes.EtcdError etcdserver: leader
// changed, code Unknown", then "isHaltErr(ContextError(ErrGRPCLeaderChanged)) = true".
package clientv3

import (
	"context"
	"testing"

	"google.golang.org/grpc/status"

	"go.etcd.io/etcd/api/v3/v3rpc/rpctypes"
)

func TestHaltOnConvertedLeaderChanged(t *testing.T) {
	ctx := context.Background()
	if isHaltErr(ctx, rpctypes.ErrGRPCLeaderChanged) {
		t.Fatalf("the gRPC error halts")
	}
	err := ContextError(ctx, rpctypes.ErrGRPCLeaderChanged) // what Authenticate returns
	t.Logf("converted: %T %v, code %v", err, err, status.Code(err))
	if isHaltErr(ctx, err) {
		t.Errorf("isHaltErr(ContextError(ErrGRPCLeaderChanged)) = true")
	}
}
