package clientv3_test

import (
	"context"
	"testing"
	"time"

	clientv3 "go.etcd.io/etcd/client/v3"
	"go.uber.org/zap"
)

// TestStatusAfterEmptySetEndpointsPanics: SetEndpoints() with no endpoint is accepted, and a later
// Maintenance.Status (which dials the endpoint through Client.Dial) indexes c.endpoints[0] and
// panics instead of returning an error. No server is needed: the dial happens before any RPC.
func TestStatusAfterEmptySetEndpointsPanics(t *testing.T) {
	cli, err := clientv3.New(clientv3.Config{Endpoints: []string{"127.0.0.1:1"}, Logger: zap.NewNop()})
	if err != nil {
		t.Fatal(err)
	}
	defer cli.Close()
	cli.SetEndpoints()
	defer func() {
		if r := recover(); r != nil {
			t.Fatalf("Status panicked after SetEndpoints(): %v", r)
		}
	}()
	ctx, cancel := context.WithTimeout(context.Background(), time.Second)
	defer cancel()
	_, _ = cli.Maintenance.Status(ctx, "127.0.0.1:1")
}
