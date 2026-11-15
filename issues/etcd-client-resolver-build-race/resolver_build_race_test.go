package clientv3_test

import (
	"context"
	"net"
	"testing"
	"time"

	clientv3 "go.etcd.io/etcd/client/v3"
)

// TestSetEndpointsRacesFirstRPC: a new client's channel is idle until its first RPC, which makes
// grpc build the client's resolver (EtcdManualResolver.Build, on grpc's serializer goroutine).
// Build writes the resolver's serviceConfig and reads its endpoints; a concurrent SetEndpoints
// (a caller's, or auto-sync's) reads and writes the same fields under the client's epMu only,
// which Build does not take. Run with -race. No server is needed: Build runs whether or not the
// connection succeeds.
func TestSetEndpointsRacesFirstRPC(t *testing.T) {
	ln, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	defer ln.Close()
	ep := ln.Addr().String()
	for i := 0; i < 20; i++ {
		cli, err := clientv3.New(clientv3.Config{Endpoints: []string{ep}, DialTimeout: time.Second})
		if err != nil {
			t.Fatal(err)
		}
		done := make(chan struct{})
		go func() {
			defer close(done)
			cli.SetEndpoints(ep)
		}()
		ctx, cancel := context.WithTimeout(context.Background(), 20*time.Millisecond)
		_, _ = cli.Get(ctx, "k")
		cancel()
		<-done
		cli.Close()
	}
}
