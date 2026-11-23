//go:build !rpcmodel

// (The model build needs the kit's codec, registered by examples/quepaxanet; the listener path is the same in both builds.)

package raxos

import (
	"context"
	"net"
	"strings"
	"testing"
	"time"

	"google.golang.org/grpc"
)

// TestR1RecorderListenFails (finding R1): a recorder whose gRPC listener cannot be made (its port
// is taken) must not end the replica; it serves once the port is free.
func TestR1RecorderListenFails(t *testing.T) {
	l, err := net.Listen("tcp", "0.0.0.0:0") // the recorder's port, taken
	if err != nil {
		t.Fatal(err)
	}
	port := l.Addr().String()[strings.LastIndex(l.Addr().String(), ":")+1:]
	cfg := testConfig()
	cfg.Peers[0].RECORDERPORT = port
	rec := NewRecorder(cfg, &ClientBatchStore{}, make(chan Decision, 100), 1, false, 0)
	rec.NetworkInit()
	time.Sleep(200 * time.Millisecond)
	l.Close()
	conn, err := grpc.Dial("127.0.0.1:"+port, grpc.WithInsecure())
	if err != nil {
		t.Fatal(err)
	}
	c := NewConsensusClient(conn)
	for i := 0; ; i++ {
		ctx, cancel := context.WithTimeout(context.Background(), time.Second)
		_, err := c.FetchBatches(ctx, &DecideRequest{Ids: []string{"x"}})
		cancel()
		if err == nil {
			break
		}
		if i == 50 {
			t.Fatalf("the recorder does not serve: %v", err)
		}
		time.Sleep(100 * time.Millisecond)
	}
}
