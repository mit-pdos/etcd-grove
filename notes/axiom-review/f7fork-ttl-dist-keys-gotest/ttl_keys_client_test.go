// Review f7fork-ttl-dist-keys (2026-11-26): does the client's LeaseTimeToLiveResponse.Keys
// (lease.go:257, the decoded pb response's slice) stay unchanged after TimeToLive returns,
// through grpc v1.84's pooled receive buffers (codec v2: MaterializeToBuffer, then Free)?
// Run in a copy of the fork's client/v3 (with ../pkg and ../../api beside it):
//   cp ttl_keys_client_test.go <copy>/client/v3/ && cd <copy>/client/v3 &&
//   GOTOOLCHAIN=go1.27.3 go test -count=1 -run TestF7forkTTLKeys -v .
package clientv3_test

import (
	"bytes"
	"context"
	"net"
	"sync"
	"sync/atomic"
	"testing"
	"time"
	"unsafe"

	"google.golang.org/grpc"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	clientv3 "go.etcd.io/etcd/client/v3"
)

type ttlServer struct {
	pb.UnimplementedLeaseServer
	n atomic.Uint64
}

const nKeys, keyLen = 8, 200

// Each reply's keys are nKeys keys of keyLen bytes, every byte the reply's counter (mod 251),
// plus one empty key: replies of equal size, so grpc's pool hands the same buffers back.
func (s *ttlServer) LeaseTimeToLive(_ context.Context, r *pb.LeaseTimeToLiveRequest) (*pb.LeaseTimeToLiveResponse, error) {
	c := byte(s.n.Add(1) % 251)
	ks := make([][]byte, 0, nKeys+1)
	for i := 0; i < nKeys; i++ {
		ks = append(ks, bytes.Repeat([]byte{c}, keyLen))
	}
	ks = append(ks, []byte{})
	return &pb.LeaseTimeToLiveResponse{Header: &pb.ResponseHeader{}, ID: r.ID, Keys: ks}, nil
}

func TestF7forkTTLKeys(t *testing.T) {
	lis, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	gs := grpc.NewServer()
	pb.RegisterLeaseServer(gs, &ttlServer{})
	go gs.Serve(lis)
	defer gs.Stop()

	cli, err := clientv3.New(clientv3.Config{Endpoints: []string{lis.Addr().String()}, DialTimeout: 5 * time.Second})
	if err != nil {
		t.Fatal(err)
	}
	defer cli.Close()

	type got struct {
		keys [][]byte
		want [][]byte
	}
	var mu sync.Mutex
	var all []got
	var wg sync.WaitGroup
	const workers, per = 8, 500
	for w := 0; w < workers; w++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			for i := 0; i < per; i++ {
				resp, err := cli.TimeToLive(context.Background(), 7, clientv3.WithAttachedKeys())
				if err != nil {
					t.Error(err)
					return
				}
				want := make([][]byte, len(resp.Keys))
				for j, k := range resp.Keys {
					want[j] = append([]byte(nil), k...)
				}
				// The caller writing its keys (it owns them in Go) must not reach later replies.
				if i%2 == 0 {
					for _, k := range resp.Keys {
						for b := range k {
							k[b] = 0xEE
						}
					}
					for j, k := range resp.Keys {
						want[j] = append(want[j][:0], k...)
					}
				}
				mu.Lock()
				all = append(all, got{resp.Keys, want})
				mu.Unlock()
			}
		}()
	}
	wg.Wait()

	// 1. every reply's keys are unchanged since its TimeToLive returned (4000 later calls reused the pool)
	changed := 0
	for _, g := range all {
		if len(g.keys) != nKeys+1 {
			t.Fatalf("got %d keys", len(g.keys))
		}
		for j := range g.keys {
			if !bytes.Equal(g.keys[j], g.want[j]) {
				changed++
			}
		}
	}
	// 2. no two non-empty keys of live replies share memory; empty keys have cap 0
	type rng struct{ lo, hi uintptr }
	var rs []rng
	empties, emptyCapNonzero := 0, 0
	for _, g := range all {
		for _, k := range g.keys {
			if len(k) == 0 {
				empties++
				if cap(k) != 0 {
					emptyCapNonzero++
				}
				continue
			}
			p := uintptr(unsafe.Pointer(unsafe.SliceData(k)))
			rs = append(rs, rng{p, p + uintptr(cap(k))})
		}
	}
	seen := map[uintptr]bool{}
	dup := 0
	for _, r := range rs {
		if seen[r.lo] {
			dup++
		}
		seen[r.lo] = true
	}
	t.Logf("replies %d, non-empty keys %d, changed %d, shared starts %d, empty keys %d (cap>0: %d)",
		len(all), len(rs), changed, dup, empties, emptyCapNonzero)
	if changed != 0 || dup != 0 || emptyCapNonzero != 0 {
		t.Fatal("a reply's keys changed or were shared")
	}
}
