// F7 fork (2026-11-26): does the follower's decode of a forwarded TimeToLive reply alias the HTTP
// body? Run from the fork's server/ module: cp this file to server/lease/leasehttp/ and
// `go test -run TestF7forkUnmarshalKeysNoAlias ./lease/leasehttp/`.
package leasehttp

import (
	"bytes"
	"testing"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/server/v3/lease/leasepb"
	"google.golang.org/protobuf/proto"
)

func TestF7forkUnmarshalKeysNoAlias(t *testing.T) {
	keys := [][]byte{[]byte("z/lease"), []byte("a/other-key")}
	b, err := proto.Marshal(&leasepb.LeaseInternalResponse{
		LeaseTimeToLiveResponse: &pb.LeaseTimeToLiveResponse{
			Header: &pb.ResponseHeader{}, ID: 7, TTL: 5, GrantedTTL: 10, Keys: keys,
		},
	})
	if err != nil {
		t.Fatal(err)
	}
	// exactly the follower's decode in TimeToLiveHTTP (http.go)
	lresp := &leasepb.LeaseInternalResponse{}
	if err := proto.Unmarshal(b, lresp); err != nil {
		t.Fatal(err)
	}
	got := lresp.LeaseTimeToLiveResponse.Keys
	// overwrite the body buffer: an aliased key would change with it
	for i := range b {
		b[i] = 0xff
	}
	for i, k := range got {
		if !bytes.Equal(k, keys[i]) {
			t.Fatalf("key %d aliases the body buffer: %q", i, k)
		}
		// and no key's backing array lies inside b (capacity-extended view)
		if cap(k) > 0 {
			k = k[:cap(k)]
			for j := range k {
				k[j] = 0
			}
		}
	}
	for i := range b {
		if b[i] != 0xff {
			t.Fatalf("writing a decoded key wrote the body buffer at %d", i)
		}
	}
}
