// Test of nonissues/etcd-rafthttp-cutpeer-twice-remote-panic.md: copy into
// server/etcdserver/api/rafthttp/ and run
// `go test ./etcdserver/api/rafthttp -run '^TestTransportCutPeerTwiceRemote$'` from server/.
package rafthttp

import (
	"testing"

	"go.uber.org/zap"

	"go.etcd.io/etcd/client/pkg/v3/types"
	stats "go.etcd.io/etcd/server/v3/etcdserver/api/v2stats"
)

// TestTransportCutPeerTwiceRemote: cutting a remote twice without a mend in between should leave
// it cut, as for a peer; it panics with "close of closed channel".
func TestTransportCutPeerTwiceRemote(t *testing.T) {
	tr := &Transport{
		Logger:      zap.NewNop(),
		ID:          types.ID(1),
		ServerStats: stats.NewServerStats("", ""),
		LeaderStats: stats.NewLeaderStats(zap.NewNop(), ""),
		peers:       map[types.ID]Peer{},
		remotes:     map[types.ID]*remote{},
	}
	tr.AddRemote(types.ID(2), []string{"http://127.0.0.1:0"})
	tr.CutPeer(types.ID(2))
	defer func() {
		if r := recover(); r != nil {
			t.Fatalf("second CutPeer panicked: %v", r)
		}
	}()
	tr.CutPeer(types.ID(2))
}
