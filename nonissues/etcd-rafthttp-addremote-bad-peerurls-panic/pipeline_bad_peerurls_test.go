// Test of nonissues/etcd-rafthttp-addremote-bad-peerurls-panic.md: copy into
// server/etcdserver/api/rafthttp/ and run
// `go test ./etcdserver/api/rafthttp -run '^TestPipelineHandlerBadPeerURLs$'` from server/.
// It uses the package's test helper fakeRaft (http_test.go).
package rafthttp

import (
	"bytes"
	"net/http"
	"net/http/httptest"
	"testing"

	"go.uber.org/zap/zaptest"

	"go.etcd.io/etcd/api/v3/version"
	"go.etcd.io/etcd/client/pkg/v3/types"
	stats "go.etcd.io/etcd/server/v3/etcdserver/api/v2stats"
	"go.etcd.io/etcd/pkg/v3/pbutil"
	"go.etcd.io/raft/v3/raftpb"
)

// TestPipelineHandlerBadPeerURLs: a raft message from an id that is not a peer, with an
// X-PeerURLs header that does not parse, gets an HTTP response; the handler does not panic (which
// net/http recovers by logging the stack and dropping the connection).
func TestPipelineHandlerBadPeerURLs(t *testing.T) {
	lg := zaptest.NewLogger(t)
	tr := &Transport{
		Logger:      lg,
		ID:          types.ID(1),
		ServerStats: stats.NewServerStats("", ""),
		LeaderStats: stats.NewLeaderStats(lg, ""),
		peers:       make(map[types.ID]Peer),
		remotes:     make(map[types.ID]*remote),
	}
	srv := httptest.NewServer(newPipelineHandler(tr, &fakeRaft{}, types.ID(0)))
	defer srv.Close()

	req, err := http.NewRequest(http.MethodPost, srv.URL+RaftPrefix,
		bytes.NewReader(pbutil.MustMarshalMessage(&raftpb.Message{})))
	if err != nil {
		t.Fatal(err)
	}
	req.Header.Set("X-Etcd-Cluster-ID", "0")
	req.Header.Set("X-Server-Version", version.Version)
	req.Header.Set("X-Server-From", "5")
	req.Header.Set("X-PeerURLs", "not a url")
	resp, err := http.DefaultClient.Do(req)
	if err != nil {
		t.Fatalf("no response to a request with a malformed X-PeerURLs: %v", err)
	}
	resp.Body.Close()
	t.Logf("status %d", resp.StatusCode)
}
