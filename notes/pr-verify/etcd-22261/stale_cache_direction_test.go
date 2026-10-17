package rafthttp

import (
	"net/http"
	"net/http/httptest"
	"testing"
	"time"

	"github.com/Masterminds/semver/v3"

	"go.etcd.io/etcd/api/v3/version"
	"go.etcd.io/etcd/client/pkg/v3/types"
)

// TestStaleCacheWhichDirectionBreaks: with a stale cached version 3.8.0 for peer 2 (now a v3.7
// member), this member's streamHandler still answers peer 2's stream dials with the stripped
// version (it looks at the request header, not the cache), so the streams peer 2 dials into us
// (which carry our raft messages to peer 2) keep working; the cache is not corrected by them, so
// the headers of our own requests to peer 2 (stream dial, pipeline post, snapshot) stay "v"-prefixed.
func TestStaleCacheWhichDirectionBreaks(t *testing.T) {
	defer func(v string) { version.Version = v }(version.Version)
	version.Version = "v3.8.0"

	tr := &Transport{}
	tr.setPeerVersion(types.ID(2), semver.MustParse("3.8.0")) // learned before the downgrade

	req, _ := http.NewRequest(http.MethodGet, "http://localhost:2380"+RaftStreamPrefix+"/message/2", nil)
	req.Header.Set("X-Etcd-Cluster-ID", "1")
	req.Header.Set("X-Server-Version", "3.7.0") // peer 2, now v3.7
	req.Header.Set("X-Raft-To", "1")
	peer := newFakePeer()
	h := newStreamHandler(tr, &fakePeerGetter{peers: map[types.ID]Peer{types.ID(2): peer}}, &fakeRaft{}, types.ID(1), types.ID(1))
	rw := httptest.NewRecorder()
	go h.ServeHTTP(rw, req)
	select {
	case conn := <-peer.connc:
		defer conn.Close()
	case <-time.After(time.Second):
		t.Fatalf("stream from the v3.7 peer not attached")
	}
	t.Logf("response to v3.7 peer's dial: X-Server-Version=%q (v3.7 parses it)", rw.Header().Get("X-Server-Version"))
	if g := rw.Header().Get("X-Server-Version"); g != "3.8.0" {
		t.Errorf("handler reply = %q", g)
	}
	out := version.VersionForPeer(tr.getPeerVersion(types.ID(2)))
	t.Logf("cache after serving: %v; header our dials/posts/snapshots to peer 2 send: %q", tr.getPeerVersion(types.ID(2)), out)
	if out != "3.8.0" {
		t.Logf("CONFIRMED: inbound streams work, outbound requests (incl. snapshotSender) still send %q", out)
	}
}

// Pre-release versions sort below V3_8, so a peer at 3.8.0-rc.0 (a Masterminds build that could
// parse "v") gets the stripped version: conservative, harmless.
func TestPrereleasePeer(t *testing.T) {
	defer func(v string) { version.Version = v }(version.Version)
	version.Version = "v3.8.0-rc.0"
	for _, pv := range []string{"3.8.0-alpha.0", "v3.8.0-rc.0", "3.8.0", "3.7.9", "3.9.0-alpha.0"} {
		t.Logf("peer %-14s -> %q", pv, version.VersionForPeer(semver.MustParse(pv)))
	}
}
