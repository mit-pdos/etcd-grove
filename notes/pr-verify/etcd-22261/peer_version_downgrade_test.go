// Copyright 2026 The etcd Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

package rafthttp

import (
	"net/http"
	"net/http/httptest"
	"strings"
	"sync/atomic"
	"testing"

	"go.uber.org/zap/zaptest"

	"go.etcd.io/etcd/api/v3/version"
	"go.etcd.io/etcd/client/pkg/v3/types"
)

// TestPeerVersionCacheStaleAfterDowngrade: a member built with a "v"-prefixed Version (as
// etcd#20915 builds it) learns a peer's version from a stream dial and keeps it until the peer is
// removed. If the peer is then downgraded to v3.7 (whose handlers parse X-Server-Version with
// coreos/go-semver and panic on a leading "v"), the member keeps sending it the "v"-prefixed
// version: every stream dial and every pipeline post to it fails, and since a failed dial gets no
// response, the cached version is never corrected.
func TestPeerVersionCacheStaleAfterDowngrade(t *testing.T) {
	defer func(v string) { version.Version = v }(version.Version)
	version.Version = "v3.8.0"

	var peerVersion atomic.Value
	peerVersion.Store("3.8.0")
	var rejected atomic.Int32
	srv := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		pv := peerVersion.Load().(string)
		if strings.HasPrefix(pv, "3.7") && strings.HasPrefix(r.Header.Get("X-Server-Version"), "v") {
			// v3.7's checkClusterCompatibilityFromHeader: serverVersion(header) is
			// semver.Must(semver.NewVersion(verStr)) of coreos/go-semver, which panics here
			// (net/http recovers and drops the connection without a response).
			rejected.Add(1)
			panic(`semver: Invalid version "` + r.Header.Get("X-Server-Version") + `"`)
		}
		w.Header().Set("X-Server-Version", pv)
		if r.Method == http.MethodPost {
			w.WriteHeader(http.StatusNoContent)
			return
		}
		w.WriteHeader(http.StatusOK)
		w.(http.Flusher).Flush()
	}))
	defer srv.Close()

	tr := &Transport{
		ID:         types.ID(2),
		ClusterID:  types.ID(1),
		streamRt:   &http.Transport{},
		pipelineRt: &http.Transport{},
	}
	sr := &streamReader{
		lg:     zaptest.NewLogger(t),
		peerID: types.ID(1),
		tr:     tr,
		picker: mustNewURLPicker(t, []string{srv.URL}),
		errorc: make(chan error, 1),
		ctx:    t.Context(),
	}

	// The peer runs v3.8: the first dial (unknown peer, "v" stripped) succeeds and caches 3.8.0.
	rc, err := sr.dial(streamTypeMessage)
	if err != nil {
		t.Fatalf("dial to the v3.8 peer: %v", err)
	}
	rc.Close()
	if v := tr.getPeerVersion(types.ID(1)); v == nil || v.String() != "3.8.0" {
		t.Fatalf("cached peer version = %v, want 3.8.0", v)
	}

	// The peer is downgraded to v3.7 (same member ID, same URL).
	peerVersion.Store("3.7.2")
	for i := 0; i < 3; i++ {
		if _, err := sr.dial(streamTypeMessage); err == nil {
			t.Fatalf("dial #%d to the downgraded peer succeeded", i)
		} else {
			t.Logf("dial #%d to the downgraded peer: %v", i, err)
		}
	}
	p := startTestPipeline(t, tr, mustNewURLPicker(t, []string{srv.URL}))
	err = p.post([]byte("some data"))
	p.stop()
	if err == nil {
		t.Fatal("pipeline post to the downgraded peer succeeded")
	}
	t.Logf("pipeline post to the downgraded peer: %v", err)
	if v := tr.getPeerVersion(types.ID(1)); v == nil || v.String() != "3.8.0" {
		t.Fatalf("cached peer version = %v, want the stale 3.8.0", v)
	}
	t.Logf("still cached: %v; requests the downgraded peer rejected: %d; header sent: %q",
		tr.getPeerVersion(types.ID(1)), rejected.Load(), version.VersionForPeer(tr.getPeerVersion(types.ID(1))))

	// A member that did not cache the peer's version (a restarted one) reaches it.
	tr2 := &Transport{ID: types.ID(3), ClusterID: types.ID(1), streamRt: &http.Transport{}}
	sr.tr = tr2
	rc, err = sr.dial(streamTypeMessage)
	if err != nil {
		t.Fatalf("dial from a member with no cached version: %v", err)
	}
	rc.Close()
	t.Errorf("BUG: after the downgrade the member can no longer reach the peer (stale cached version 3.8.0, header %q), while a member without the cache can",
		version.VersionForPeer(tr.getPeerVersion(types.ID(1))))
}
