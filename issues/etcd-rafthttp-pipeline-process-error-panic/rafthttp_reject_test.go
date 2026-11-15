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

package integration

import (
	"bytes"
	"context"
	"io"
	"net"
	"net/http"
	"testing"
	"time"

	"github.com/stretchr/testify/require"
	"google.golang.org/protobuf/proto"

	"go.etcd.io/etcd/api/v3/version"
	"go.etcd.io/etcd/client/pkg/v3/types"
	"go.etcd.io/etcd/tests/v3/framework/integration"
	"go.etcd.io/raft/v3/raftpb"
)

// postRaftMessage posts m to the member's raft pipeline endpoint ("/raft")
// as a peer's rafthttp pipeline does (the headers of rafthttp's
// createPostRequest), and returns the status and the error of reading the
// response body to its end (net/http cuts the body short when the handler
// panics after flushing it).
func postRaftMessage(t *testing.T, to *integration.Member, from types.ID, m *raftpb.Message) (int, error) {
	t.Helper()
	b, err := proto.Marshal(m)
	require.NoError(t, err)
	// The integration framework's peer URLs are unix sockets
	// ("unix://<path>"), served over HTTP.
	u := to.PeerURLs[0]
	req, err := http.NewRequest(http.MethodPost, "http://"+u.Host+"/raft", bytes.NewReader(b))
	require.NoError(t, err)
	req.Header.Set("Content-Type", "application/protobuf")
	req.Header.Set("X-Server-From", from.String())
	req.Header.Set("X-Server-Version", version.Version)
	req.Header.Set("X-Min-Cluster-Version", version.MinClusterVersion)
	req.Header.Set("X-Etcd-Cluster-ID", to.Server.Cluster().ID().String())
	cl := &http.Client{Transport: &http.Transport{
		DialContext: func(ctx context.Context, _, _ string) (net.Conn, error) {
			var d net.Dialer
			return d.DialContext(ctx, "unix", u.Host)
		},
	}, Timeout: 5 * time.Second}
	resp, err := cl.Do(req)
	require.NoError(t, err)
	defer resp.Body.Close()
	_, rerr := io.ReadAll(resp.Body)
	return resp.StatusCode, rerr
}

// TestRaftPipelineRejectsMisaddressedMessage: a member that receives, on its
// raft pipeline endpoint, a message addressed to another member (a peer that
// still has that member's old peer URL) should reject it with a 4xx status,
// as EtcdServer.Process asks, and not panic.
func TestRaftPipelineRejectsMisaddressedMessage(t *testing.T) {
	integration.BeforeTest(t)
	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 3})
	defer clus.Terminate(t)
	clus.WaitLeader(t)

	m0, m1, m2 := clus.Members[0], clus.Members[1], clus.Members[2]
	// What m1's pipeline sends to m2 when the URL it holds for m2 is served by m0.
	msg := &raftpb.Message{
		Type: raftpb.MsgHeartbeat.Enum(),
		From: new(uint64(m1.ID())),
		To:   new(uint64(m2.ID())),
		Term: new(m1.Server.Term()),
	}
	code, rerr := postRaftMessage(t, m0, m1.ID(), msg)
	require.NoErrorf(t, rerr, "response body cut short (status %d): the handler panicked", code)
	require.Truef(t, code >= 400 && code < 500, "status %d (%s), want a 4xx rejection", code, http.StatusText(code))
}

// TestRaftPipelineRejectsRemovedMember: a message from a removed member should
// be answered 403 Forbidden, the status EtcdServer.Process returns for it and
// that rafthttp's sender reads as "this member was removed", without a panic.
func TestRaftPipelineRejectsRemovedMember(t *testing.T) {
	integration.BeforeTest(t)
	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 3, DisableStrictReconfigCheck: true})
	defer clus.Terminate(t)
	clus.WaitLeader(t)

	m0, removed := clus.Members[0], clus.Members[2]
	removedID := removed.ID()
	term := removed.Server.Term()
	require.NoError(t, clus.RemoveMember(t, clus.Client(0), uint64(removedID)))
	require.Eventually(t, func() bool { return m0.Server.IsIDRemoved(uint64(removedID)) },
		10*time.Second, 50*time.Millisecond)

	// What the removed member's pipeline sends to m0 before it learns of its removal.
	msg := &raftpb.Message{
		Type: raftpb.MsgHeartbeatResp.Enum(),
		From: new(uint64(removedID)),
		To:   new(uint64(m0.ID())),
		Term: new(term),
	}
	code, rerr := postRaftMessage(t, m0, removedID, msg)
	require.NoErrorf(t, rerr, "response body cut short (status %d): the handler panicked", code)
	require.Equalf(t, http.StatusForbidden, code, "status %d (%s)", code, http.StatusText(code))
}
