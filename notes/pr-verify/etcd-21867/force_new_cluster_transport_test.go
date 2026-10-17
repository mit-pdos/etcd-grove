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
	"context"
	"net"
	"sync/atomic"
	"testing"
	"time"

	"github.com/stretchr/testify/require"

	"go.etcd.io/etcd/client/pkg/v3/transport"
	"go.etcd.io/etcd/tests/v3/framework/integration"
)

// TestForceNewClusterStopsDialingRemovedPeers checks that, once a member
// restarted with --force-new-cluster has settled as a one-member cluster, its
// peer transport no longer dials the members that were dropped: after the
// restart, a listener on a dropped member's peer address must see no
// connection attempts.
func TestForceNewClusterStopsDialingRemovedPeers(t *testing.T) {
	testForceNewClusterStopsDialingRemovedPeers(t, 0, 1)
}

// The same once a snapshot covers the membership entries: the restart replays no
// ConfChangeAddNode entry.
func TestForceNewClusterStopsDialingRemovedPeersAfterSnapshot(t *testing.T) {
	testForceNewClusterStopsDialingRemovedPeers(t, 10, 30)
}

func testForceNewClusterStopsDialingRemovedPeers(t *testing.T, snapshotCount uint64, puts int) {
	integration.BeforeTest(t)
	c := integration.NewCluster(t, &integration.ClusterConfig{Size: 3, SnapshotCount: snapshotCount})
	defer c.Terminate(t)

	for i := 0; i < puts; i++ {
		ctx, cancel := context.WithTimeout(t.Context(), integration.RequestTimeout)
		_, err := c.Members[0].Client.Put(ctx, "/foo", "bar")
		cancel()
		require.NoError(t, err)
	}

	addr1 := c.Members[1].PeerURLs[0].Host
	addr2 := c.Members[2].PeerURLs[0].Host

	c.Members[0].Stop(t)
	c.Members[1].Terminate(t)
	c.Members[2].Terminate(t)
	c.Members[0].ForceNewCluster = true
	require.NoError(t, c.Members[0].Restart(t))
	c.WaitMembersForLeader(t, c.Members[:1])
	require.Len(t, c.Members[0].Server.Cluster().Members(), 1)

	// Let the force-new-cluster config change entries apply.
	time.Sleep(time.Second)

	var dials atomic.Int64
	for _, addr := range []string{addr1, addr2} {
		ln, lerr := transport.NewUnixListener(addr)
		require.NoError(t, lerr)
		defer ln.Close()
		go func(ln net.Listener) {
			for {
				conn, aerr := ln.Accept()
				if aerr != nil {
					return
				}
				dials.Add(1)
				conn.Close()
			}
		}(ln)
	}
	time.Sleep(2 * time.Second)
	require.Zerof(t, dials.Load(), "the force-new-cluster member still dials removed peers (%d connections in 2s)", dials.Load())
}
