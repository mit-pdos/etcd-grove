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

// After a --force-new-cluster restart (membership ConfChangeAddNode entries still
// in the WAL), a second, ordinary restart: does the member still dial the dropped
// peers?
func TestForceNewClusterThenPlainRestartDials(t *testing.T) {
	integration.BeforeTest(t)
	c := integration.NewCluster(t, &integration.ClusterConfig{Size: 3})
	defer c.Terminate(t)
	ctx, cancel := context.WithTimeout(t.Context(), integration.RequestTimeout)
	_, err := c.Members[0].Client.Put(ctx, "/foo", "bar")
	cancel()
	require.NoError(t, err)

	addrs := []string{c.Members[1].PeerURLs[0].Host, c.Members[2].PeerURLs[0].Host}
	c.Members[0].Stop(t)
	c.Members[1].Terminate(t)
	c.Members[2].Terminate(t)
	c.Members[0].ForceNewCluster = true
	require.NoError(t, c.Members[0].Restart(t))
	c.WaitMembersForLeader(t, c.Members[:1])
	time.Sleep(time.Second)
	t.Logf("after force-new-cluster: dials=%d", countDials(t, addrs))

	c.Members[0].Stop(t)
	c.Members[0].ForceNewCluster = false
	require.NoError(t, c.Members[0].Restart(t))
	c.WaitMembersForLeader(t, c.Members[:1])
	require.Len(t, c.Members[0].Server.Cluster().Members(), 1)
	time.Sleep(time.Second)
	n := countDials(t, addrs)
	t.Logf("after plain restart: dials=%d", n)
	require.Zero(t, n)
}

func countDials(t *testing.T, addrs []string) int64 {
	var dials atomic.Int64
	var lns []net.Listener
	for _, addr := range addrs {
		ln, lerr := transport.NewUnixListener(addr)
		require.NoError(t, lerr)
		lns = append(lns, ln)
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
	for _, ln := range lns {
		ln.Close()
	}
	return dials.Load()
}
