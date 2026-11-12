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
	"errors"
	"fmt"
	"sync"
	"testing"
	"time"

	"github.com/stretchr/testify/require"

	"go.etcd.io/etcd/api/v3/v3rpc/rpctypes"
	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/tests/v3/framework/integration"
)

// TestV3SerializableReadsOnRemovedMember removes a member while clients send it
// serializable reads. The removed member stops; the reads in flight should
// fail, not crash the process.
func TestV3SerializableReadsOnRemovedMember(t *testing.T) {
	integration.BeforeTest(t)

	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 3})
	defer clus.Terminate(t)

	ctx := t.Context()
	cli := clus.Client(0)
	for i := 0; i < 2000; i++ {
		_, err := cli.Put(ctx, fmt.Sprintf("k%05d", i), "v")
		require.NoError(t, err)
	}

	target := clus.Members[2]
	tcli, err := integration.NewClient(t, clientv3.Config{Endpoints: []string{target.GRPCURL}})
	require.NoError(t, err)
	defer tcli.Close()

	stop := make(chan struct{})
	var wg sync.WaitGroup
	for g := 0; g < 8; g++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			for {
				select {
				case <-stop:
					return
				default:
				}
				rctx, cancel := context.WithTimeout(context.Background(), time.Second)
				tcli.Get(rctx, "k", clientv3.WithPrefix(), clientv3.WithSerializable())
				cancel()
			}
		}()
	}
	time.Sleep(200 * time.Millisecond)

	// The remove is refused until every member has been connected for a while.
	deadline := time.Now().Add(20 * time.Second)
	for {
		_, err = cli.MemberRemove(ctx, uint64(target.Server.MemberID()))
		if err == nil || !errors.Is(err, rpctypes.ErrUnhealthy) || time.Now().After(deadline) {
			break
		}
		time.Sleep(500 * time.Millisecond)
	}
	require.NoError(t, err)
	select {
	case <-target.Server.StopNotify():
	case <-time.After(10 * time.Second):
		t.Fatal("the removed member did not stop")
	}
	time.Sleep(2 * time.Second) // the reads go on against the stopped member
	close(stop)
	wg.Wait()

	target.Terminate(t)
	clus.Members = clus.Members[:2]
}
