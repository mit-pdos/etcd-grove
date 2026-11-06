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
	"crypto/sha1"
	"encoding/binary"
	"errors"
	"fmt"
	"os"
	"sync"
	"sync/atomic"
	"testing"

	"go.etcd.io/etcd/api/v3/v3rpc/rpctypes"
	"go.etcd.io/etcd/tests/v3/framework/integration"
)

// TestLeaseGrantNoIDCollidesAcrossMembers grants leases without an ID through
// two members of a 3-member cluster whose member IDs agree in their low 15 bits
// but not in the 16th. The server chooses the ID (rpc.proto: "If ID is set to
// 0, the lessor chooses an ID"), so a Grant should never fail because the ID
// it chose is taken.
func TestLeaseGrantNoIDCollidesAcrossMembers(t *testing.T) {
	integration.BeforeTest(t)

	// The framework names member i's peer URL after the listener counter
	// (integration.NewLocalListener): find a counter value that gives two
	// members IDs agreeing in the low 15 bits only.
	peerURL := func(c int32) string {
		return fmt.Sprintf("%s://127.0.0.1:%05d%05d", integration.URLScheme, c+integration.BasePort, os.Getpid())
	}
	predict := func(c0 int32) [3]uint64 {
		var ids [3]uint64
		for i := int32(0); i < 3; i++ {
			// MustNewMember: UniqNumber, then the peer listener, then the client
			// listener. A member of a new cluster has the ID of its peer URLs and
			// cluster token (membership.computeMemberID).
			h := sha1.Sum([]byte(peerURL(c0+3*i+2) + integration.ClusterName))
			ids[i] = binary.BigEndian.Uint64(h[:8])
		}
		return ids
	}
	start := atomic.LoadInt32(&integration.UniqueCount)
	c0, ia, ib := int32(-1), -1, -1
	for c := start; c < start+1000000 && c0 < 0; c++ {
		ids := predict(c)
		for i := 0; i < 3 && c0 < 0; i++ {
			for j := i + 1; j < 3; j++ {
				if (ids[i]^ids[j])&0xffff == 0x8000 {
					c0, ia, ib = c, i, j
					break
				}
			}
		}
	}
	if c0 < 0 {
		t.Skip("no listener counter gives two member IDs agreeing in the low 15 bits only")
	}
	atomic.StoreInt32(&integration.UniqueCount, c0)

	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 3})
	defer clus.Terminate(t)

	want := predict(c0)
	for i, m := range clus.Members {
		if uint64(m.Server.MemberID()) != want[i] {
			t.Fatalf("member %d has ID %x, predicted %x", i, uint64(m.Server.MemberID()), want[i])
		}
	}
	t.Logf("members %d and %d have IDs %x and %x", ia, ib, want[ia], want[ib])

	ctx := context.Background()
	const ttl = 3600
	grant := func(member, other int) int64 {
		resp, err := clus.Client(member).Grant(ctx, ttl)
		if errors.Is(err, rpctypes.ErrLeaseExist) {
			t.Fatalf("Grant without an ID through member %d failed: %v (the ID it chose is a lease granted through member %d)", member, err, other)
		}
		if err != nil {
			t.Fatal(err)
		}
		return int64(resp.ID)
	}
	la := grant(ia, ib)
	lb := grant(ib, ia)
	const suffixMask = 1<<48 - 1
	// The member whose IDs are behind will reach the other's.
	behind, ahead := ia, ib
	gap := lb&suffixMask - la&suffixMask
	if gap < 0 {
		behind, ahead, gap = ib, ia, -gap
	}
	t.Logf("first leases %x (member %d) and %x (member %d): member %d is %d IDs behind", la, ia, lb, ib, behind, gap)

	// A few more leases through the member ahead. Every request also takes an
	// ID for its raft entry, so a Grant takes two IDs and a Put one: the Puts
	// give the member ahead leases with both odd and even IDs.
	for i := 0; i < 10; i++ {
		grant(ahead, behind)
		if _, err := clus.Client(ahead).Put(ctx, "k", "v"); err != nil {
			t.Fatal(err)
		}
	}

	// Grant through the member behind until its IDs are past the other's.
	n := gap + 100
	var next atomic.Int64
	var wg sync.WaitGroup
	var stopped atomic.Bool
	errc := make(chan error, 64)
	cli := clus.Client(behind)
	for w := 0; w < 64; w++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			for next.Add(1) <= n && !stopped.Load() {
				if _, err := cli.Grant(ctx, ttl); err != nil {
					stopped.Store(true)
					errc <- err
					return
				}
			}
		}()
	}
	wg.Wait()
	close(errc)
	for err := range errc {
		if errors.Is(err, rpctypes.ErrLeaseExist) {
			t.Fatalf("Grant without an ID through member %d failed: %v (the ID it chose is a lease granted through member %d)", behind, err, ahead)
		}
		t.Fatal(err)
	}
}
