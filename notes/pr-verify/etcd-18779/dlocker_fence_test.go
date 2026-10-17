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

package concurrency_test

import (
	"context"
	"fmt"
	"testing"
	"time"

	"github.com/stretchr/testify/require"
	"google.golang.org/grpc"

	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/client/v3/concurrency"
	"go.etcd.io/etcd/tests/v3/framework/integration"
)

// TestDLockerRevFencing: successive holders of a DLocker get increasing Rev()
// values, including a holder that takes over after the previous holder's lease
// is revoked (the contrib/lock scenario); Rev() is -1 before Lock and after Unlock.
func TestDLockerRevFencing(t *testing.T) {
	integration.BeforeTest(t)
	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 1})
	defer clus.Terminate(t)
	cli := clus.RandClient()

	newSess := func() *concurrency.Session {
		s, err := concurrency.NewSession(cli)
		require.NoError(t, err)
		t.Cleanup(func() { s.Close() })
		return s
	}

	var last int64 = -1
	for i := 0; i < 3; i++ {
		l := concurrency.NewDLocker(newSess(), "/fence")
		require.Equal(t, int64(-1), l.Rev())
		l.Lock()
		rev := l.Rev()
		require.Greater(t, rev, last)
		last = rev
		l.Unlock()
		require.Equal(t, int64(-1), l.Rev())
	}

	// Holder 1's lease is revoked while it holds the lock; holder 2 acquires.
	s1 := newSess()
	l1 := concurrency.NewDLocker(s1, "/fence")
	l1.Lock()
	rev1 := l1.Rev()
	_, err := cli.Revoke(context.TODO(), s1.Lease())
	require.NoError(t, err)
	l2 := concurrency.NewDLocker(newSess(), "/fence")
	l2.Lock()
	rev2 := l2.Rev()
	require.Greater(t, rev2, rev1)
	t.Logf("holder 1 rev %d (lease revoked), holder 2 rev %d", rev1, rev2)
	// Holder 1 still reports its stale token: a storage that rejects tokens
	// below the largest one seen fences it off once holder 2 has written.
	require.Equal(t, rev1, l1.Rev())
	l2.Unlock()
}

// TestDLockerRevKeyRecreated runs the schedule of issues/mutex-lock-recreated.md
// (Mutexes A and B on one session, C and D on others): B's Lock returns nil
// while D holds the lock. Their Rev() values still order them: B's (r1) is
// below D's (r2), so a fenced resource rejects B's writes once D has written.
func TestDLockerRevKeyRecreated(t *testing.T) {
	integration.BeforeTest(t)
	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 1})
	defer clus.Terminate(t)
	cli := clus.RandClient()
	pfx := "/recreated-fence"

	txnDone := make(chan struct{}, 64)
	interceptor := func(ctx context.Context, method string, req, reply any, cc *grpc.ClientConn, invoker grpc.UnaryInvoker, opts ...grpc.CallOption) error {
		err := invoker(ctx, method, req, reply, cc, opts...)
		if method == "/etcdserverpb.KV/Txn" {
			txnDone <- struct{}{}
		}
		return err
	}
	cliS, err := integration.NewClient(t, clientv3.Config{
		Endpoints:   []string{clus.Members[0].GRPCURL},
		DialOptions: []grpc.DialOption{grpc.WithChainUnaryInterceptor(interceptor)},
	})
	require.NoError(t, err)
	defer cliS.Close()
	waitTxn := func() {
		select {
		case <-txnDone:
		case <-time.After(10 * time.Second):
			t.Fatal("no Txn")
		}
	}
	newSess := func(c *clientv3.Client) *concurrency.Session {
		s, err := concurrency.NewSession(c)
		require.NoError(t, err)
		t.Cleanup(func() { s.Close() })
		return s
	}
	keyRev := func(key string, present bool) int64 {
		var rev int64
		require.Eventually(t, func() bool {
			resp, err := cli.Get(context.TODO(), key)
			if err != nil {
				return false
			}
			if !present {
				return len(resp.Kvs) == 0
			}
			if len(resp.Kvs) == 0 {
				return false
			}
			rev = resp.Kvs[0].CreateRevision
			return true
		}, 10*time.Second, 10*time.Millisecond)
		return rev
	}
	lockAsync := func(ctx context.Context, m *concurrency.Mutex) chan error {
		ch := make(chan error, 1)
		go func() { ch <- m.Lock(ctx) }()
		return ch
	}
	wait := func(ch chan error) error {
		select {
		case err := <-ch:
			return err
		case <-time.After(10 * time.Second):
			t.Fatal("Lock did not return")
			return nil
		}
	}

	sS, sT, sU := newSess(cliS), newSess(cli), newSess(cli)
	mA, mB := concurrency.NewMutex(sS, pfx), concurrency.NewMutex(sS, pfx)
	mC, mD := concurrency.NewMutex(sT, pfx), concurrency.NewMutex(sU, pfx)
	keyA := fmt.Sprintf("%s/%x", pfx, sS.Lease())
	keyD := fmt.Sprintf("%s/%x", pfx, sU.Lease())

	require.NoError(t, mC.Lock(context.TODO()))
	ctxA, cancelA := context.WithCancel(context.TODO())
	a1 := lockAsync(ctxA, mA)
	waitTxn()
	r1 := keyRev(keyA, true)
	b := lockAsync(context.TODO(), mB)
	waitTxn()
	cancelA()
	require.Error(t, wait(a1))
	keyRev(keyA, false)
	d := lockAsync(context.TODO(), mD)
	r2 := keyRev(keyD, true)
	ctxA2, cancelA2 := context.WithCancel(context.TODO())
	defer cancelA2()
	a2 := lockAsync(ctxA2, mA)
	waitTxn()
	r3 := keyRev(keyA, true)
	require.Less(t, r1, r2)
	require.Less(t, r2, r3)

	require.NoError(t, mC.Unlock(context.TODO()))
	require.NoError(t, wait(d))
	errB := wait(b) // on the unfixed Mutex.Lock, B returns nil while D holds the lock
	t.Logf("B's Lock returned %v; B.Rev()=%d D.Rev()=%d (r1=%d r2=%d r3=%d)", errB, mB.Rev(), mD.Rev(), r1, r2, r3)
	require.NoError(t, errB)
	require.Equal(t, r1, mB.Rev())
	require.Equal(t, r2, mD.Rev())
	require.Less(t, mB.Rev(), mD.Rev())
	cancelA2()
	<-a2
}
