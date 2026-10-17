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
	"sync/atomic"
	"testing"
	"time"

	"github.com/stretchr/testify/require"
	"google.golang.org/grpc"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/client/v3/concurrency"
	"go.etcd.io/etcd/tests/v3/framework/integration"
)

// TestProbeTryLockDeleteUnfenced shows that TryLock's "cannot lock, so delete the key"
// path still deletes by key name only (etcd-io/etcd#22115 fences Unlock, not TryLock).
//
// Mutex A on session S calls TryLock while C (another session) holds the lock. A's
// transaction creates pfx/<lease S> at revision rA; A is not the owner, so it deletes
// its key. Just before that delete reaches etcd (an interceptor runs the hook), the
// key is deleted and Mutex B on the same session S calls Lock, which re-creates
// pfx/<lease S> at a newer revision and starts waiting behind C. A's delete then
// removes B's incarnation: B's place in the queue is lost while B is waiting.
//
// The probe passes when the bug is present (B's key is gone after A's TryLock).
func TestProbeTryLockDeleteUnfenced(t *testing.T) {
	var hook atomic.Pointer[func()]
	beforeDelete := func(ctx context.Context, method string, req, reply any,
		cc *grpc.ClientConn, invoker grpc.UnaryInvoker, opts ...grpc.CallOption,
	) error {
		if method == pb.KV_DeleteRange_FullMethodName {
			if h := hook.Swap(nil); h != nil {
				(*h)()
			}
		}
		return invoker(ctx, method, req, reply, cc, opts...)
	}

	cliS, err := integration.NewClient(t, clientv3.Config{
		Endpoints:   exampleEndpoints(),
		DialOptions: []grpc.DialOption{grpc.WithChainUnaryInterceptor(beforeDelete)},
	})
	require.NoError(t, err)
	defer cliS.Close()
	cliC, err := integration.NewClient(t, clientv3.Config{Endpoints: exampleEndpoints()})
	require.NoError(t, err)
	defer cliC.Close()

	sC, err := concurrency.NewSession(cliC)
	require.NoError(t, err)
	defer sC.Close()
	sS, err := concurrency.NewSession(cliS)
	require.NoError(t, err)
	defer sS.Close()

	ctx := t.Context()
	pfx := "/probe-trylock/"
	mC := concurrency.NewMutex(sC, pfx)
	require.NoError(t, mC.Lock(ctx))

	mA := concurrency.NewMutex(sS, pfx)
	mB := concurrency.NewMutex(sS, pfx)
	bLocked := make(chan error, 1)
	var bRev int64
	h := func() {
		k := mA.Key()
		// The key A just created is deleted (as by another handle of session S) ...
		_, derr := cliC.Delete(ctx, k)
		require.NoError(t, derr)
		// ... and B, on the same session, re-creates it and waits behind C.
		go func() { bLocked <- mB.Lock(ctx) }()
		require.Eventually(t, func() bool {
			g, gerr := cliC.Get(ctx, k)
			if gerr != nil || len(g.Kvs) != 1 {
				return false
			}
			bRev = g.Kvs[0].CreateRevision
			return true
		}, 5*time.Second, 10*time.Millisecond)
	}
	hook.Store(&h)

	require.ErrorIs(t, mA.TryLock(ctx), concurrency.ErrLocked)
	require.NotZero(t, bRev, "B re-created the key")

	g, err := cliC.Get(ctx, mB.Key())
	require.NoError(t, err)
	// The bug: A's TryLock deleted B's newer incarnation of the shared key.
	require.Empty(t, g.Kvs, "TryLock's delete removed the key B re-created at revision %d", bRev)

	require.NoError(t, mC.Unlock(ctx))
	select {
	case err := <-bLocked:
		t.Logf("B's Lock returned %v after its key was deleted by A's TryLock", err)
	case <-time.After(5 * time.Second):
		t.Logf("B's Lock still waiting")
	}
}
