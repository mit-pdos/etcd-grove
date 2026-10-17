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

	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/client/v3/concurrency"
	"go.etcd.io/etcd/tests/v3/framework/integration"
)

// hookFinalGet runs hook once, just before the first single-key Get (no
// options) of key after it is armed: Mutex.Lock's final existence check.
type hookFinalGet struct {
	clientv3.KV
	key   atomic.Value // string
	armed atomic.Bool
	hook  func()
}

func (k *hookFinalGet) Get(ctx context.Context, key string, opts ...clientv3.OpOption) (*clientv3.GetResponse, error) {
	if len(opts) == 0 {
		if want, _ := k.key.Load().(string); want == key && k.armed.CompareAndSwap(true, false) {
			k.hook()
		}
	}
	return k.KV.Get(ctx, key, opts...)
}

// TestMutexLockRecreatedAfterWait: B (session S) waits behind C. C unlocks;
// B's waitDeletes returns nil (its waitKey watch is gone). Before B's final
// Get, another Mutex A of session S unlocks (deletes the shared key) and locks
// again (recreating it after D's key). D (session U), which waited on S's old
// key, gets the lock; B's final Get only sees that the key exists and returns
// nil too.
func TestMutexLockRecreatedAfterWait(t *testing.T) {
	const pfx = "/mutex-recreated-after-wait"

	cli, err := integration.NewClient(t, clientv3.Config{Endpoints: exampleEndpoints()})
	require.NoError(t, err)
	defer cli.Close()
	cliS, err := integration.NewClient(t, clientv3.Config{Endpoints: exampleEndpoints()})
	require.NoError(t, err)
	defer cliS.Close()
	hk := &hookFinalGet{KV: cliS.KV}
	cliS.KV = hk

	sC, err := concurrency.NewSession(cli)
	require.NoError(t, err)
	defer sC.Close()
	sS, err := concurrency.NewSession(cliS)
	require.NoError(t, err)
	defer sS.Close()
	sU, err := concurrency.NewSession(cli)
	require.NoError(t, err)
	defer sU.Close()

	mC := concurrency.NewMutex(sC, pfx)
	require.NoError(t, mC.Lock(t.Context()))

	mB := concurrency.NewMutex(sS, pfx)
	bDone := make(chan error, 1)
	go func() { bDone <- mB.Lock(t.Context()) }()
	waitKeys := func(n int) {
		require.Eventually(t, func() bool {
			r, gerr := cli.Get(t.Context(), pfx+"/", clientv3.WithPrefix())
			return gerr == nil && len(r.Kvs) == n
		}, 5*time.Second, 10*time.Millisecond)
	}
	waitKeys(2)
	mD := concurrency.NewMutex(sU, pfx)
	dDone := make(chan error, 1)
	go func() { dDone <- mD.Lock(t.Context()) }()
	waitKeys(3)
	time.Sleep(300 * time.Millisecond) // let the watches register

	sKey := mB.Key()
	aCtx, aCancel := context.WithCancel(t.Context())
	defer aCancel()
	hk.hook = func() {
		// A (session S): its canceled Lock's Unlock deletes the shared key...
		_, herr := cli.Delete(t.Context(), sKey)
		require.NoError(t, herr)
		// ...and it locks again, recreating the key after D's.
		mA := concurrency.NewMutex(sS, pfx)
		go func() { _ = mA.Lock(aCtx) }()
		waitKeys(2)
		time.Sleep(300 * time.Millisecond) // D acquires
	}
	hk.key.Store(sKey)
	hk.armed.Store(true)
	require.NoError(t, mC.Unlock(t.Context()))

	var bErr, dErr error
	select {
	case dErr = <-dDone:
	case <-time.After(5 * time.Second):
		t.Fatal("D did not get the lock")
	}
	select {
	case bErr = <-bDone:
	case <-time.After(5 * time.Second):
		t.Fatal("B did not return")
	}
	t.Logf("D: %v, B: %v", dErr, bErr)
	require.NoError(t, dErr)
	require.Errorf(t, bErr, "B's Lock returned nil while D (another session) holds the lock")
}
