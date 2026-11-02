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

package lease_test

import (
	"context"
	"sync/atomic"
	"testing"
	"time"

	"github.com/stretchr/testify/require"

	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/client/v3/concurrency"
	"go.etcd.io/etcd/client/v3/leasing"
	"go.etcd.io/etcd/tests/v3/framework/integration"
)

// TestLeasingSessionExpireAfterAcquire checks that a key acquired with a
// session lease that ends before the key is cached is not served from the
// cache under the next session: writes by other clients become visible.
func TestLeasingSessionExpireAfterAcquire(t *testing.T) {
	integration.BeforeTest(t)
	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 1})
	defer clus.Terminate(t)

	cli, err := integration.NewClient(t, clientv3.Config{Endpoints: clus.Client(0).Endpoints()})
	require.NoError(t, err)
	defer cli.Close()
	kv := clus.Client(0)

	_, err = kv.Put(t.Context(), "k", "v1")
	require.NoError(t, err)

	hkv := &afterCommitKV{KV: cli.KV}
	cli.KV = hkv
	lkv, closeLKV, err := leasing.NewKV(cli, "pfx/", concurrency.WithTTL(2))
	require.NoError(t, err)
	defer closeLKV()

	// After the acquisition of k commits, and before the leasing KV caches k,
	// the session lease ends (revoked here, as when it expires) and the
	// leasing KV starts a new session.
	hook := func() {
		lresp, lerr := kv.Get(t.Context(), "pfx/k")
		if lerr != nil || len(lresp.Kvs) == 0 {
			t.Errorf("expected the leasing key of k, got %v, %v", lresp, lerr)
			return
		}
		old := clientv3.LeaseID(lresp.Kvs[0].Lease)
		if _, lerr = kv.Revoke(t.Context(), old); lerr != nil {
			t.Error(lerr)
			return
		}
		// The leasing KV grants a new lease only after it reset its cache.
		for {
			ls, lerr := kv.Leases(t.Context())
			if lerr != nil {
				t.Error(lerr)
				return
			}
			if len(ls.Leases) > 0 && ls.Leases[0].ID != old {
				return
			}
			time.Sleep(10 * time.Millisecond)
		}
	}
	hkv.hook.Store(&hook)
	resp, err := lkv.Get(t.Context(), "k")
	require.NoError(t, err)
	require.Nilf(t, hkv.hook.Load(), "expected the acquisition to commit")
	require.Len(t, resp.Kvs, 1)
	require.Equal(t, "v1", string(resp.Kvs[0].Value))

	// No client holds the lease on k: this put does not wait for any.
	_, err = kv.Put(t.Context(), "k", "v2")
	require.NoError(t, err)

	require.Eventuallyf(t, func() bool {
		resp, err := lkv.Get(t.Context(), "k")
		return err == nil && len(resp.Kvs) == 1 && string(resp.Kvs[0].Value) == "v2"
	}, 5*time.Second, 50*time.Millisecond, "expected the leasing KV to return the value put by another client")
}

// afterCommitKV runs hook (once) after a transaction commits.
type afterCommitKV struct {
	clientv3.KV
	hook atomic.Pointer[func()]
}

func (kv *afterCommitKV) Txn(ctx context.Context) clientv3.Txn {
	return &afterCommitTxn{Txn: kv.KV.Txn(ctx), kv: kv}
}

type afterCommitTxn struct {
	clientv3.Txn
	kv *afterCommitKV
}

func (txn *afterCommitTxn) If(cs ...clientv3.Cmp) clientv3.Txn {
	txn.Txn = txn.Txn.If(cs...)
	return txn
}

func (txn *afterCommitTxn) Then(ops ...clientv3.Op) clientv3.Txn {
	txn.Txn = txn.Txn.Then(ops...)
	return txn
}

func (txn *afterCommitTxn) Else(ops ...clientv3.Op) clientv3.Txn {
	txn.Txn = txn.Txn.Else(ops...)
	return txn
}

func (txn *afterCommitTxn) Commit() (*clientv3.TxnResponse, error) {
	resp, err := txn.Txn.Commit()
	if hook := txn.kv.hook.Swap(nil); hook != nil {
		(*hook)()
	}
	return resp, err
}
