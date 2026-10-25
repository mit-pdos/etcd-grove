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

package apply

import (
	"context"
	"sync/atomic"
	"testing"

	"github.com/stretchr/testify/require"
	"go.uber.org/zap/zaptest"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/pkg/v3/featuregate"
	"go.etcd.io/etcd/server/v3/etcdserver/api/membership"
	mvcctxn "go.etcd.io/etcd/server/v3/etcdserver/txn"
	"go.etcd.io/etcd/server/v3/features"
	"go.etcd.io/etcd/server/v3/lease"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
	"go.etcd.io/etcd/server/v3/storage/mvcc"
	"go.etcd.io/etcd/server/v3/storage/schema"
)

type panicLessor struct {
	lease.FakeLessor
}

func (p *panicLessor) Lookup(id lease.LeaseID) *lease.Lease {
	panic("Lessor.Lookup called unexpectedly")
}

func (p *panicLessor) Attach(id lease.LeaseID, items []lease.LeaseItem) error {
	panic("Lessor.Attach called unexpectedly")
}

func (p *panicLessor) Detach(id lease.LeaseID, items []lease.LeaseItem) error {
	panic("Lessor.Detach called unexpectedly")
}

type countingFeatureGate struct {
	featuregate.FeatureGate
	enabledCalls atomic.Int64
}

func (c *countingFeatureGate) Enabled(key featuregate.Feature) bool {
	c.enabledCalls.Add(1)
	return c.FeatureGate.Enabled(key)
}

func TestPR19809_ApplierV3Backend_ContextAndOps(t *testing.T) {
	lg := zaptest.NewLogger(t)
	be, _ := betesting.NewDefaultTmpBackend(t)
	t.Cleanup(func() {
		betesting.Close(t, be)
	})

	cluster := membership.NewCluster(lg)
	cluster.SetBackend(schema.NewMembershipBackend(lg, be))
	cluster.AddMember(&membership.Member{ID: memberID}, true)
	lessor := lease.NewLessor(lg, be, cluster, lease.LessorConfig{})
	kv := mvcc.NewStore(lg, be, lessor, mvcc.StoreConfig{})
	t.Cleanup(func() {
		kv.Close()
		lessor.Stop()
	})

	applier := &applierV3backend{
		options: ApplierOptions{
			Logger:                       lg,
			Lessor:                       lessor,
			KV:                           kv,
			TxnModeWriteWithSharedBuffer: true,
		},
	}

	tctx := applier.context()
	require.Equal(t, lg, tctx.Logger)
	require.Equal(t, lessor, tctx.Lessor)
	require.Equal(t, kv, tctx.KV)
	require.True(t, tctx.TxnModeWriteWithSharedBuffer)

	putResp, _, err := applier.Put(&pb.PutRequest{Key: []byte("k1"), Value: []byte("v1")})
	require.NoError(t, err)
	require.Equal(t, int64(2), putResp.Header.Revision)

	rangeResp, _, err := applier.Range(&pb.RangeRequest{Key: []byte("k1")})
	require.NoError(t, err)
	require.Len(t, rangeResp.Kvs, 1)
	require.Equal(t, []byte("v1"), rangeResp.Kvs[0].Value)

	txnResp, _, err := applier.Txn(&pb.TxnRequest{
		Compare: []*pb.Compare{
			{
				Key:         []byte("k1"),
				Target:      pb.Compare_VALUE,
				Result:      pb.Compare_EQUAL,
				TargetUnion: &pb.Compare_Value{Value: []byte("v1")},
			},
		},
		Success: []*pb.RequestOp{
			{
				Request: &pb.RequestOp_RequestPut{
					RequestPut: &pb.PutRequest{Key: []byte("k2"), Value: []byte("v2")},
				},
			},
		},
	}, false)
	require.NoError(t, err)
	require.True(t, txnResp.Succeeded)

	delResp, _, err := applier.DeleteRange(&pb.DeleteRangeRequest{Key: []byte("k1")})
	require.NoError(t, err)
	require.Equal(t, int64(1), delResp.Deleted)
}

func TestPR19809_RangeAndDeleteRangeIgnoreUnusedTxnContextFields(t *testing.T) {
	lg := zaptest.NewLogger(t)
	be, _ := betesting.NewDefaultTmpBackend(t)
	t.Cleanup(func() {
		betesting.Close(t, be)
	})

	kv := mvcc.NewStore(lg, be, &lease.FakeLessor{}, mvcc.StoreConfig{})
	t.Cleanup(func() {
		kv.Close()
	})

	_, _, err := mvcctxn.Put(context.Background(), mvcctxn.TxnContext{
		Logger:                       lg,
		Lessor:                       &lease.FakeLessor{},
		KV:                           kv,
		TxnModeWriteWithSharedBuffer: false,
	}, &pb.PutRequest{Key: []byte("foo"), Value: []byte("bar")})
	require.NoError(t, err)

	// Range only reads Logger and KV; passing a Lessor that panics on any method call
	// and toggling TxnModeWriteWithSharedBuffer has zero effect on Range.
	for _, sharedBuf := range []bool{false, true} {
		resp, _, err := mvcctxn.Range(context.Background(), mvcctxn.TxnContext{
			Logger:                       lg,
			Lessor:                       &panicLessor{},
			KV:                           kv,
			TxnModeWriteWithSharedBuffer: sharedBuf,
		}, &pb.RangeRequest{Key: []byte("foo")}, true)
		require.NoError(t, err)
		require.Len(t, resp.Kvs, 1)
		require.Equal(t, []byte("bar"), resp.Kvs[0].Value)
	}

	// DeleteRange also only reads Logger and KV.
	delResp, _, err := mvcctxn.DeleteRange(context.Background(), mvcctxn.TxnContext{
		Logger:                       lg,
		Lessor:                       &panicLessor{},
		KV:                           kv,
		TxnModeWriteWithSharedBuffer: true,
	}, &pb.DeleteRangeRequest{Key: []byte("foo")})
	require.NoError(t, err)
	require.Equal(t, int64(1), delResp.Deleted)
}

func TestPR19809_EtcdServerRangeFeatureGateEvaluation(t *testing.T) {
	lg := zaptest.NewLogger(t)
	be, _ := betesting.NewDefaultTmpBackend(t)
	t.Cleanup(func() {
		betesting.Close(t, be)
	})

	kv := mvcc.NewStore(lg, be, &lease.FakeLessor{}, mvcc.StoreConfig{})
	t.Cleanup(func() {
		kv.Close()
	})

	fg := &countingFeatureGate{FeatureGate: features.NewDefaultServerFeatureGate("test", lg)}

	// Simulate the closure in (*EtcdServer).Range (v3_server.go:149-156):
	// Every Range call now queries ServerFeatureGate.Enabled(TxnModeWriteWithSharedBuffer)
	// even though txn.Range ignores TxnModeWriteWithSharedBuffer.
	for i := 0; i < 5; i++ {
		_, _, err := mvcctxn.Range(context.Background(), mvcctxn.TxnContext{
			Logger:                       lg,
			Lessor:                       &lease.FakeLessor{},
			KV:                           kv,
			TxnModeWriteWithSharedBuffer: fg.Enabled(features.TxnModeWriteWithSharedBuffer),
		}, &pb.RangeRequest{Key: []byte("foo")}, true)
		require.NoError(t, err)
	}
	require.Equal(t, int64(5), fg.enabledCalls.Load())
}
