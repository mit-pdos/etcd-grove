package ordering_test

import (
	"context"
	"testing"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/client/v3/ordering"
)

// mockKV implements clientv3.KV and records every Do/Put/Delete invocation.
type mockKV struct {
	clientv3.KV
	doCalls     int
	putCalls    int
	deleteCalls int
	revs        []int64
}

func (m *mockKV) nextRev() int64 {
	idx := m.doCalls - 1
	if idx >= len(m.revs) {
		idx = len(m.revs) - 1
	}
	return m.revs[idx]
}

func (m *mockKV) Do(ctx context.Context, op clientv3.Op) (clientv3.OpResponse, error) {
	m.doCalls++
	rev := m.nextRev()
	if op.IsGet() {
		resp := &clientv3.GetResponse{
			Header: &pb.ResponseHeader{Revision: rev},
		}
		return resp.OpResponse(), nil
	}
	if op.IsTxn() {
		resp := &clientv3.TxnResponse{
			Header:    &pb.ResponseHeader{Revision: rev},
			Succeeded: true,
		}
		return resp.OpResponse(), nil
	}
	if op.IsPut() {
		resp := &clientv3.PutResponse{
			Header: &pb.ResponseHeader{Revision: rev},
		}
		return resp.OpResponse(), nil
	}
	resp := &clientv3.DeleteResponse{
		Header: &pb.ResponseHeader{Revision: rev},
	}
	return resp.OpResponse(), nil
}

func (m *mockKV) Put(ctx context.Context, key, val string, opts ...clientv3.OpOption) (*clientv3.PutResponse, error) {
	m.putCalls++
	return &clientv3.PutResponse{
		Header: &pb.ResponseHeader{Revision: 100},
	}, nil
}

func (m *mockKV) Delete(ctx context.Context, key string, opts ...clientv3.OpOption) (*clientv3.DeleteResponse, error) {
	m.deleteCalls++
	return &clientv3.DeleteResponse{
		Header: &pb.ResponseHeader{Revision: 100},
	}, nil
}

func (m *mockKV) Txn(ctx context.Context) clientv3.Txn {
	return &nopTxn{}
}

type nopTxn struct{}

func (n *nopTxn) If(cs ...clientv3.Cmp) clientv3.Txn  { return n }
func (n *nopTxn) Then(ops ...clientv3.Op) clientv3.Txn { return n }
func (n *nopTxn) Else(ops ...clientv3.Op) clientv3.Txn { return n }
func (n *nopTxn) Commit() (*clientv3.TxnResponse, error) {
	return nil, nil
}

// TestPR22122_MutableTxnExecutedAtMostOnce verifies that PR #22122 prevents
// txnOrdering.Commit() from re-executing mutable transactions when
// txnResp.Header.Revision < prevRev and orderViolationFunc returns nil.
func TestPR22122_MutableTxnExecutedAtMostOnce(t *testing.T) {
	ctx := context.Background()
	m := &mockKV{
		// 1st Do (Get): rev 10 (sets prevRev = 10)
		// 2nd Do (Mutable Txn): rev 5 (< prevRev=10, triggers orderViolationFunc)
		// 3rd Do (if retried): rev 12
		revs: []int64{10, 5, 12},
	}
	violations := 0
	kv := ordering.NewKV(m, func(op clientv3.Op, resp clientv3.OpResponse, prevRev int64) error {
		violations++
		return nil
	})

	// Establish prevRev = 10 via Get.
	getResp, err := kv.Get(ctx, "k")
	if err != nil || getResp.Header.Revision != 10 {
		t.Fatalf("unexpected Get result: resp=%v, err=%v", getResp, err)
	}

	// Execute a mutable Txn (contains OpPut in Then).
	m.doCalls = 0
	m.revs = []int64{5, 12}
	txnResp, err := kv.Txn(ctx).
		If(clientv3.Compare(clientv3.Version("k"), "=", 1)).
		Then(clientv3.OpPut("k", "v")).
		Commit()
	if err != nil {
		t.Fatalf("unexpected Commit error: %v", err)
	}
	if m.doCalls != 1 {
		t.Fatalf("expected mutable Txn to execute Do at most once, got %d calls", m.doCalls)
	}
	if violations != 1 {
		t.Fatalf("expected 1 order violation callback, got %d", violations)
	}
	t.Logf("PASS [PR #22122]: mutable Txn executed Do exactly %d time (returned rev=%d < prevRev=10 without resubmitting)",
		m.doCalls, txnResp.Header.Revision)
}

// TestPR22122_ReadOnlyNestedTxnRetriesUntilMonotonic verifies that a read-only
// transaction (including nested read-only OpTxn) retries on ordering violations
// until txnResp.Header.Revision >= prevRev.
func TestPR22122_ReadOnlyNestedTxnRetriesUntilMonotonic(t *testing.T) {
	ctx := context.Background()
	m := &mockKV{
		revs: []int64{10},
	}
	violations := 0
	kv := ordering.NewKV(m, func(op clientv3.Op, resp clientv3.OpResponse, prevRev int64) error {
		violations++
		return nil
	})

	_, err := kv.Get(ctx, "k")
	if err != nil {
		t.Fatalf("unexpected Get error: %v", err)
	}

	// Nested read-only Txn: first two attempts return rev 4 and 8 (< 10), third returns rev 15 (>= 10).
	m.doCalls = 0
	m.revs = []int64{4, 8, 15}
	nestedRO := clientv3.OpTxn(nil, []clientv3.Op{clientv3.OpGet("k2")}, nil)
	txnResp, err := kv.Txn(ctx).
		Then(clientv3.OpGet("k1"), nestedRO).
		Commit()
	if err != nil {
		t.Fatalf("unexpected Commit error: %v", err)
	}
	if m.doCalls != 3 {
		t.Fatalf("expected read-only Txn to retry 3 times, got %d", m.doCalls)
	}
	if txnResp.Header.Revision != 15 {
		t.Fatalf("expected final revision 15 >= 10, got %d", txnResp.Header.Revision)
	}
	t.Logf("PASS [PR #22122]: nested read-only Txn retried %d times until rev=%d >= prevRev=10",
		m.doCalls, txnResp.Header.Revision)
}

// TestCaveat1_MutableTxnViolationDiscardsCommittedRespWhenClosureErrors demonstrates
// that when orderViolationFunc returns an error (as recommended in doc.go:36 or after
// NewOrderViolationSwitchEndpointClosure exceeds 5*len(Endpoints)), txnOrdering.Commit()
// has ALREADY executed the mutable transaction on the server, and then discards txnResp
// and returns (nil, err).
func TestCaveat1_MutableTxnViolationDiscardsCommittedRespWhenClosureErrors(t *testing.T) {
	ctx := context.Background()
	m := &mockKV{
		revs: []int64{10},
	}
	kv := ordering.NewKV(m, func(op clientv3.Op, resp clientv3.OpResponse, prevRev int64) error {
		return ordering.ErrNoGreaterRev
	})

	_, _ = kv.Get(ctx, "k") // sets prevRev = 10

	m.doCalls = 0
	m.revs = []int64{7} // server executes and commits the Put at rev 7 (< 10)
	txnResp, err := kv.Txn(ctx).
		Then(clientv3.OpPut("k", "v")).
		Commit()
	if m.doCalls != 1 {
		t.Fatalf("expected 1 Do call, got %d", m.doCalls)
	}
	if err != ordering.ErrNoGreaterRev || txnResp != nil {
		t.Fatalf("expected (nil, ErrNoGreaterRev), got (%v, %v)", txnResp, err)
	}
	t.Logf("CAVEAT 1 CONFIRMED: mutable Txn was already committed on server (doCalls=%d), but Commit() discarded txnResp and returned (%v, %v)",
		m.doCalls, txnResp, err)
}

// TestCaveat2_PutDeleteAndDoBypassKvOrdering demonstrates that kvOrdering does not
// override Put, Delete, or Do:
// 1. Calling kv.Put at rev 100 does not update prevRev, so a subsequent kv.Get at
//    stale rev 50 succeeds without triggering orderViolationFunc!
// 2. Calling kv.Do(ctx, OpGet) at stale rev 5 bypassed kvOrdering completely.
func TestCaveat2_PutDeleteAndDoBypassKvOrdering(t *testing.T) {
	ctx := context.Background()
	m := &mockKV{
		revs: []int64{50},
	}
	violations := 0
	kv := ordering.NewKV(m, func(op clientv3.Op, resp clientv3.OpResponse, prevRev int64) error {
		violations++
		return ordering.ErrNoGreaterRev
	})

	// 1. kv.Put returns Header.Revision = 100, but kvOrdering does not override Put!
	putResp, err := kv.Put(ctx, "k", "v")
	if err != nil || putResp.Header.Revision != 100 {
		t.Fatalf("unexpected Put result: %v, %v", putResp, err)
	}

	// 2. Subsequent kv.Get returns Header.Revision = 50 (< 100), but prevRev is still 0!
	getResp, err := kv.Get(ctx, "k")
	if err != nil {
		t.Fatalf("unexpected Get error: %v", err)
	}
	if violations != 0 {
		t.Fatalf("expected 0 violations because Put did not update prevRev, got %d", violations)
	}

	// 3. Now prevRev is 50; calling kv.Do(ctx, OpGet) at rev 5 bypasses kvOrdering completely!
	m.doCalls = 0
	m.revs = []int64{5}
	doResp, err := kv.Do(ctx, clientv3.OpGet("k"))
	if err != nil || doResp.Get().Header.Revision != 5 || violations != 0 {
		t.Fatalf("unexpected Do result: rev=%d, err=%v, violations=%d",
			doResp.Get().Header.Revision, err, violations)
	}
	t.Logf("CAVEAT 2 CONFIRMED: kv.Put(rev=%d) left prevRev=0 so kv.Get(rev=%d) saw 0 violations; kv.Do(rev=%d < prevRev=50) bypassed kvOrdering with 0 violations",
		putResp.Header.Revision, getResp.Header.Revision, doResp.Get().Header.Revision)
}
