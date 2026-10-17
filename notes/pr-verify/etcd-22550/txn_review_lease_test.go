package txn

import (
	"testing"

	"github.com/stretchr/testify/require"
	"go.uber.org/zap/zaptest"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
)

// TestReviewIgnoreLeaseKeysOnly: a put with ignore_lease keeps the key's lease; a keys-only
// range (fast path) then, and inside a txn after a put, returns it.
func TestReviewIgnoreLeaseKeysOnly(t *testing.T) {
	s, lessor := setup(t, testSetup{lease: 7})
	lg := zaptest.NewLogger(t)
	_, _, err := Put(t.Context(), lg, lessor, s, &pb.PutRequest{Key: []byte("a"), Value: []byte("v"), Lease: 7})
	require.NoError(t, err)
	_, _, err = Put(t.Context(), lg, lessor, s, &pb.PutRequest{Key: []byte("a"), Value: []byte("w"), IgnoreLease: true})
	require.NoError(t, err)
	resp, _, err := Range(t.Context(), lg, s, &pb.RangeRequest{Key: []byte("a"), KeysOnly: true}, true)
	require.NoError(t, err)
	require.Len(t, resp.Kvs, 1)
	require.Equal(t, int64(7), resp.Kvs[0].Lease)

	// a txn: put b with lease 7, then a keys-only range of [a, c) in the same txn
	tr := &pb.TxnRequest{Success: []*pb.RequestOp{
		{Request: &pb.RequestOp_RequestPut{RequestPut: &pb.PutRequest{Key: []byte("b"), Value: []byte("v"), Lease: 7}}},
		{Request: &pb.RequestOp_RequestRange{RequestRange: &pb.RangeRequest{Key: []byte("a"), RangeEnd: []byte("c"), KeysOnly: true}}},
	}}
	for _, shared := range []bool{false, true} {
		txr, _, err := Txn(t.Context(), lg, tr, shared, s, lessor, false)
		require.NoError(t, err)
		rr := txr.Responses[1].GetResponseRange()
		require.Len(t, rr.Kvs, 2)
		require.Equal(t, int64(7), rr.Kvs[0].Lease)
		require.Equal(t, int64(7), rr.Kvs[1].Lease)
	}
}
