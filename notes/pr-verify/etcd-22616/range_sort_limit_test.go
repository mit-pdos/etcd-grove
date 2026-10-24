package txn

import (
	"testing"

	"github.com/stretchr/testify/require"
	"go.uber.org/zap/zaptest"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
)

// TestRangeSortLimit checks that a sorted range with a limit returns the first
// key-values of the same range without a limit.
func TestRangeSortLimit(t *testing.T) {
	s, _ := setup(t, testSetup{})
	s.Put([]byte("c"), []byte("1"), 0)
	s.Put([]byte("b"), []byte("2"), 0)
	s.Put([]byte("a"), []byte("3"), 0)

	tests := []struct {
		limit int64
		want  []string
	}{
		{limit: 0, want: []string{"c", "b", "a"}},
		{limit: 1, want: []string{"c"}},
		{limit: 2, want: []string{"c", "b"}},
	}
	for _, tt := range tests {
		resp, _, err := Range(t.Context(), zaptest.NewLogger(t), s, &pb.RangeRequest{
			Key:        []byte("a"),
			RangeEnd:   []byte("d"),
			Limit:      tt.limit,
			SortTarget: pb.RangeRequest_CREATE,
			SortOrder:  pb.RangeRequest_NONE,
		}, true)
		require.NoError(t, err)
		var keys []string
		for _, kv := range resp.Kvs {
			keys = append(keys, string(kv.Key))
		}
		require.Equalf(t, tt.want, keys, "limit %d", tt.limit)
	}
}
