package txn

import (
	"fmt"
	"testing"

	"github.com/stretchr/testify/require"
	"go.uber.org/zap/zaptest"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
)

func TestRangeSortLimit(t *testing.T) {
	s, _ := setup(t, testSetup{})
	s.Put([]byte("c"), []byte("1"), 0)
	s.Put([]byte("b"), []byte("2"), 0)
	s.Put([]byte("a"), []byte("3"), 0)

	ctx := t.Context()
	lg := zaptest.NewLogger(t)

	for _, limit := range []int64{1, 2, 3} {
		t.Run(fmt.Sprintf("limit_%d", limit), func(t *testing.T) {
			resp, _, err := Range(ctx, lg, s, &pb.RangeRequest{
				Key:        []byte("a"),
				RangeEnd:   []byte("d"),
				SortTarget: pb.RangeRequest_CREATE,
				SortOrder:  pb.RangeRequest_NONE,
				Limit:      limit,
			}, false)
			require.NoError(t, err)

			var keys []string
			for _, kv := range resp.Kvs {
				keys = append(keys, string(kv.Key))
			}

			expected := []string{"c", "b", "a"}[:limit]
			require.Equal(t, expected, keys)
		})
	}
}
