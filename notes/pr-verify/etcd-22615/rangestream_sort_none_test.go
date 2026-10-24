package v3rpc

import (
	"testing"

	"github.com/stretchr/testify/require"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/status"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
)

func TestCheckRangeStreamRequestSortNone(t *testing.T) {
	// Key sort with NONE or ASCEND is mvcc's native order and is supported by RangeStream.
	for _, order := range []pb.RangeRequest_SortOrder{pb.RangeRequest_NONE, pb.RangeRequest_ASCEND} {
		err := checkRangeStreamRequest(&pb.RangeRequest{
			Key:        []byte("a"),
			RangeEnd:   []byte("z"),
			SortTarget: pb.RangeRequest_KEY,
			SortOrder:  order,
		})
		require.NoError(t, err)
	}

	// Non-key sort target with SortOrder == NONE requires full-range sorting (ascending by target),
	// which RangeStream does not perform; checkRangeStreamRequest must reject it with Unimplemented.
	for _, target := range []pb.RangeRequest_SortTarget{
		pb.RangeRequest_VERSION,
		pb.RangeRequest_CREATE,
		pb.RangeRequest_MOD,
		pb.RangeRequest_VALUE,
	} {
		err := checkRangeStreamRequest(&pb.RangeRequest{
			Key:        []byte("a"),
			RangeEnd:   []byte("z"),
			SortTarget: target,
			SortOrder:  pb.RangeRequest_NONE,
		})
		require.Error(t, err, "target=%v", target)
		st, ok := status.FromError(err)
		require.True(t, ok)
		require.Equal(t, codes.Unimplemented, st.Code(), "target=%v", target)
	}
}
