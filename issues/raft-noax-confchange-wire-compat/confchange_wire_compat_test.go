package raft_test

import (
	"testing"

	"go.etcd.io/raft/v3"
	pb "go.etcd.io/raft/v3/raftpb"
	"google.golang.org/protobuf/encoding/protowire"
	"google.golang.org/protobuf/proto"
)

// A newer application can attach metadata that an older entry formatter
// does not know. The change to the voting configuration is still the same.
func TestDescribeEntryWithNewConfChangeField(t *testing.T) {
	for _, tc := range []struct {
		name string
		kind pb.EntryType
		msg  proto.Message
	}{
		{"v1", pb.EntryConfChange, &pb.ConfChange{
			Type: pb.ConfChangeAddNode.Enum(), NodeId: proto.Uint64(42),
		}},
		{"v2", pb.EntryConfChangeV2, &pb.ConfChangeV2{
			Changes: []*pb.ConfChangeSingle{{Type: pb.ConfChangeAddNode.Enum(), NodeId: proto.Uint64(42)}},
		}},
	} {
		t.Run(tc.name, func(t *testing.T) {
			describe := func() string {
				t.Helper()
				wire, err := proto.Marshal(tc.msg)
				if err != nil {
					t.Fatal(err)
				}
				return raft.DescribeEntry(&pb.Entry{Type: tc.kind.Enum(), Data: wire}, nil)
			}
			want := describe()
			field := protowire.AppendTag(nil, 20, protowire.BytesType)
			tc.msg.ProtoReflect().SetUnknown(protowire.AppendString(field, "optional metadata"))
			if got := describe(); got != want {
				t.Errorf("DescribeEntry after adding optional metadata = %q, want %q", got, want)
			}
		})
	}
}
