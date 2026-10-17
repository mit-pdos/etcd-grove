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

package etcdserver

// TestProcessMessagesKeepsReadyOrder from etcd-io/etcd#22485 (commit 501702689), alone in a file
// so that it can be dropped into any checkout of server/etcdserver.

import (
	"testing"

	"github.com/stretchr/testify/require"
	"go.uber.org/zap/zaptest"

	"go.etcd.io/etcd/server/v3/mock/mockstorage"
	"go.etcd.io/raft/v3"
	"go.etcd.io/raft/v3/raftpb"
)

func TestProcessMessagesKeepsReadyOrder(t *testing.T) {
	r := newRaftNode(raftNodeConfig{
		lg:          zaptest.NewLogger(t),
		isIDRemoved: func(id uint64) bool { return id == 5 },
		Node:        newNopReadyNode(),
		storage:     mockstorage.NewStorageRecorder(""),
		raftStorage: raft.NewMemoryStorage(),
		transport:   newNopTransporter(),
	})

	const (
		lead  = uint64(1)
		peer2 = uint64(2)
		peer3 = uint64(3)
		peer5 = uint64(5)
	)
	app := func(to, index uint64) *raftpb.Message {
		return &raftpb.Message{
			Type:  raftpb.MsgApp.Enum(),
			From:  new(lead),
			To:    new(to),
			Term:  new(uint64(1)),
			Index: new(index),
		}
	}
	resp := func(index uint64) *raftpb.Message {
		return &raftpb.Message{
			Type:  raftpb.MsgAppResp.Enum(),
			From:  new(peer2),
			To:    new(lead),
			Term:  new(uint64(1)),
			Index: new(index),
		}
	}
	type msgFields struct {
		typ   raftpb.MessageType
		to    uint64
		index uint64
	}

	tests := []struct {
		name string
		ms   []*raftpb.Message
		// want holds indexes into ms of the messages expected in the output.
		want []int
	}{
		{
			name: "MsgApp",
			ms: []*raftpb.Message{
				app(peer2, 10),
				app(peer2, 11),
				app(peer2, 12),
				app(peer3, 10),
				app(peer5, 10),
			},
			want: []int{0, 1, 2, 3},
		},
		{
			name: "MsgAppResp",
			ms: []*raftpb.Message{
				resp(1),
				app(peer2, 10),
				resp(2),
				resp(3),
			},
			want: []int{1, 3},
		},
		{
			name: "mixed",
			ms: []*raftpb.Message{
				app(peer2, 10),
				app(peer2, 11),
				app(peer2, 12),
				resp(1),
				resp(2),
				app(peer5, 10),
			},
			want: []int{0, 1, 2, 4},
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			before := make([]msgFields, len(tt.ms))
			for i, m := range tt.ms {
				before[i] = msgFields{typ: m.GetType(), to: m.GetTo(), index: m.GetIndex()}
			}

			got := r.processMessages(tt.ms)

			require.Len(t, got, len(tt.want))
			for i, idx := range tt.want {
				require.Samef(t, tt.ms[idx], got[i], "got[%d] is not the Ready pointer", i)
			}

			require.Len(t, tt.ms, len(before))
			for i, m := range tt.ms {
				require.Equal(t, before[i].typ, m.GetType())
				require.Equal(t, before[i].to, m.GetTo())
				require.Equal(t, before[i].index, m.GetIndex())
			}
		})
	}
}
