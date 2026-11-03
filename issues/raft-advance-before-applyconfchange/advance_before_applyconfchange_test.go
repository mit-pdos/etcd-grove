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

package raft

import (
	"context"
	"testing"
	"time"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
	"google.golang.org/protobuf/proto"

	"go.etcd.io/raft/v3/raftpb"
)

// TestNodeAdvanceBeforeApplyConfChange runs three nodes whose applications
// handle each Ready as doc.go describes, except that node 1's application calls
// Advance before it has applied the Ready's committed entries, which
// Node.Advance allows. No index may be committed with two different entries.
func TestNodeAdvanceBeforeApplyConfChange(t *testing.T) {
	type member struct {
		ctx       context.Context
		n         *nodeTestHarness
		s         *MemoryStorage
		committed map[uint64]*raftpb.Entry
	}
	ms := map[uint64]*member{}
	for id := uint64(1); id <= 3; id++ {
		s := newTestMemoryStorage(withPeers(1, 2, 3))
		ctx, cancel, n := newNodeTestHarness(t.Context(), t, newTestConfig(id, 10, 1, s))
		defer cancel()
		ms[id] = &member{ctx: ctx, n: n, s: s, committed: map[uint64]*raftpb.Entry{}}
	}
	apply := func(m *member, e *raftpb.Entry) {
		if e.GetType() == raftpb.EntryConfChange {
			cc := &raftpb.ConfChange{}
			require.NoError(t, proto.Unmarshal(e.GetData(), cc))
			m.n.ApplyConfChange(cc)
		}
	}
	var applying []*raftpb.Entry // node 1's committed entries, not applied yet
	var cut uint64               // a node cut off from the others
	stabilize := func() {
		for busy := true; busy; {
			busy = false
			var msgs []*raftpb.Message
			for id := uint64(1); id <= 3; id++ {
				m := ms[id]
				select {
				case rd := <-m.n.Ready():
					busy = true
					if !IsEmptyHardState(rd.HardState) {
						require.NoError(t, m.s.SetHardState(rd.HardState))
					}
					require.NoError(t, m.s.Append(rd.Entries))
					msgs = append(msgs, rd.Messages...)
					for _, e := range rd.CommittedEntries {
						m.committed[e.GetIndex()] = e
						if id == 1 {
							applying = append(applying, e)
						} else {
							apply(m, e)
						}
					}
					m.n.Advance()
				case <-time.After(20 * time.Millisecond):
				}
			}
			for _, msg := range msgs {
				if msg.GetFrom() != cut && msg.GetTo() != cut {
					require.NoError(t, ms[msg.GetTo()].n.Step(ms[msg.GetTo()].ctx, msg))
				}
			}
		}
	}

	require.NoError(t, ms[1].n.Campaign(ms[1].ctx))
	stabilize()
	// Node 1 commits "remove 2" at index 2, then "remove 1" at index 3. Nodes 2
	// and 3 apply both: node 3 is the only voter in its configuration.
	for _, id := range []uint64{2, 1} {
		cc := &raftpb.ConfChange{Type: raftpb.ConfChangeRemoveNode.Enum(), NodeId: new(id)}
		require.NoError(t, ms[1].n.ProposeConfChange(ms[1].ctx, cc))
		stabilize()
	}
	require.Equal(t, raftpb.EntryConfChange, ms[3].committed[3].GetType())
	// With node 3 cut off, node 1 commits x at index 4.
	cut = 3
	require.NoError(t, ms[1].n.Propose(ms[1].ctx, []byte("x")))
	stabilize()
	// Node 3 becomes leader on its own and commits an entry at index 4.
	require.NoError(t, ms[3].n.Campaign(ms[3].ctx))
	stabilize()
	// Node 1's application finishes applying.
	for _, e := range applying {
		apply(ms[1], e)
	}

	require.Contains(t, ms[1].committed, uint64(4))
	require.Contains(t, ms[3].committed, uint64(4))
	assert.Equal(t, DescribeEntry(ms[1].committed[4], nil), DescribeEntry(ms[3].committed[4], nil),
		"index 4 committed on nodes 1 and 3")
}
