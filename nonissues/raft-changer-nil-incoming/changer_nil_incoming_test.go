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

package confchange

import (
	"testing"

	"github.com/stretchr/testify/require"

	pb "go.etcd.io/raft/v3/raftpb"
	"go.etcd.io/raft/v3/tracker"
)

// TestChangerNilIncomingVoters adds a voter through a Changer over a
// ProgressTracker literal whose incoming voter map is nil (not built by
// tracker.MakeProgressTracker, as raft's own trackers are). It panics with
// "assignment to entry in nil map".
func TestChangerNilIncomingVoters(t *testing.T) {
	c := Changer{
		Tracker:   tracker.ProgressTracker{Progress: tracker.ProgressMap{}, MaxInflight: 10},
		LastIndex: 1,
	}
	require.NotPanics(t, func() {
		_, _, err := c.Simple(&pb.ConfChangeSingle{Type: pb.ConfChangeAddNode.Enum(), NodeId: new(uint64(1))})
		require.NoError(t, err)
	})
}
