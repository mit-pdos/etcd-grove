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

package membership

import (
	"testing"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"

	"go.etcd.io/etcd/client/pkg/v3/types"
)

// TestIsLocalMemberLearner verifies all three branches of IsLocalMemberLearner:
//  1. local member present and IsLearner == true  -> returns true
//  2. local member present and IsLearner == false -> returns false
//  3. local member absent from c.members          -> logs at Debug and returns false (no panic)
func TestIsLocalMemberLearner(t *testing.T) {
	tests := []struct {
		name      string
		members   []*Member
		localID   types.ID
		isLearner bool
	}{
		{
			name:      "local member is a learner",
			members:   []*Member{newTestMemberAsLearner(1, nil, "node1", nil)},
			localID:   1,
			isLearner: true,
		},
		{
			name:      "local member is a voting member",
			members:   []*Member{newTestMember(1, nil, "node1", nil)},
			localID:   1,
			isLearner: false,
		},
		{
			name:      "local member removed from the cluster",
			members:   []*Member{newTestMember(2, nil, "node2", nil)},
			localID:   1,
			isLearner: false,
		},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			c := newTestCluster(t, tt.members)
			c.localID = tt.localID
			assert.Equal(t, tt.isLearner, c.IsLocalMemberLearner())
		})
	}
}

// TestUnaryInterceptorLearnerCheckRemovedMember reproduces the race in
// newUnaryInterceptor / newStreamInterceptor:
//
//	if s.IsMemberExist(s.MemberID()) && s.IsLearner() && !isRPCSupportedForLearner(req)
//
// where the apply loop removes the local member between IsMemberExist and IsLearner.
func TestUnaryInterceptorLearnerCheckRemovedMember(t *testing.T) {
	c := newTestCluster(t, []*Member{
		newTestMember(1, nil, "node1", nil),
		newTestMember(2, nil, "node2", nil),
	})
	c.SetID(types.ID(1), types.ID(100))
	require.True(t, c.IsMemberExist(types.ID(1)), "local member should exist initially")

	// Simulate the apply loop applying ConfChangeRemoveNode for the local member
	// between IsMemberExist(localID) and IsLocalMemberLearner().
	c.RemoveMember(types.ID(1), ApplyBoth)
	require.False(t, c.IsMemberExist(types.ID(1)), "local member should be removed")

	// Before PR #22188, this panicked with "failed to find local ID in cluster members".
	// With PR #22188, it logs at Debug and returns false.
	require.False(t, c.IsLocalMemberLearner())
}

// TestProbeRemovedLearnerReportedAsNonLearnerDuringShutdownWindow demonstrates that
// when a learner member (IsLearner == true) is removed via ConfChangeRemoveNode,
// during the 1-second stopWithDelay window (server.go:1225) before s.Stop() runs,
// IsLocalMemberLearner() transitions from true to false ("report it as a non-learner"),
// causing both learnerCheck (/readyz/non_learner) and the interceptor's
// IsMemberExist && IsLearner check to treat the unpromoted, removed learner as a non-learner.
func TestProbeRemovedLearnerReportedAsNonLearnerDuringShutdownWindow(t *testing.T) {
	c := newTestCluster(t, []*Member{
		newTestMemberAsLearner(1, nil, "learner1", nil),
		newTestMember(2, nil, "voter2", nil),
	})
	c.SetID(types.ID(1), types.ID(100))

	// Before removal: local member is a learner.
	require.True(t, c.IsMemberExist(types.ID(1)))
	require.True(t, c.IsLocalMemberLearner(), "active learner must report IsLearner == true")

	// ConfChangeRemoveNode(1) removes the learner from c.members while the server
	// continues running for 1s (go s.stopWithDelay(10*100*time.Millisecond, ...)).
	c.RemoveMember(types.ID(1), ApplyBoth)

	// After removal (during the 1s stopWithDelay window):
	// IsLocalMemberLearner() now returns false even though member 1 was a learner and
	// was never promoted to a voting member.
	require.False(t, c.IsMemberExist(types.ID(1)))
	require.False(t, c.IsLocalMemberLearner(), "removed learner is now reported as non-learner (false)")
}
