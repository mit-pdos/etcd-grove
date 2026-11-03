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

	"go.etcd.io/etcd/client/pkg/v3/types"
)

// TestUnaryInterceptorLearnerCheckRemovedMember runs, in order, the calls the unary
// interceptor's learner check makes (s.IsMemberExist(s.MemberID()) && s.IsLearner(), each
// under its own lock) with the apply loop's removal of the local member in between: the
// learner check must not panic.
func TestUnaryInterceptorLearnerCheckRemovedMember(t *testing.T) {
	c := newTestCluster(t, []*Member{newTestMember(1, nil, "node1", nil), newTestMember(2, nil, "node2", nil)})
	c.SetID(types.ID(1), types.ID(100))
	if !c.IsMemberExist(types.ID(1)) {
		t.Fatal("local member should exist")
	}
	// the apply loop applies the local member's removal here
	c.RemoveMember(types.ID(1), true)
	defer func() {
		if r := recover(); r != nil {
			t.Fatalf("the learner check of a request panicked: %v", r)
		}
	}()
	c.IsLocalMemberLearner()
}
