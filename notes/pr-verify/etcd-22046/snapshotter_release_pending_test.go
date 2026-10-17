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

package snap

import (
	"strings"
	"testing"

	"go.uber.org/zap/zaptest"

	"go.etcd.io/raft/v3/raftpb"
)

// TestReleaseSnapDBsDeletesDBPendingApply (etcd-io/etcd#18055): the database
// file of snapshot A is saved on receipt; before A is applied the raft loop
// persists a newer snapshot B and releases older database files, deleting A's.
// The apply loop's lookup of A's file (OpenSnapshotBackend -> DBFilePath) then
// fails, and applySnapshot panics with "failed to open snapshot backend".
// Fails at the pinned base; passes with etcd-io/etcd#22046.
func TestReleaseSnapDBsDeletesDBPendingApply(t *testing.T) {
	ss := New(zaptest.NewLogger(t), t.TempDir())
	if _, err := ss.SaveDBFrom(strings.NewReader("A"), 100); err != nil {
		t.Fatal(err)
	}
	b := uint64(200)
	if err := ss.ReleaseSnapDBs(&raftpb.Snapshot{Metadata: &raftpb.SnapshotMetadata{Index: &b}}); err != nil {
		t.Fatal(err)
	}
	if _, err := ss.DBFilePath(100); err != nil {
		t.Errorf("DBFilePath(100) after ReleaseSnapDBs(200): %v", err)
	}
}
