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
	"fmt"
	"path/filepath"
	"strings"
	"testing"

	"go.uber.org/zap/zaptest"

	"go.etcd.io/etcd/client/pkg/v3/fileutil"
	"go.etcd.io/raft/v3/raftpb"
)

func snapAt(index uint64) *raftpb.Snapshot {
	return &raftpb.Snapshot{Metadata: &raftpb.SnapshotMetadata{Index: &index}}
}

func dbExists(dir string, index uint64) bool {
	return fileutil.Exist(filepath.Join(dir, fmt.Sprintf("%016x.snap.db", index)))
}

// TestReleaseSnapDBsUnappliedDBIsKept: a database file saved on receipt whose
// snapshot is never applied (raft drops the MsgSnap: an older term, or an index
// at or below the commit index) keeps its pending mark, so no later
// ReleaseSnapDBs removes it. Before the PR the next release removed it.
func TestReleaseSnapDBsUnappliedDBIsKept(t *testing.T) {
	dir := t.TempDir()
	ss := New(zaptest.NewLogger(t), dir)

	if _, err := ss.SaveDBFrom(strings.NewReader("A"), 100); err != nil {
		t.Fatal(err)
	}
	// raft ignores snapshot 100; later snapshots 200 and 300 are applied and
	// released.
	for _, idx := range []uint64{200, 300} {
		if err := ss.ReleaseSnapDBs(snapAt(idx)); err != nil {
			t.Fatal(err)
		}
	}
	if dbExists(dir, 100) {
		t.Errorf("snapshot db 100 was never applied and is still on disk after releases at 200 and 300")
	}
}

