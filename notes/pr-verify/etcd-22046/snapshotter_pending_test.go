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
	"os"
	"path/filepath"
	"strings"
	"sync"
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

// TestReleaseSnapDBsReceivedAgainAfterApplyIsKept: ReleaseDBSnapshot's comment
// says that dropping the mark lets ReleaseSnapDBs clean up a file left behind
// "when the same snapshot db is received again". If the second copy arrives
// after the apply consumed the first, SaveDBFrom marks it again and nothing
// ever drops that mark.
func TestReleaseSnapDBsReceivedAgainAfterApplyIsKept(t *testing.T) {
	dir := t.TempDir()
	ss := New(zaptest.NewLogger(t), dir)

	if _, err := ss.SaveDBFrom(strings.NewReader("A"), 100); err != nil {
		t.Fatal(err)
	}
	// the apply path (storage.OpenSnapshotBackend): rename onto db, drop the mark
	fn, err := ss.DBFilePath(100)
	if err != nil {
		t.Fatal(err)
	}
	if err := os.Rename(fn, filepath.Join(dir, "db")); err != nil {
		t.Fatal(err)
	}
	ss.ReleaseDBSnapshot(100)

	// the same snapshot is received again (raft ignores it: index 100 is applied)
	if _, err := ss.SaveDBFrom(strings.NewReader("A"), 100); err != nil {
		t.Fatal(err)
	}
	if err := ss.ReleaseSnapDBs(snapAt(200)); err != nil {
		t.Fatal(err)
	}
	if dbExists(dir, 100) {
		t.Errorf("the re-received snapshot db 100 is still on disk after a release at 200")
	}
}

// TestSaveDBFromRacesReleaseSnapDBs: SaveDBFrom renames the file into place,
// syncs the directory, and only then marks it; ReleaseSnapDBs checks the mark
// and removes the file without holding the mark's lock. A release that lists
// the directory in between removes a file whose SaveDBFrom then succeeds and
// marks it. (In the server this needs a release at an index above the saved
// one while it is being received, and raft then ignores that snapshot; the
// mark is left behind.)
func TestSaveDBFromRacesReleaseSnapDBs(t *testing.T) {
	dir := t.TempDir()
	ss := New(zaptest.NewLogger(t), dir)

	lost := 0
	for i := 0; i < 2000 && lost == 0; i++ {
		idx := uint64(100 + i)
		var wg sync.WaitGroup
		stop := make(chan struct{})
		wg.Add(1)
		go func() {
			defer wg.Done()
			for {
				select {
				case <-stop:
					return
				default:
					ss.ReleaseSnapDBs(snapAt(1 << 40))
				}
			}
		}()
		_, err := ss.SaveDBFrom(strings.NewReader("A"), idx)
		close(stop)
		wg.Wait()
		if err != nil {
			t.Fatal(err)
		}
		if _, err := ss.DBFilePath(idx); err != nil {
			lost++
			t.Logf("SaveDBFrom(%d) returned nil, then DBFilePath(%d): %v (pending mark set: %v)",
				idx, idx, err, ss.isPendingDB(idx))
		}
	}
	if lost > 0 {
		t.Errorf("a concurrent ReleaseSnapDBs removed a file SaveDBFrom saved and marked")
	}
}
