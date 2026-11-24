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

package integration

import (
	"context"
	"io"
	"os"
	"path/filepath"
	"testing"
	"time"

	"github.com/stretchr/testify/require"
	gofail "go.etcd.io/gofail/runtime"
	"go.uber.org/zap/zaptest"

	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/server/v3/storage/backend"
	"go.etcd.io/etcd/server/v3/storage/schema"
	"go.etcd.io/etcd/server/v3/storage/wal"
	"go.etcd.io/etcd/server/v3/storage/wal/walpb"
	"go.etcd.io/etcd/tests/v3/framework/integration"
)

// TestBackendAheadOfWALAfterKill shows that a follower that receives log
// entries together with their commit index applies them to its backend before
// its raft loop saves them to the WAL: a copy of its data directory taken while
// the raft loop is held before Save (what a kill -9 at that moment leaves) has
// a backend consistent index above the WAL's last entry. It then restarts the
// follower from that copy and checks what clients see.
//
// Needs `gofail enable server/etcdserver/` (raftBeforeSave).
func TestBackendAheadOfWALAfterKill(t *testing.T) {
	integration.BeforeTest(t)
	if len(gofail.List()) == 0 {
		t.Skip("run 'gofail enable server/etcdserver/' first")
	}
	// Leader heartbeats stop while its raft loop sleeps in the failpoint: keep
	// the election timeout above the sleep.
	oldTicks := integration.ElectionTicks
	integration.ElectionTicks = 500 // 5s
	defer func() { integration.ElectionTicks = oldTicks }()

	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 3})
	defer clus.Terminate(t)
	ctx := context.Background()

	lead := clus.WaitLeader(t)
	f := (lead + 1) % 3
	b := (lead + 2) % 3
	A, B, F := clus.Members[lead], clus.Members[b], clus.Members[f]
	cli := clus.Client(lead)

	_, err := cli.Put(ctx, "warmup", "v")
	require.NoError(t, err)
	waitApplied(t, F, A.Server.AppliedIndex())

	// F misses the next writes: they are committed by A and B.
	F.InjectPartition(t, A, B)
	var resp *clientv3.PutResponse
	for k := 0; k < 5; k++ {
		resp, err = cli.Put(ctx, "x", "after-partition")
		require.NoError(t, err)
	}
	i := A.Server.AppliedIndex()
	waitApplied(t, B, i)
	t.Logf("committed and applied by A and B up to index %d (revision %d); F applied %d",
		i, resp.Header.Revision, F.Server.AppliedIndex())

	// Hold every raft loop before Save, then let F catch up: F's raft loop
	// gets the missing entries and their commit index in one Ready.
	require.NoError(t, gofail.Enable("raftBeforeSave", `sleep(1500)`))
	failpointOn := true
	defer func() {
		if failpointOn {
			gofail.Disable("raftBeforeSave")
		}
	}()
	F.RecoverPartition(t, A, B)
	waitApplied(t, F, i)
	time.Sleep(300 * time.Millisecond) // > the backend batch interval (100ms)

	image := filepath.Join(t.TempDir(), "image")
	copyDir(t, F.DataDir, image)
	// "Kill" F here: cut it off before its raft loop leaves the failpoint, so
	// that no acknowledgement of the entries it has not saved reaches A.
	F.InjectPartition(t, A, B)
	require.NoError(t, gofail.Disable("raftBeforeSave"))
	failpointOn = false

	ci, walLast, walCommit := readImage(t, image)
	t.Logf("kill -9 image of F: backend consistent index %d, WAL last index %d, WAL HardState commit %d",
		ci, walLast, walCommit)
	require.GreaterOrEqual(t, ci, i)
	require.Less(t, walLast, ci, "backend ahead of the WAL's last entry")

	// Restart F from the image (A and B still hold the entries).
	F.Stop(t)
	require.NoError(t, os.RemoveAll(F.DataDir))
	copyDir(t, image, F.DataDir)
	require.NoError(t, F.Restart(t))
	F.RecoverPartition(t, A, B)
	select {
	case <-F.ReadyNotify():
	case <-time.After(30 * time.Second):
		t.Fatal("F not ready after restart")
	}
	fcli, err := integration.NewClientV3(F)
	require.NoError(t, err)
	defer fcli.Close()
	g, err := fcli.Get(ctx, "x", clientv3.WithSerializable())
	require.NoError(t, err)
	require.Len(t, g.Kvs, 1)
	require.GreaterOrEqual(t, g.Header.Revision, resp.Header.Revision)
	t.Logf("F restarted from the image, ready, serves revision %d (applied %d)",
		g.Header.Revision, F.Server.AppliedIndex())
}

func waitApplied(t *testing.T, m *integration.Member, idx uint64) {
	deadline := time.Now().Add(120 * time.Second)
	for m.Server.AppliedIndex() < idx {
		if time.Now().After(deadline) {
			t.Fatalf("member %s applied %d < %d", m.Name, m.Server.AppliedIndex(), idx)
		}
		time.Sleep(5 * time.Millisecond)
	}
}

func readImage(t *testing.T, dataDir string) (ci, walLast, walCommit uint64) {
	lg := zaptest.NewLogger(t)
	be := backend.NewDefaultBackend(lg, filepath.Join(dataDir, "member", "snap", "db"))
	ci, _ = schema.ReadConsistentIndex(be.ReadTx())
	require.NoError(t, be.Close())
	w, err := wal.OpenForRead(lg, filepath.Join(dataDir, "member", "wal"), &walpb.Snapshot{})
	require.NoError(t, err)
	defer w.Close()
	_, st, ents, err := w.ReadAll()
	require.NoError(t, err)
	if len(ents) > 0 {
		walLast = ents[len(ents)-1].GetIndex()
	}
	return ci, walLast, st.GetCommit()
}

func copyDir(t *testing.T, src, dst string) {
	require.NoError(t, filepath.Walk(src, func(p string, info os.FileInfo, err error) error {
		if err != nil {
			return err
		}
		rel, _ := filepath.Rel(src, p)
		target := filepath.Join(dst, rel)
		if info.IsDir() {
			return os.MkdirAll(target, 0o700)
		}
		in, err := os.Open(p)
		if err != nil {
			return err
		}
		defer in.Close()
		out, err := os.Create(target)
		if err != nil {
			return err
		}
		defer out.Close()
		_, err = io.Copy(out, in)
		return err
	}))
}
