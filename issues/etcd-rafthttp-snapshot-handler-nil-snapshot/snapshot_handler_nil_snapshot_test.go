// Reproduction for issues/etcd-rafthttp-snapshot-handler-nil-snapshot.md (etcd-io/etcd#22440).
//
// Drop into go.etcd.io/etcd/server/v3/etcdserver/api/rafthttp (repository etcd-io/etcd, or the
// fork upamanyus/etcd at the pinned revision 107edf7e492a5cd7e8d958ed8a7ac9dbf1ecf81f), then run,
// from the module directory server/:
//
//	go test ./etcdserver/api/rafthttp/ -run TestSnapshotHandlerMsgSnapWithoutSnapshot -v
//
// Fails at the pin: snapshotHandler.ServeHTTP panics with a nil pointer dereference
// (http.go:272, m.Snapshot.Metadata). Passes once the handler answers 400 to a MsgSnap without a
// Snapshot (etcd-io/etcd#22441).
package rafthttp

import (
	"bytes"
	"net/http"
	"net/http/httptest"
	"testing"

	"go.uber.org/zap/zaptest"

	"go.etcd.io/etcd/api/v3/version"
	"go.etcd.io/etcd/client/pkg/v3/types"
	"go.etcd.io/etcd/server/v3/etcdserver/api/snap"
	"go.etcd.io/raft/v3/raftpb"
)

func TestSnapshotHandlerMsgSnapWithoutSnapshot(t *testing.T) {
	r := &fakeRaft{}
	tr := &Transport{ClusterID: types.ID(1), Raft: r}
	h := newSnapshotHandler(tr, r, snap.New(zaptest.NewLogger(t), t.TempDir()), types.ID(1))

	// A well-formed MsgSnap whose Snapshot field (9) is absent: it decodes with m.Snapshot == nil.
	m := &raftpb.Message{Type: raftpb.MsgSnap.Enum(), From: new(uint64(2)), To: new(uint64(1))}
	var body bytes.Buffer
	if err := (&messageEncoder{w: &body}).encode(m); err != nil {
		t.Fatal(err)
	}

	req, err := http.NewRequest(http.MethodPost, "/raft/snapshot", &body)
	if err != nil {
		t.Fatal(err)
	}
	req.Header.Set("X-Etcd-Cluster-ID", "1")
	req.Header.Set("X-Server-Version", version.Version)
	rw := httptest.NewRecorder()

	func() {
		defer func() {
			if p := recover(); p != nil {
				t.Fatalf("snapshotHandler panicked on a MsgSnap without a Snapshot: %v", p)
			}
		}()
		h.ServeHTTP(rw, req)
	}()
	if rw.Code != http.StatusBadRequest {
		t.Fatalf("status = %d, want %d", rw.Code, http.StatusBadRequest)
	}
}
