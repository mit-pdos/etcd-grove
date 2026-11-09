package etcdserverboot

import (
	"go.uber.org/zap"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/server/v3/etcdserver/api/snap"
	serverstorage "go.etcd.io/etcd/server/v3/storage"
	"go.etcd.io/etcd/server/v3/storage/backend"
	"go.etcd.io/etcd/server/v3/storage/wal"
	"go.etcd.io/etcd/server/v3/storage/wal/walpb"
	"go.etcd.io/raft/v3/raftpb"
)

func u64(v uint64) *uint64 { return &v }

func entry(term, index uint64) *raftpb.Entry {
	t := raftpb.EntryNormal
	return &raftpb.Entry{Term: u64(term), Index: u64(index), Type: &t, Data: []byte("x")}
}

// REQ etcdserverboot/wal-save-order: the raft loop's writes through the Storage interface are what
// a restart reads back: a snapshot record saved, then entries after it and a hard state, the files
// below the snapshot released, the WAL closed; opened again at the snapshot, ReadAll returns the
// hard state and the entries after the snapshot.
// Users: the raft loop (raft.go: SaveSnap of a received snapshot before Save; Release after),
// the apply thread's snapshot (SaveSnap, Release), bootstrap's restart (wal.Open, ReadAll).
// Assumes: walDir is a fresh directory, snapDir an existing one; the disk does not fail (diskOk).
// Specs: NewStorage.spec, storage.SaveSnap.spec, storage.Save.spec, storage.Release.spec,
// storage.Close.spec; Wal.Recs.save, saveSnap, release, newest, entsAfter (the trusted model).
func ReqSaveOrder(lg *zap.Logger, walDir, snapDir string) {
	w, err := wal.Create(lg, walDir, []byte("meta"))
	if err != nil {
		panic("wal-save-order: create") // diskOk
	}
	st := serverstorage.NewStorage(lg, w, snap.New(lg, snapDir))
	cs := &raftpb.ConfState{Voters: []uint64{1}}
	sn := &raftpb.Snapshot{Metadata: &raftpb.SnapshotMetadata{Index: u64(2), Term: u64(1), ConfState: cs}}
	if err := st.Save(&raftpb.HardState{Term: u64(1), Vote: u64(1), Commit: u64(2)},
		[]*raftpb.Entry{entry(1, 1), entry(1, 2)}); err != nil {
		panic("wal-save-order: save")
	}
	if err := st.SaveSnap(sn); err != nil {
		panic("wal-save-order: save snapshot")
	}
	if err := st.Save(&raftpb.HardState{Term: u64(1), Vote: u64(1), Commit: u64(4)},
		[]*raftpb.Entry{entry(1, 3), entry(1, 4)}); err != nil {
		panic("wal-save-order: save")
	}
	if err := st.Release(sn); err != nil {
		panic("wal-save-order: release")
	}
	if err := st.Close(); err != nil {
		panic("wal-save-order: close")
	}

	w2, err := wal.Open(lg, walDir, &walpb.Snapshot{Index: u64(2), Term: u64(1)})
	if err != nil {
		panic("wal-save-order: open at the saved snapshot")
	}
	defer w2.Close()
	_, hs, ents, err := w2.ReadAll()
	if err != nil {
		panic("wal-save-order: read")
	}
	if hs.GetCommit() != 4 || len(ents) != 2 || ents[0].GetIndex() != 3 || ents[1].GetIndex() != 4 {
		panic("wal-save-order: the restart does not read what was saved")
	}
}

// REQ etcdserverboot/quota: the quota accepts the three request kinds its callers pass, at any
// size, and answers (a refusal on false is a Step refusal; no workload premise).
// Users: apply's capped applier (apply.newQuotaApplierV3), v3rpc's quota interceptors.
// Assumes: be is an open backend.
// Specs: NewBackendQuota.spec, BackendQuota.Available.spec, BackendQuota.Cost.spec.
func ReqQuota(lg *zap.Logger, be backend.Backend) {
	q := serverstorage.NewBackendQuota(lg, 0, be, "q")
	_ = q.Available(&pb.PutRequest{Key: []byte("k"), Value: make([]byte, 1<<20)})
	_ = q.Available(&pb.TxnRequest{})
	_ = q.Cost(&pb.LeaseGrantRequest{TTL: 5})
	_ = q.Remaining()
}
