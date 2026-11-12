package backend

import (
	"os"

	"go.etcd.io/etcd/server/v3/storage/schema"
)

// REQ backend/force-commit-durable: a write unlocked before ForceCommit returns survives a crash
// after it. A crash target: the program is also its own recovery, run again after any crash (also
// one during a recovery); no run panics. The marker file, created after ForceCommit returns,
// records that it did: a run that finds it only checks. The directory is synced after the
// backend's file is created, so that the file's name survives (bbolt does not sync it,
// nonissues/etcd-backend-name-lost-restart-panic.md).
// Users: storage/mvcc/kvstore.go:213-216 (the scheduled compaction committed before it runs),
// :289 (Commit, before the merged snapshot: etcdserver/snapshot_merge.go:36), lease/lessor.go:834,
// etcdserver/v3_server.go:412.
func ReqForceCommitDurable() {
	if _, err := os.Stat("specreq-backend-durable.marker"); err != nil { // ForceCommit has not returned
		be := open("specreq-backend-durable.db", nil)
		if d, err := os.Open("."); err != nil || d.Sync() != nil || d.Close() != nil {
			return
		}
		tx := be.BatchTx()
		tx.LockOutsideApply()
		tx.UnsafePut(schema.Meta, []byte("k"), []byte("v"))
		tx.Unlock()
		be.ForceCommit()
		f, err := os.Create("specreq-backend-durable.marker")
		be.Close()
		if err != nil || f.Close() != nil {
			return
		}
	}
	be := open("specreq-backend-durable.db", nil)
	if string(get(be.ReadTx(), schema.Meta, []byte("k"))) != "v" {
		panic("force-commit-durable: a crash lost a write committed by ForceCommit")
	}
	be.Close()
}
