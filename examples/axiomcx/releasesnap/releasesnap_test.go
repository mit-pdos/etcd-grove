// Package releasesnap is the Go counterexample to the trust-boundary axiom
// storage.storage.Release.wp_proof (found 2026-11-17 by etcd-grove-03's releasesnap attack;
// notes/release-snapdb-held-file.md). etcd's Snapshotter.ReleaseSnapDBs(snap) deletes every
// <hex>.snap.db below snap's index by listing the directory, including a file a caller already
// took out of snapDirInv's map (SnapRO.snapDir_take) and still holds as backend.fileHolds; the
// axiom's frame keeps that fileHolds, and snapDir_take with Rm = snapRmM hands exactly the
// □ (∀ j < i+1, Rm j) a Release at i+1 needs. The program below opens the held file after the
// release and panics in Go ("claim: the held snapshot file holds D"). Tests only, no Goose
// project; the attack's original, an internal test of package snap, is
// /shared/tmp/releasesnap-attack/etcd/server/etcdserver/api/snap/releaseattack_test.go.
package releasesnap

import (
	"bytes"
	"os"
	"path/filepath"
	"testing"

	bolt "go.etcd.io/bbolt"
	"go.etcd.io/etcd/server/v3/etcdserver/api/snap"
	"go.etcd.io/raft/v3/raftpb"
	"go.uber.org/zap/zaptest"
)

func snapAt(i uint64) *raftpb.Snapshot {
	return &raftpb.Snapshot{Metadata: &raftpb.SnapshotMetadata{Index: &i}}
}

func heldFile(t *testing.T) {
	dir := t.TempDir()
	ss := snap.New(zaptest.NewLogger(t), dir)
	// a bbolt image D with key k=v
	src := filepath.Join(t.TempDir(), "src.db")
	db, err := bolt.Open(src, 0o600, nil)
	if err != nil {
		t.Fatal(err)
	}
	if err := db.Update(func(tx *bolt.Tx) error {
		b, err := tx.CreateBucket([]byte("key"))
		if err != nil {
			return err
		}
		return b.Put([]byte("k"), []byte("v"))
	}); err != nil {
		t.Fatal(err)
	}
	db.Close()
	img, err := os.ReadFile(src)
	if err != nil {
		t.Fatal(err)
	}
	const k = 5
	if _, err := ss.SaveDBFrom(bytes.NewReader(img), k); err != nil {
		t.Fatal(err)
	}
	p, err := ss.DBFilePath(k) // proof: p = snapDBPath ss k, the client holds fileHolds p D
	if err != nil {
		t.Fatal(err)
	}
	if err := ss.ReleaseSnapDBs(snapAt(k + 1)); err != nil { // axiom: the frame keeps fileHolds p D
		t.Fatal(err)
	}
	db2, err := bolt.Open(p, 0o600, nil) // newBackend's open: its post says data D
	if err != nil {
		panic("claim: the held snapshot file holds D (open: " + err.Error() + ")")
	}
	defer db2.Close()
	db2.View(func(tx *bolt.Tx) error {
		b := tx.Bucket([]byte("key"))
		if b == nil || string(b.Get([]byte("k"))) != "v" {
			panic("claim: the held snapshot file holds D")
		}
		return nil
	})
}

func TestAttackHeldFile(t *testing.T) {
	defer func() {
		r := recover()
		t.Logf("heldFile: recovered %v", r)
		if r == nil {
			t.Errorf("heldFile: no panic")
		}
	}()
	heldFile(t)
}
