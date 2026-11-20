// Package releasesnapdbs: the Go evidence of the axiom review of the proposed
// snap.Snapshotter.ReleaseSnapDBs spec (wal-link L2, 2026-11-17;
// notes/axiom-review/releasesnapdbs.md). At the etcd pin (upamanyus/etcd 8c28a4296):
//
//   - TestAttackNames: which entries of the snapshotter's directory ReleaseSnapDBs(i)
//     removes: every entry whose name ends in ".snap.db" and whose prefix parses as a
//     base-16 uint64 below i (strconv.ParseUint(prefix, 16, 64)), canonical (16 lowercase
//     hex digits, snapDBPath) or not ("5.snap.db", 19 digits, an empty directory named
//     "3.snap.db"); it returns an error only when the directory cannot be opened or listed,
//     never for a failed removal (logged and skipped: a non-empty directory stays).
//   - TestAttackHeldFile: the refutation. A caller that took file k out of the directory's
//     invariant (SnapRO.snapDir_take, then OpenSnapshotBackend's fileHolds) and calls
//     ReleaseSnapDBs at k+1 loses the file: Go lists the directory, not the invariant.
//     Opening the path afterwards creates an empty database, not the image D the held
//     fileHolds claims.
//
// Run: cd examples && GOWORK=off go test -count=1 -v ./axiomcx/releasesnapdbs/
package releasesnapdbs

import (
	"bytes"
	"os"
	"path/filepath"
	"reflect"
	"sort"
	"testing"

	bolt "go.etcd.io/bbolt"
	"go.uber.org/zap/zaptest"

	"go.etcd.io/etcd/server/v3/etcdserver/api/snap"

	"go.etcd.io/raft/v3/raftpb"
)

func names(t *testing.T, dir string) []string {
	es, err := os.ReadDir(dir)
	if err != nil {
		t.Fatal(err)
	}
	var r []string
	for _, e := range es {
		r = append(r, e.Name())
	}
	sort.Strings(r)
	return r
}

func snapAt(i uint64) *raftpb.Snapshot {
	return &raftpb.Snapshot{Metadata: &raftpb.SnapshotMetadata{Index: &i}}
}

// Which names ReleaseSnapDBs(10) removes, and when it errs.
func TestAttackNames(t *testing.T) {
	dir := t.TempDir()
	ss := snap.New(zaptest.NewLogger(t), dir)
	removed := []string{
		"0000000000000005.snap.db",    // canonical, < i
		"5.snap.db",                   // short hex: parses 5
		"0000000000000000005.snap.db", // 19 digits: parses 5
		"9.snap.db",
		"3.snap.db", // an empty directory (created below)
	}
	kept := []string{
		"000000000000000a.snap.db",  // canonical, == i
		"000000000000000b.snap.db",  // canonical, > i
		"000000000000000A.snap.db",  // uppercase: parses 10, not below i
		"0000000000000005.SNAP.db",  // suffix is case-sensitive
		"0x5.snap.db",               // ParseUint with base 16 rejects the prefix
		"5_0.snap.db",               // underscores rejected with an explicit base
		"+5.snap.db",                // sign rejected
		".snap.db",                  // empty prefix
		"10000000000000000.snap.db", // 17 hex digits: out of range
		"4.snap.db",                 // a non-empty directory: Remove fails, logged, skipped
		"tmp12345", "0000000000000005-0000000000000001.snap", "db",
	}
	for _, f := range append(append([]string{}, removed...), kept...) {
		switch f {
		case "3.snap.db":
			if err := os.Mkdir(filepath.Join(dir, f), 0o700); err != nil {
				t.Fatal(err)
			}
		case "4.snap.db":
			if err := os.MkdirAll(filepath.Join(dir, f, "inner"), 0o700); err != nil {
				t.Fatal(err)
			}
		default:
			if err := os.WriteFile(filepath.Join(dir, f), []byte("x"), 0o600); err != nil {
				t.Fatal(err)
			}
		}
	}
	if err := ss.ReleaseSnapDBs(snapAt(10)); err != nil {
		t.Fatalf("ReleaseSnapDBs: %v (a failed removal is not an error)", err)
	}
	want := append([]string{}, kept...)
	sort.Strings(want)
	if got := names(t, dir); !reflect.DeepEqual(got, want) {
		t.Errorf("after ReleaseSnapDBs(10):\n got  %v\n want %v", got, want)
	}
	// nil metadata: GetIndex() is 0, nothing is below it
	if err := ss.ReleaseSnapDBs(&raftpb.Snapshot{}); err != nil {
		t.Fatal(err)
	}
	// the directory cannot be opened: the only error (with a failed listing)
	ss2 := snap.New(nil, filepath.Join(dir, "nope"))
	if err := ss2.ReleaseSnapDBs(snapAt(10)); err == nil {
		t.Errorf("missing directory: want an error")
	}
}

// The refutation: a held file below the release index is removed.
func TestAttackHeldFile(t *testing.T) {
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
	img, _ := os.ReadFile(src)
	const k = 5
	if _, err := ss.SaveDBFrom(bytes.NewReader(img), k); err != nil {
		t.Fatal(err)
	}
	p, err := ss.DBFilePath(k) // the proof: p = snapDBPath ss k, the caller holds fileHolds p D
	if err != nil {
		t.Fatal(err)
	}
	if err := ss.ReleaseSnapDBs(snapAt(k + 1)); err != nil { // the proposed spec frames fileHolds p D
		t.Fatal(err)
	}
	if _, err := os.Stat(p); !os.IsNotExist(err) {
		t.Fatalf("held file %s still there (err %v): the attack did not reproduce", p, err)
	}
	// newBackend's open of the held path: an empty database, not D
	db2, err := bolt.Open(p, 0o600, nil)
	if err != nil {
		t.Fatalf("open: %v", err)
	}
	defer db2.Close()
	db2.View(func(tx *bolt.Tx) error {
		if b := tx.Bucket([]byte("key")); b != nil {
			t.Errorf("the reopened file holds D: the attack did not reproduce")
		}
		return nil
	})
	t.Logf("held %s removed by ReleaseSnapDBs(%d): the spec's framed fileHolds is false", p, k+1)
}
