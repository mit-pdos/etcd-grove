package bolttrunc

// TestTruncatedSnapshotDB: what a follower gets if it saves a bbolt snapshot stream cut
// short (as SaveDBFrom does under etcd PR #21569 when the sender's Tx.WriteTo stops with
// io.EOF): the first two pages (the meta pages WriteTo writes first) are intact, so
// bolt.Open succeeds; reading the data then touches pages past the end of the file.
// The read runs in a child process because a fault on an mmapped page past EOF (SIGBUS)
// kills the process. The child opens with etcd's backend options (10 GiB InitialMmapSize, map
// freelist).

import (
	"bytes"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"testing"

	bolt "go.etcd.io/bbolt"
)

func TestTruncatedSnapshotDB(t *testing.T) {
	if p := os.Getenv("BOLTTRUNC_OPEN"); p != "" {
		db, err := bolt.Open(p, 0o600, &bolt.Options{InitialMmapSize: 10 << 30, FreelistType: bolt.FreelistMapType}) // etcd backend defaults
		if err != nil {
			fmt.Println("OPEN-ERROR:", err)
			return
		}
		fmt.Println("OPEN-OK")
		n := 0
		err = db.View(func(tx *bolt.Tx) error {
			return tx.Bucket([]byte("key")).ForEach(func(k, v []byte) error { n++; _ = v[len(v)-1]; return nil })
		})
		fmt.Println("READ:", n, "keys, err:", err)
		return
	}
	dir := t.TempDir()
	db, err := bolt.Open(filepath.Join(dir, "src.db"), 0o600, nil)
	if err != nil {
		t.Fatal(err)
	}
	if err := db.Update(func(tx *bolt.Tx) error {
		b, err := tx.CreateBucket([]byte("key"))
		if err != nil {
			return err
		}
		for i := 0; i < 20000; i++ {
			if err := b.Put([]byte(fmt.Sprintf("k%08d", i)), bytes.Repeat([]byte{'v'}, 1000)); err != nil {
				return err
			}
		}
		return nil
	}); err != nil {
		t.Fatal(err)
	}
	var buf bytes.Buffer
	var size int64
	if err := db.View(func(tx *bolt.Tx) error { size = tx.Size(); _, err := tx.WriteTo(&buf); return err }); err != nil {
		t.Fatal(err)
	}
	db.Close()
	trunc := filepath.Join(dir, "trunc.snap.db")
	if err := os.WriteFile(trunc, buf.Bytes()[:size/4], 0o600); err != nil {
		t.Fatal(err)
	}
	cmd := exec.Command(os.Args[0], "-test.run=TestTruncatedSnapshotDB", "-test.v")
	cmd.Env = append(os.Environ(), "BOLTTRUNC_OPEN="+trunc)
	out, err := cmd.CombinedOutput()
	t.Logf("tx.Size()=%d, kept %d bytes; child exit: %v\n%s", size, size/4, err, firstLines(out, 60))
}

func firstLines(b []byte, n int) []byte {
	ls := bytes.SplitN(b, []byte("\n"), n+1)
	if len(ls) > n {
		ls = ls[:n]
	}
	return bytes.Join(ls, []byte("\n"))
}
