// Reviewer tests for etcd-io/etcd#21202 (package etcdutl, PR head a9522b154).

package etcdutl

import (
	"bytes"
	"encoding/json"
	"io"
	"os"
	"path/filepath"
	"syscall"
	"testing"

	"github.com/spf13/cobra"
	"go.uber.org/zap"

	"go.etcd.io/etcd/server/v3/lease"
	"go.etcd.io/etcd/server/v3/storage/backend"
	"go.etcd.io/etcd/server/v3/storage/mvcc"
)

func reviewDB(t *testing.T) string {
	dbPath := filepath.Join(t.TempDir(), "r.db")
	b := backend.NewDefaultBackend(zap.NewNop(), dbPath)
	st := mvcc.NewStore(zap.NewNop(), b, &lease.FakeLessor{}, mvcc.StoreConfig{})
	st.Put([]byte("secret-key-name"), []byte("v"), lease.NoLease)
	st.Close()
	b.Close()
	return dbPath
}

func captureStdout(t *testing.T, f func()) string {
	r, w, _ := os.Pipe()
	old := os.Stdout
	os.Stdout = w
	f()
	w.Close()
	os.Stdout = old
	var buf bytes.Buffer
	io.Copy(&buf, r)
	return buf.String()
}

// R7: `etcdutl hashkv --detailed -w json` writes the per-key array and then the
// printer's object to stdout: two JSON documents, not one.
func TestReviewDetailedStdoutMixed(t *testing.T) {
	db := reviewDB(t)
	root := &cobra.Command{Use: "etcdutl"}
	root.PersistentFlags().StringP("write-out", "w", "simple", "")
	root.AddCommand(NewHashKVCommand())
	root.SetArgs([]string{"hashkv", db, "--detailed", "-w", "json"})
	out := captureStdout(t, func() {
		if err := root.Execute(); err != nil {
			t.Fatal(err)
		}
	})
	t.Logf("stdout:\n%s", out)
	var v any
	if err := json.Unmarshal([]byte(out), &v); err != nil {
		t.Errorf("stdout of --detailed -w json is not one JSON document: %v", err)
	}
	hashKVDetailed = false
}

// R8: --output is written with mode 0644 (key names readable by every user), over
// an existing file, and silently ignored without --detailed.
func TestReviewOutputFile(t *testing.T) {
	db := reviewDB(t)
	old := syscall.Umask(0o022)
	defer syscall.Umask(old)
	out := filepath.Join(t.TempDir(), "keys.json")
	if _, err := calculateHashKV(db, 0, 0, true, out); err != nil {
		t.Fatal(err)
	}
	fi, _ := os.Stat(out)
	data, _ := os.ReadFile(out)
	t.Logf("mode %v, contents %s", fi.Mode(), data)
	out2 := filepath.Join(t.TempDir(), "never.json")
	if _, err := calculateHashKV(db, 0, 0, false, out2); err != nil {
		t.Fatal(err)
	}
	if _, err := os.Stat(out2); err == nil {
		t.Logf("output written without --detailed")
	} else {
		t.Logf("--output without --detailed: no file written, no error (%v)", err)
	}
}
