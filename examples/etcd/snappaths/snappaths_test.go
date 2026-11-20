// Package snappaths checks the path equations the Lean proof's vocabulary assumes of etcd's
// configuration and snapshotter (wal-link, 2026-11-19, option B1;
// Proof/go_etcd_io/etcd/server/v3/config/Defs.lean, Proof/go_etcd_io/etcd/server/v3/etcdserver/api/snap/Defs.lean):
//
//   - config.backendPathOf dd = config.snapDirOf dd ++ "/db": cfg.BackendPath() is cfg.SnapDir() + "/db";
//   - snap.snapDBPathOf dd i = config.snapDirOf dd ++ "/" ++ snapDBName i: the snapshotter
//     bootstrap makes (snap.New(lg, cfg.SnapDir())) returns, from DBFilePath(i),
//     cfg.SnapDir() + "/" + fmt.Sprintf("%016x.snap.db", i).
//
// Both hold because filepath.Join cleans: cfg.SnapDir() is clean and ends in the element "snap"
// (so not in "/"), and "db" and the snapshot names are clean single elements. The test runs the real
// etcd code (the fork at the pin) on data directories that are relative, absolute, empty, ".",
// "..", with repeated and trailing slashes and with "." and ".." elements.
package snappaths

import (
	"fmt"
	"os"
	"path/filepath"
	"strings"
	"testing"

	"go.uber.org/zap"

	"go.etcd.io/etcd/server/v3/config"
	"go.etcd.io/etcd/server/v3/etcdserver/api/snap"
)

var dataDirs = []string{
	"", ".", "..", "default.etcd", "a", "a/", "a//b/", "./a/../b", "a/./b/.", "../d", "x/..",
}

func TestSnapPaths(t *testing.T) {
	base := t.TempDir()
	cwd := filepath.Join(base, "w", "v")
	if err := os.MkdirAll(cwd, 0o755); err != nil {
		t.Fatal(err)
	}
	t.Chdir(cwd)
	dirs := append([]string{}, dataDirs...)
	dirs = append(dirs, filepath.Join(base, "abs"), base+"//abs2/", "/")
	ids := []uint64{0, 1, 0xabc, 1<<64 - 1}
	for _, dd := range dirs {
		cfg := config.ServerConfig{DataDir: dd}
		sd := cfg.SnapDir()
		if sd != filepath.Clean(sd) || strings.HasSuffix(sd, "/") || !strings.HasSuffix(sd, "snap") {
			t.Errorf("DataDir %q: SnapDir %q not clean or not ending in snap", dd, sd)
		}
		if got, want := cfg.BackendPath(), sd+"/db"; got != want {
			t.Errorf("DataDir %q: BackendPath %q, want SnapDir+\"/db\" = %q", dd, got, want)
		}
		if dd == "/" {
			continue // no directory to create there; the string equations above still hold
		}
		if err := os.MkdirAll(sd, 0o755); err != nil {
			t.Fatal(err)
		}
		ss := snap.New(zap.NewNop(), sd)
		for _, id := range ids {
			name := fmt.Sprintf("%016x.snap.db", id)
			if strings.ContainsAny(name, "/\x00") || len(name) != 24 {
				t.Errorf("name %q", name)
			}
			if err := os.WriteFile(filepath.Join(sd, name), nil, 0o644); err != nil {
				t.Fatal(err)
			}
			got, err := ss.DBFilePath(id)
			if err != nil {
				t.Fatalf("DataDir %q id %x: %v", dd, id, err)
			}
			if want := sd + "/" + name; got != want {
				t.Errorf("DataDir %q id %x: DBFilePath %q, want SnapDir+\"/\"+name = %q", dd, id, got, want)
			}
		}
	}
}
