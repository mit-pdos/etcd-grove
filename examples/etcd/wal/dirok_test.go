package wal

import (
	"os"
	"path/filepath"
	"strings"
	"testing"
)

// TestDirOk: dirOk accepts the directories the tester runs on (t.TempDir's, the crash driver's
// root/data/member and root/oracle) and paths at its bounds, and refuses the rest, so that Main's
// check passes on a valid configuration and returns on an invalid one.
func TestDirOk(t *testing.T) {
	root := t.TempDir()
	long := "/" + strings.Repeat("a", 255)
	// the longest path dirOk accepts: maxDir-1 bytes
	longest := strings.Repeat(long, 15) + "/" + strings.Repeat("b", maxDir-1-15*256-1)
	good := []string{
		"/a", "/data/member", "/oracle", "/a/.b", "/...", "/a..", "/.a/b.",
		root, root + "/data/member", root + "/oracle",
		long, long + long,
		longest,
	}
	for _, p := range good {
		if !dirOk(p) {
			t.Errorf("dirOk(%q) = false, want true", p)
		}
		if filepath.Clean(p) != p || !filepath.IsAbs(p) {
			t.Errorf("%q: not clean and absolute", p)
		}
	}
	bad := []string{
		"", "/", "a", "a/b", "//a", "/a/", "/a//b", "/.", "/..", "/a/.", "/a/..", "/./a", "/../a",
		"/" + strings.Repeat("a", 256), long + "/" + strings.Repeat("b", 256),
		longest + "b",
	}
	for _, p := range bad {
		if dirOk(p) {
			t.Errorf("dirOk(%q) = true, want false", p)
		}
	}
}

// TestMainCheck: Main on a directory dirOk refuses returns without touching the file system, and
// on the crash driver's directories runs Boot (which creates the WAL and the oracle file).
func TestMainCheck(t *testing.T) {
	root := t.TempDir()
	Main(root+"/", root+"/oracle")
	Main("relative", root)
	Main(root, root+"/./x")
	if m, _ := filepath.Glob(root + "/*"); len(m) != 0 {
		t.Errorf("Main created %v", m)
	}
	area, orDir := root+"/data/member", root+"/oracle"
	for _, d := range []string{area, orDir} {
		if err := os.MkdirAll(d, 0o755); err != nil {
			t.Fatal(err)
		}
	}
	Main(area, orDir)
	for _, f := range []string{area + "/wal", orDir + "/state"} {
		if _, err := os.Stat(f); err != nil {
			t.Errorf("Main did not run Boot: %v", err)
		}
	}
}
