package mvccfull

import (
	"os"
	"strings"
	"testing"
)

// TestMainAt (rule 38's non-vacuity test for MainAt's checks): a fresh temporary directory passes
// them and the run happens (its database file exists afterwards; Run panics if a check fails), while
// a directory that does not fit, or that already holds the database, makes MainAt return untouched.
func TestMainAt(t *testing.T) {
	if !dirFits("/"+strings.Repeat("a", 255)) || dirFits("/"+strings.Repeat("a", 256)) ||
		dirFits("/"+strings.Repeat("a/", 1900)) {
		t.Fatal("dirFits disagrees with DirFits on a boundary case")
	}
	d := t.TempDir()
	MainAt(d)
	if _, err := os.Stat(FilePaths(MainConfig(d + "/mvccfull"))[0]); err != nil {
		t.Fatalf("MainAt(%q) did not run: %v", d, err)
	}
	d2 := t.TempDir()
	MainAt(d2 + "/" + strings.Repeat("a", 300))
	if fs, _ := os.ReadDir(d2); len(fs) != 0 {
		t.Fatal("MainAt ran in a directory that does not fit")
	}
	d3 := t.TempDir()
	if err := os.WriteFile(FilePaths(MainConfig(d3 + "/mvccfull"))[0], []byte("x"), 0o644); err != nil {
		t.Fatal(err)
	}
	MainAt(d3)
	if fs, _ := os.ReadDir(d3); len(fs) != 1 {
		t.Fatal("MainAt ran in a directory already holding its database")
	}
}
