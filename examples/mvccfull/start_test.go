package mvccfull

import (
	"os"
	"strings"
	"testing"
)

// TestMainAt (rule 38's non-vacuity test for MainAt's checks): a directory that does not fit, or
// that already holds the database, makes MainAt return untouched; MainAt's run, for a Config in
// scope whose files are absent (here MainConfig's, which inScope admits), is FilePaths' check
// passing and Run creating the database (Run panics if a check fails). TestDrawConfig shows that
// drawn Configs pass inScope.
func TestMainAt(t *testing.T) {
	if !dirFits("/"+strings.Repeat("a", 255)) || dirFits("/"+strings.Repeat("a", 256)) ||
		dirFits("/"+strings.Repeat("a/", 1900)) {
		t.Fatal("dirFits disagrees with DirFits on a boundary case")
	}
	d := t.TempDir()
	cfg := MainConfig(d + "/mvccfull")
	if !inScope(cfg) {
		t.Fatal("MainConfig is not in scope")
	}
	for _, p := range FilePaths(cfg) {
		if !absent(p) {
			t.Fatalf("%s is there in a fresh directory", p)
		}
	}
	Run(cfg)
	if _, err := os.Stat(FilePaths(cfg)[0]); err != nil {
		t.Fatalf("Run in %q did not create its database: %v", d, err)
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
	for i := 0; i < 1000; i++ {
		MainAt(d3)
	}
	if fs, _ := os.ReadDir(d3); len(fs) != 1 {
		t.Fatal("MainAt ran in a directory already holding its database")
	}
}

// TestDrawConfig (non-vacuity of MainAt's draw): over many draws, inScope admits some, and each
// of its bounds both rejects and admits drawn values, so every part of the range is drawn.
func TestDrawConfig(t *testing.T) {
	const n = 2000000
	in := 0
	for i := 0; i < n; i++ {
		cfg := drawConfig("p")
		if len(cfg.Mix.Step) != 6 || len(cfg.Mix.Op) != 9 || len(cfg.Mix.Read) != 6 {
			t.Fatal("drawConfig's weights have the wrong lengths")
		}
		if inScope(cfg) {
			in++
			if cfg.Ops < 0 || cfg.Ops >= 1<<38 || cfg.Depth > 37 || cfg.MaxVal > 1<<20 ||
				hashing(cfg.Mix.Read) {
				t.Fatalf("inScope admitted %+v", cfg)
			}
		}
	}
	t.Logf("%d of %d drawn Configs in scope", in, n)
	if in == 0 {
		t.Fatal("no drawn Config is in scope")
	}
	big := Config{Ops: 1 << 38, Mix: Mix{Read: []int{1}}}
	if inScope(big) || !inScope(Config{Ops: 1<<38 - 1, Mix: Mix{Read: []int{1}}}) {
		t.Fatal("inScope's Ops bound is not 2^38")
	}
	if inScope(Config{Readers: 1<<27 - 1, Streams: 1, Mix: Mix{Read: []int{1}}}) ||
		!inScope(Config{Readers: 1<<27 - 2, Streams: 0, Mix: Mix{Read: []int{1}}}) {
		t.Fatal("inScope's reader-slot bound is not 2^28")
	}
	if inScope(Config{Mix: Mix{Read: []int{1 << 62, 1 << 62}}}) ||
		!inScope(Config{Mix: Mix{Read: []int{1<<62 - 1, 1 << 62}}}) {
		t.Fatal("weightsFit's bound is not 2^63")
	}
}
