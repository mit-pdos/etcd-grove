package conform_test

import (
	"archive/tar"
	"bytes"
	"compress/gzip"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"runtime"
	"sort"
	"strings"
	"testing"
	"time"

	"github.com/mit-pdos/etcd-grove/examples/net/conform/overlay"
	"github.com/mit-pdos/etcd-grove/examples/net/conform/tracecheck"
)

// The seven examples whose process tests the collection traces.
var examples = []string{"echo", "framed", "acceptloop", "duplex", "halfclose", "preface", "shutdown"}

// The probe's modes (probe/main.go).
var probeModes = []string{"writeclose", "writeclosewrite", "resetwrite", "killwrite", "deadlinewrite",
	"emptywrite", "dialthenlisten", "dialtimeout"}

// TestOverlay checks that the tracer's renames, call patches and re-implemented bodies match
// the installed Go's net sources exactly (overlay.Make fails otherwise). It skips on a Go
// other than overlay.GoVersion, which the tracer refuses.
func TestOverlay(t *testing.T) {
	if runtime.Version() != overlay.GoVersion {
		t.Skipf("Go %s; the tracer is written for %s", runtime.Version(), overlay.GoVersion)
	}
	p, err := overlay.Make(t.TempDir())
	if err != nil {
		t.Fatal(err)
	}
	if _, err := os.Stat(p); err != nil {
		t.Fatal(err)
	}
}

// TestSample checks the committed sample traces (testdata/*.tar.gz, the checker's test inputs).
func TestSample(t *testing.T) {
	files, _ := filepath.Glob("testdata/*.tar.gz")
	if len(files) == 0 {
		t.Fatal("no sample traces in testdata")
	}
	st := tracecheck.NewStats()
	for _, f := range files {
		dirs, err := tracecheck.LoadTarGz(f)
		if err != nil {
			t.Fatal(err)
		}
		for _, d := range dirs {
			for _, e := range tracecheck.Check(d, st, tracecheck.Options{}) {
				t.Errorf("%s: %v", f, e)
			}
		}
	}
	t.Logf("sample:\n%s", st)
}

func runCmd(t *testing.T, dir string, env []string, timeout time.Duration, name string, args ...string) (string, error) {
	t.Helper()
	cmd := exec.Command(name, args...)
	cmd.Dir = dir
	cmd.Env = append(os.Environ(), env...)
	var out bytes.Buffer
	cmd.Stdout = &out
	cmd.Stderr = &out
	if err := cmd.Start(); err != nil {
		return "", err
	}
	done := make(chan error, 1)
	go func() { done <- cmd.Wait() }()
	select {
	case err := <-done:
		return out.String(), err
	case <-time.After(timeout):
		cmd.Process.Kill()
		<-done
		return out.String(), fmt.Errorf("timed out after %v", timeout)
	}
}

// runProbe runs the traced probe's mode with args into the trace directory dir, and writes
// its report next to it (dir.txt).
func runProbe(t *testing.T, probe, dir, mode string, args ...string) {
	t.Helper()
	if err := os.MkdirAll(dir, 0o755); err != nil {
		t.Fatal(err)
	}
	out, err := runCmd(t, ".", []string{"NETTCP_TRACE_DIR=" + dir, "NETTCP_NODE=probe"}, 5*time.Minute,
		probe, append([]string{"-mode", mode}, args...)...)
	os.WriteFile(dir+".txt", []byte(out), 0o644)
	if err != nil {
		t.Errorf("probe -mode %s: %v\n%s", mode, err, out)
		return
	}
	t.Logf("%s", out)
}

// TestCollect builds the examples' commands and the probe with the tracer, runs the
// examples' process tests (TestProcesses, TestServerCrashes) and every probe mode, and checks
// the traces (README.md, "Collecting traces"). Only with NETTCP_CONFORM=1. The traces go to
// $NETTCP_CONFORM_OUT (which must not exist or be empty), else a fresh temporary directory;
// NETTCP_CONFORM_SEMANTICS=1 also traces the measured semantics tests (examples/net/semantics),
// NETTCP_CONFORM_SAMPLE=1 also rewrites the committed sample (testdata/).
func TestCollect(t *testing.T) {
	if os.Getenv("NETTCP_CONFORM") != "1" {
		t.Skip("NETTCP_CONFORM=1 collects the conformance traces")
	}
	out := os.Getenv("NETTCP_CONFORM_OUT")
	if out == "" {
		var err error
		if out, err = os.MkdirTemp("", "nettcp-conform-"); err != nil {
			t.Fatal(err)
		}
	} else {
		if ents, err := os.ReadDir(out); err == nil && len(ents) > 0 {
			t.Fatalf("NETTCP_CONFORM_OUT=%s is not empty", out)
		}
		if err := os.MkdirAll(out, 0o755); err != nil {
			t.Fatal(err)
		}
	}
	out, _ = filepath.Abs(out)
	t.Logf("conformance traces: %s/traces", out)
	ov, err := overlay.Make(filepath.Join(out, "overlay"))
	if err != nil {
		t.Fatal(err)
	}
	traces := filepath.Join(out, "traces")
	modRoot, _ := filepath.Abs("../..")

	// The examples' process tests.
	var pkgs []string
	for _, ex := range examples {
		pkgs = append(pkgs, "./net/"+ex)
	}
	env := []string{"NETTCP_CONFORM=1", "NETTCP_TRACE_DIR=" + traces, "NETTCP_OVERLAY=" + ov}
	o, err := runCmd(t, modRoot, env, 20*time.Minute, "go",
		append([]string{"test", "-count=1", "-p=1", "-v", "-run", "^(TestProcesses|TestServerCrashes)$"}, pkgs...)...)
	os.WriteFile(filepath.Join(out, "examples.txt"), []byte(o), 0o644)
	if err != nil {
		t.Fatalf("the examples' process tests: %v\n%s", err, o)
	}

	// The probe.
	probe := filepath.Join(out, "bin", "probe")
	if o, err := runCmd(t, modRoot, nil, 5*time.Minute, "go", "build", "-overlay", ov, "-o", probe, "./net/conform/probe"); err != nil {
		t.Fatalf("go build the probe: %v\n%s", err, o)
	}
	for _, m := range probeModes {
		runProbe(t, probe, filepath.Join(traces, "probe", m), m)
	}

	// The semantics tests (their child processes are killed by the tests themselves, which
	// record no events: checked leniently).
	if os.Getenv("NETTCP_CONFORM_SEMANTICS") == "1" {
		dir := filepath.Join(traces, "semantics", "all")
		os.MkdirAll(dir, 0o755)
		o, err := runCmd(t, modRoot, []string{"NETTCP_TRACE_DIR=" + dir, "NETTCP_NODE=semantics"}, 20*time.Minute,
			"go", "test", "-overlay", ov, "-count=1", "./net/semantics")
		os.WriteFile(filepath.Join(out, "semantics.txt"), []byte(o), 0o644)
		if err != nil {
			t.Logf("the semantics tests failed (their traces are kept): %v\n%s", err, o)
		}
	}

	st := check(t, traces)
	os.WriteFile(filepath.Join(out, "summary.txt"), []byte(st.String()), 0o644)
	t.Logf("summary (%s/summary.txt):\n%s", out, st)

	if os.Getenv("NETTCP_CONFORM_SAMPLE") == "1" {
		writeSample(t, out, probe, traces)
	}
}

// check checks every trace directory under root.
func check(t *testing.T, root string) *tracecheck.Stats {
	t.Helper()
	dirs, err := tracecheck.Dirs(root)
	if err != nil {
		t.Fatal(err)
	}
	st := tracecheck.NewStats()
	nerr := 0
	for _, dn := range dirs {
		d, err := tracecheck.Load(dn)
		if err != nil {
			t.Error(err)
			continue
		}
		rel, _ := filepath.Rel(root, dn)
		opt := tracecheck.Options{Lenient: strings.HasPrefix(rel, "semantics")}
		for _, e := range tracecheck.Check(d, st, opt) {
			if nerr++; nerr <= 50 {
				t.Error(e)
			}
		}
	}
	if nerr > 50 {
		t.Errorf("... %d problems in all", nerr)
	}
	return st
}

// writeSample rewrites testdata/: some of the examples' runs, and the probe's modes run small
// (one iteration each), each directory a .tar.gz.
func writeSample(t *testing.T, out, probe, traces string) {
	t.Helper()
	old, _ := filepath.Glob("testdata/*.tar.gz")
	for _, f := range old {
		os.Remove(f)
	}
	os.MkdirAll("testdata", 0o755)
	for _, ex := range []string{"echo/TestProcesses", "echo/TestServerCrashes", "halfclose/TestServerCrashes",
		"shutdown/TestProcesses", "preface/TestProcesses", "duplex/TestServerCrashes"} {
		writeTarGz(t, filepath.Join("testdata", strings.ReplaceAll(ex, "/", "-")+".tar.gz"), filepath.Join(traces, ex), ex)
	}
	small := filepath.Join(out, "sample")
	args := map[string][]string{"dialtimeout": {"-dials", "300"}}
	for _, m := range probeModes {
		dir := filepath.Join(small, "probe", m)
		runProbe(t, probe, dir, m, append([]string{"-iters", "1"}, args[m]...)...)
		writeTarGz(t, filepath.Join("testdata", "probe-"+m+".tar.gz"), dir, "probe/"+m)
	}
	check(t, small)
	var total int64
	files, _ := filepath.Glob("testdata/*.tar.gz")
	for _, f := range files {
		if fi, err := os.Stat(f); err == nil {
			total += fi.Size()
		}
	}
	t.Logf("sample: %d files, %d bytes", len(files), total)
	if total > 2<<20 {
		t.Errorf("the sample is %d bytes, over 2 MiB", total)
	}
}

// writeTarGz writes the trace files of dir into file, under the directory name name.
func writeTarGz(t *testing.T, file, dir, name string) {
	t.Helper()
	ents, err := os.ReadDir(dir)
	if err != nil {
		t.Fatal(err)
	}
	var names []string
	for _, e := range ents {
		if strings.HasSuffix(e.Name(), ".jsonl") {
			names = append(names, e.Name())
		}
	}
	sort.Strings(names)
	var buf bytes.Buffer
	z, _ := gzip.NewWriterLevel(&buf, gzip.BestCompression)
	tw := tar.NewWriter(z)
	for _, n := range names {
		b, err := os.ReadFile(filepath.Join(dir, n))
		if err != nil {
			t.Fatal(err)
		}
		h := &tar.Header{Name: name + "/" + n, Mode: 0o644, Size: int64(len(b)), ModTime: time.Unix(0, 0), Format: tar.FormatPAX}
		if err := tw.WriteHeader(h); err != nil {
			t.Fatal(err)
		}
		tw.Write(b)
	}
	tw.Close()
	z.Close()
	if err := os.WriteFile(file, buf.Bytes(), 0o644); err != nil {
		t.Fatal(err)
	}
}
