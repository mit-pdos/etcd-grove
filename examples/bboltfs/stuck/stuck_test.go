package stuck

import (
	"fmt"
	"os"
	"os/exec"
	"strings"
	"testing"
)

// TestMain runs one probe and prints its answer when re-executed by
// TestSignals (BBOLTFS_PROBE set).
func TestMain(m *testing.M) {
	name := os.Getenv("BBOLTFS_PROBE")
	if name == "" {
		os.Exit(m.Run())
	}
	f, ok := killers[name]
	if !ok {
		os.Exit(3)
	}
	fmt.Println("RESULT", f(os.Getenv("BBOLTFS_DIR")))
	os.Exit(0)
}

// What Go/Linux answers for the probes that have a safe, fixed answer, to keep
// the comments in stuck.go honest. The racing probes have no fixed answer and
// are not run.
func TestGo(t *testing.T) {
	for name, c := range map[string]struct {
		f    func(string) bool
		want bool
	}{
		"testLoadPastEOFSamePage": {testLoadPastEOFSamePage, true},
		"testMmapWritable":        {testMmapWritable, true},
		"testMmapOffset":          {testMmapOffset, true},
		"testMmapZeroLength":      {testMmapZeroLength, true},
		"testMunmapResliced":      {testMunmapResliced, true},
		"testUseAfterClose":       {testUseAfterClose, true},
		"testFdatasyncAfterClose": {testFdatasyncAfterClose, true},
		"testNeverOpenedFd":       {testNeverOpenedFd, true},
		"testOutsidePath":         {testOutsidePath, true},
		"testAppend":              {testAppend, true},
		"testWriteReadOnly":       {testWriteReadOnly, true},
	} {
		t.Run(name, func(t *testing.T) {
			if got := c.f(t.TempDir()); got != c.want {
				t.Errorf("%s = %v in Go, want %v", name, got, c.want)
			}
		})
	}
}

// The probes that die of a signal: gc turns a fault on a non-nil address into
// "unexpected fault address ... fatal error: fault" with "[signal SIGSEGV" or
// "[signal SIGBUS", exit 2. Under -race the CAS faults inside the race
// runtime, and gc's report is a garbled "SIGSEGV: segmentation violation".
var killers = map[string]func(string) bool{
	"fatalStoreMapped":    fatalStoreMapped,
	"testLoadPastEOF":     testLoadPastEOF,
	"testLoadAfterMunmap": testLoadAfterMunmap,
	"testLoadAfterShrink": testLoadAfterShrink,
	"fatalCASMapped":      fatalCASMapped,
}

var killedBy = map[string]string{
	"fatalStoreMapped":    "SIGSEGV",
	"testLoadPastEOF":     "SIGBUS",
	"testLoadAfterMunmap": "SIGSEGV",
	"testLoadAfterShrink": "SIGBUS",
	"fatalCASMapped":      "SIGSEGV",
}

func TestSignals(t *testing.T) {
	for name := range killers {
		t.Run(name, func(t *testing.T) {
			cmd := exec.Command(os.Args[0], "-test.run=^$")
			cmd.Env = append(os.Environ(), "BBOLTFS_PROBE="+name, "BBOLTFS_DIR="+t.TempDir())
			out, err := cmd.CombinedOutput()
			if err == nil {
				t.Fatalf("%s did not die: %s", name, out)
			}
			sig := killedBy[name]
			if !strings.Contains(string(out), "unexpected fault address") ||
				!strings.Contains(string(out), sig) {
				t.Fatalf("%s: want a death by %s, got %v:\n%s", name, sig, err, out)
			}
		})
	}
}
