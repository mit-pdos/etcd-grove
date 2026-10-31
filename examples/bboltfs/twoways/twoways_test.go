package twoways

import (
	"fmt"
	"os"
	"os/exec"
	"strings"
	"testing"
	"time"
)

var probes = map[string]func(string) bool{
	"bootUnsyncedData":     bootUnsyncedData,
	"bootUnsyncedName":     bootUnsyncedName,
	"bootFailedThenSync":   bootFailedThenSync,
	"bootUnsyncedTruncate": bootUnsyncedTruncate,
}

// TestMain runs one boot and prints its answer when re-executed by
// TestPhases (BBOLTFS_BOOT set). A setup boot never returns.
func TestMain(m *testing.M) {
	name := os.Getenv("BBOLTFS_BOOT")
	if name == "" {
		os.Exit(m.Run())
	}
	f, ok := probes[name]
	if !ok {
		os.Exit(3)
	}
	fmt.Println("RESULT", f(os.Getenv("BBOLTFS_DIR")))
	os.Exit(0)
}

// Crashes cannot be tested in Go. This drives the phases with a stand-in: a
// boot that has not returned after a while is killed (SIGKILL) and the next
// boot started. A killed process loses nothing (the page cache survives), so
// every probe that reaches its observing boot answers true, the "nothing lost"
// answer, at the third boot. bootFailedThenSync never gets there, since its
// syncs do not fail.
func TestPhases(t *testing.T) {
	for name, want := range map[string]string{
		"bootUnsyncedData":     "RESULT true",
		"bootUnsyncedName":     "RESULT true",
		"bootFailedThenSync":   "",
		"bootUnsyncedTruncate": "RESULT true",
	} {
		t.Run(name, func(t *testing.T) {
			t.Parallel()
			dir := t.TempDir()
			got := ""
			boots := 0
			for boots < 4 && got == "" {
				boots++
				got = boot(t, name, dir)
			}
			if got != want {
				t.Fatalf("%s: got %q after %d boots, want %q", name, got, boots, want)
			}
			if want != "" && boots != 3 {
				t.Errorf("%s answered at boot %d, want 3", name, boots)
			}
		})
	}
}

// boot runs one boot of the probe in a child process, and returns its answer,
// or "" if it was still running (waiting for a crash) when killed.
func boot(t *testing.T, name, dir string) string {
	cmd := exec.Command(os.Args[0], "-test.run=^$")
	// GORACE: under -race, a process otherwise sleeps 1s before exiting
	cmd.Env = append(os.Environ(), "BBOLTFS_BOOT="+name, "BBOLTFS_DIR="+dir, "GORACE=atexit_sleep_ms=0")
	var out strings.Builder
	cmd.Stdout = &out
	if err := cmd.Start(); err != nil {
		t.Fatal(err)
	}
	done := make(chan error, 1)
	go func() { done <- cmd.Wait() }()
	select {
	case err := <-done:
		if err != nil {
			t.Fatalf("%s: boot failed: %v\n%s", name, err, out.String())
		}
		return strings.TrimSpace(out.String())
	case <-time.After(2 * time.Second):
		_ = cmd.Process.Kill()
		<-done
		return ""
	}
}

// The racing probes have no fixed answer on Linux. This only runs them, under
// -race too, to check that they terminate and race on no Go memory.
func TestRacingRuns(t *testing.T) {
	for i := 0; i < 20; i++ {
		_ = testReadAtRacingWriteAt(t.TempDir())
		_ = testStatRacingExtend(t.TempDir())
	}
}
