package crashlog

import (
	"os"
	"testing"
)

// TestBoot runs the boot program on a fresh directory, then again on the
// committed file; then on files a crash may leave: one cut short, and one with
// the flag unset after the data.
func TestBoot(t *testing.T) {
	dir := t.TempDir()
	Boot(dir)
	b, err := os.ReadFile(dir + "/log")
	if err != nil {
		t.Fatal(err)
	}
	if len(b) != 9 || !dataOk(b[:8]) || b[8] != 1 {
		t.Fatalf("after the first boot the file is %x", b)
	}
	Boot(dir) // the committed path
	for _, img := range [][]byte{{}, {1, 2, 3}, {0, 0, 0, 0, 0, 0, 0, 0}, append(newData(), 0)} {
		if err := os.WriteFile(dir+"/log", img, 0o666); err != nil {
			t.Fatal(err)
		}
		Boot(dir)
		b, err := os.ReadFile(dir + "/log")
		if err != nil {
			t.Fatal(err)
		}
		if len(b) != 9 || !dataOk(b[:8]) || b[8] != 1 {
			t.Fatalf("from %x the file is %x", img, b)
		}
		Boot(dir)
	}
}
