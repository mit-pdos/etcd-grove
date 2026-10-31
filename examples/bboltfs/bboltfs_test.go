package bboltfs

import (
	"os"
	"os/exec"
	"sync/atomic"
	"syscall"
	"testing"
	"time"
)

// TestMain runs a helper when re-executed by a test (BBOLTFS_HELPER set).
func TestMain(m *testing.M) {
	switch os.Getenv("BBOLTFS_HELPER") {
	case "":
		os.Exit(m.Run())
	case "bootloop":
		// boot forever, until the parent kills the process
		for {
			BootMinibolt(os.Getenv("BBOLTFS_DIR"))
		}
	default:
		os.Exit(3)
	}
}

var targets = map[string]func(string) bool{
	"testOpenCreate":         testOpenCreate,
	"testInit":               testInit,
	"testReadPageSize":       testReadPageSize,
	"testShortReadAt":        testShortReadAt,
	"testMmapMeta":           testMmapMeta,
	"testWriteVisibleInMap":  testWriteVisibleInMap,
	"testGrowRemap":          testGrowRemap,
	"testOpenTrunc":          testOpenTrunc,
	"testReadOnlyReopen":     testReadOnlyReopen,
	"testFlock":              testFlock,
	"testTrivialCalls":       testTrivialCalls,
	"testWriteAtEmpty":       testWriteAtEmpty,
	"testConcurrentDisjoint": testConcurrentDisjoint,

	"testNegativeOffset":          testNegativeOffset,
	"testStatRacingExtendBounded": testStatRacingExtendBounded,
	"testWriteTo":                 testWriteTo,
}

// The targets hold in Go, each in a fresh directory, and meet no
// environmental failure (which would make them return true vacuously).
func TestTargets(t *testing.T) {
	for name, f := range targets {
		t.Run(name, func(t *testing.T) {
			before := atomic.LoadUint64(&envErrors)
			if !f(t.TempDir()) {
				t.Errorf("%s returned false", name)
			}
			if atomic.LoadUint64(&envErrors) != before {
				t.Errorf("%s met an environmental failure", name)
			}
		})
	}
}

// The concurrent targets, many times (and under -race).
func TestConcurrentRepeated(t *testing.T) {
	for name, f := range map[string]func(string) bool{
		"testConcurrentDisjoint":      testConcurrentDisjoint,
		"testStatRacingExtendBounded": testStatRacingExtendBounded,
		"testWriteTo":                 testWriteTo,
	} {
		for i := 0; i < 100; i++ {
			before := atomic.LoadUint64(&envErrors)
			if !f(t.TempDir()) {
				t.Fatalf("%s: run %d returned false", name, i)
			}
			if atomic.LoadUint64(&envErrors) != before {
				t.Fatalf("%s: run %d met an environmental failure", name, i)
			}
		}
	}
}

// A failed commit poisons the handle: later reads and commits refuse.
func TestMiniboltFailedCommit(t *testing.T) {
	path := t.TempDir() + "/db"
	db, err := Open(path)
	if err != nil {
		t.Fatal(err)
	}
	if err := db.Commit(2); err != nil {
		t.Fatal(err)
	}
	_ = db.file.Close() // every later system call on the file fails
	if err := db.Commit(3); err == nil {
		t.Fatal("commit on a closed file succeeded")
	}
	if _, _, _, err := db.Get(); err != errFailed {
		t.Fatalf("Get after a failed commit: %v, want errFailed", err)
	}
	if err := db.Commit(3); err != errFailed {
		t.Fatalf("Commit after a failed commit: %v, want errFailed", err)
	}
	db.Close()
	db, err = Open(path)
	if err != nil {
		t.Fatal(err)
	}
	defer db.Close()
	if txid, v, has, err := db.Get(); err != nil || txid != 2 || !has || v != 2 {
		t.Fatalf("reopened: txid %d, value %d, has %v, err %v", txid, v, has, err)
	}
}

// minibolt round-trips across remaps and grows, and across Close and Open.
func TestMiniboltRoundTrip(t *testing.T) {
	path := t.TempDir() + "/db"
	db, err := Open(path)
	if err != nil {
		t.Fatal(err)
	}
	if txid, _, has, err := db.Get(); err != nil || txid != 1 || has {
		t.Fatalf("fresh db: txid %d, has %v", txid, has)
	}
	const last = 60 // 62 pages: the mapping grows 32 -> 64 -> 128 -> 256 KiB
	for v := uint64(2); v <= last; v++ {
		if err := db.Commit(v); err != nil {
			t.Fatal(err)
		}
		if txid, got, has, err := db.Get(); err != nil || txid != v || !has || got != v {
			t.Fatalf("after commit %d: txid %d, value %d, has %v", v, txid, got, has)
		}
	}
	if db.datasz != 1<<18 {
		t.Errorf("mapping is %d bytes, want 256 KiB", db.datasz)
	}
	db.Close()
	info, err := os.Stat(path)
	if err != nil {
		t.Fatal(err)
	}
	if info.Size() != 1<<18 {
		t.Errorf("file is %d bytes, want 256 KiB (grown to the mapping)", info.Size())
	}
	db, err = Open(path)
	if err != nil {
		t.Fatal(err)
	}
	if txid, got, has, err := db.Get(); err != nil || txid != last || !has || got != last {
		t.Fatalf("reopened: txid %d, value %d, has %v", txid, got, has)
	}
	db.Close()
}

// Opening a file whose metas are both invalid (here: zero, as after a crash in
// init's first step) redoes init.
func TestMiniboltReinit(t *testing.T) {
	path := t.TempDir() + "/db"
	if err := os.WriteFile(path, make([]byte, 4*pageSize), 0o666); err != nil {
		t.Fatal(err)
	}
	db, err := Open(path)
	if err != nil {
		t.Fatal(err)
	}
	if txid, _, has, err := db.Get(); err != nil || txid != 1 || has {
		t.Fatalf("reinitialized db: txid %d, has %v", txid, has)
	}
	db.Close()
}

// The boot program, run again and again without crashes, never panics, and
// each boot commits one transaction.
func TestBootMinibolt(t *testing.T) {
	dir := t.TempDir()
	const boots = 30
	for i := 0; i < boots; i++ {
		BootMinibolt(dir)
	}
	db, err := Open(dir + "/db")
	if err != nil {
		t.Fatal(err)
	}
	defer db.Close()
	if txid, v, has, err := db.Get(); err != nil || txid != 1+boots || !has || v != txid {
		t.Fatalf("after %d boots: txid %d, value %d, has %v", boots, txid, v, has)
	}
}

// The boot program in a process that is killed (SIGKILL) at arbitrary points
// and restarted. A killed process is not a crash of the node (the page cache
// survives), so this only checks that no boot's assertion fires when a boot is
// cut short; the model's crash relation cannot be tested in Go.
func TestBootMiniboltKilled(t *testing.T) {
	if testing.Short() {
		t.Skip("slow")
	}
	dir := t.TempDir()
	for i := 0; i < 8; i++ {
		cmd := exec.Command(os.Args[0], "-test.run=^$")
		cmd.Env = append(os.Environ(), "BBOLTFS_HELPER=bootloop", "BBOLTFS_DIR="+dir)
		if err := cmd.Start(); err != nil {
			t.Fatal(err)
		}
		time.Sleep(time.Duration(50+37*i) * time.Millisecond)
		_ = cmd.Process.Kill()
		err := cmd.Wait()
		ee, ok := err.(*exec.ExitError)
		if !ok {
			t.Fatalf("boot loop %d: %v", i, err)
		}
		if ws := ee.Sys().(syscall.WaitStatus); !ws.Signaled() || ws.Signal() != syscall.SIGKILL {
			t.Fatalf("boot loop %d ended by itself (a panic?): %v", i, err)
		}
	}
	BootMinibolt(dir)
	db, err := Open(dir + "/db")
	if err != nil {
		t.Fatal(err)
	}
	defer db.Close()
	if txid, v, has, err := db.Get(); err != nil || txid < 2 || !has || v != txid {
		t.Fatalf("after the killed boots: txid %d, value %d, has %v", txid, v, has)
	}
}
