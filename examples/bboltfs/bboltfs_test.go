package bboltfs

import (
	"fmt"
	"os"
	"os/exec"
	"sync/atomic"
	"syscall"
	"testing"
	"time"
)

// TestMain runs a helper when re-executed by a test (BBOLTFS_HELPER set): the
// boot loop of TestBootMiniboltKilled, or a Linux fact of linux_test.go.
func TestMain(m *testing.M) {
	switch h := os.Getenv("BBOLTFS_HELPER"); h {
	case "":
		os.Exit(m.Run())
	case "bootloop":
		// boot forever, until the parent kills the process
		for {
			BootMinibolt(os.Getenv("BBOLTFS_DIR"))
		}
	default:
		f, ok := facts[h]
		if !ok {
			os.Exit(3)
		}
		fmt.Println("RESULT", f(os.Getenv("BBOLTFS_DIR")))
		os.Exit(0)
	}
}

// The programs hold in Go, each in a fresh directory, and meet no
// environmental failure (which would make them return true vacuously).
func TestPrograms(t *testing.T) {
	for name, f := range map[string]func(string) bool{
		"testMinibolt":           testMinibolt,
		"testMiniboltConcurrent": testMiniboltConcurrent,
	} {
		t.Run(name, func(t *testing.T) {
			before := atomic.LoadUint64(&envErrors)
			if !f(t.TempDir()) {
				t.Fatalf("%s returned false", name)
			}
			if atomic.LoadUint64(&envErrors) != before {
				t.Fatalf("%s met an environmental failure", name)
			}
		})
	}
}

// The concurrent program, again and again (and under -race, which checks that
// it races on no Go memory).
func TestMiniboltConcurrentRepeated(t *testing.T) {
	n := 30
	if testing.Short() {
		n = 3
	}
	for i := 0; i < n; i++ {
		before := atomic.LoadUint64(&envErrors)
		if !testMiniboltConcurrent(t.TempDir()) || atomic.LoadUint64(&envErrors) != before {
			t.Fatalf("run %d failed", i)
		}
	}
}

// After a failed commit the handle refuses every transaction, and a reopen
// sees the last commit that succeeded.
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
