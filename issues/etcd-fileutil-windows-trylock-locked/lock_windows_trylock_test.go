// Reproduction for issues/etcd-fileutil-windows-trylock-locked.md (etcd-io/etcd#14252).
//
// Windows only. Drop into go.etcd.io/etcd/client/pkg/v3/fileutil (directory client/pkg/fileutil of
// etcd-io/etcd, or of the fork upamanyus/etcd at the pinned revision
// 107edf7e492a5cd7e8d958ed8a7ac9dbf1ecf81f), then run, on a Windows host, from the module
// directory client/pkg/:
//
//	go test ./fileutil/ -run 'TestTryLockFileOnLockedFile|TestPurgeFileKeepsLockedFile' -v
//
// Expected at the pin (from reading lock_windows.go; not run here, no Windows host): both tests
// FAIL. LockFileEx with LOCKFILE_FAIL_IMMEDIATELY on a file another handle has locked fails with
// ERROR_LOCK_VIOLATION, which lockFile (lock_windows.go:84-97) maps to nil, so TryLockFile returns
// a *LockedFile instead of ErrLocked, and the purger removes a WAL file the WAL holds. The tests
// pass once lockFile maps ERROR_LOCK_VIOLATION to ErrLocked.
//
// Only cross-compiled at the pin (GOOS=windows go test -c ./fileutil/ and GOOS=windows go vet).
// The existing TestLockAndUnlock (lock_test.go) checks the same thing on every platform; upstream
// CI does not run it on Windows.

//go:build windows

package fileutil

import (
	"errors"
	"fmt"
	"os"
	"path/filepath"
	"testing"
	"time"

	"go.uber.org/zap/zaptest"
)

// TryLockFile on a file locked through another handle must report ErrLocked.
func TestTryLockFileOnLockedFile(t *testing.T) {
	p := filepath.Join(t.TempDir(), "locked")
	l, err := LockFile(p, os.O_WRONLY|os.O_CREATE, PrivateFileMode)
	if err != nil {
		t.Fatal(err)
	}
	defer l.Close()

	l2, err := TryLockFile(p, os.O_WRONLY, PrivateFileMode)
	if err == nil {
		l2.Close()
		t.Fatal("TryLockFile on a locked file returned a lock (want ErrLocked)")
	}
	if !errors.Is(err, ErrLocked) {
		t.Fatalf("TryLockFile on a locked file: err = %v, want ErrLocked", err)
	}
}

// The purger must not remove a file that is locked (the WAL's protocol: the WAL keeps every file
// it still needs locked, purgeFile removes only files it can lock).
func TestPurgeFileKeepsLockedFile(t *testing.T) {
	dir := t.TempDir()
	for i := 0; i < 3; i++ {
		f, err := os.Create(filepath.Join(dir, fmt.Sprintf("%d.test", i)))
		if err != nil {
			t.Fatal(err)
		}
		f.Close()
	}
	// The oldest file is still held, as the WAL holds files above the last released snapshot.
	l, err := LockFile(filepath.Join(dir, "0.test"), os.O_WRONLY, PrivateFileMode)
	if err != nil {
		t.Fatal(err)
	}
	defer l.Close()

	stop := make(chan struct{})
	purgec := make(chan string, 10)
	errch := purgeFile(zaptest.NewLogger(t), dir, "test", 1, 10*time.Millisecond, stop, purgec, nil, true)
	time.Sleep(100 * time.Millisecond)
	close(stop)

	select {
	case f := <-purgec:
		t.Fatalf("purged %s, which is locked", f)
	case err := <-errch:
		t.Fatalf("purge error: %v", err)
	default:
	}
	if _, err := os.Stat(filepath.Join(dir, "0.test")); err != nil {
		t.Fatalf("locked file is gone: %v", err)
	}
}
