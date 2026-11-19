//go:build linux

package semantics

// Measurements behind premise_no_io_err.go's lock requests and directory reads, on configuration
// C (env_config.go): run-models-on-c.sh runs them with the other models' tests. Support only: the
// premise is an environment assumption (no ENOLCK, no I/O error); these show that on C, with no
// memory pressure and a healthy device, the calls it covers succeed whenever the semantics lets
// them.

import (
	"os"
	"strconv"
	"syscall"
	"testing"

	"golang.org/x/sys/unix"
)

const noIoErrRounds = 20000

// An uncontended whole-file OFD write lock, blocking (fileutil.LockFile's F_OFD_SETLKW) and not
// (F_OFD_SETLK), and its F_UNLCK, succeed every round; so do flock's LOCK_EX (blocking and
// LOCK_NB) and LOCK_UN on the same file (flock and OFD locks are independent: locks_flock_vs_ofd.go).
func TestNoIoErrLocks(t *testing.T) {
	name := extDir(t) + "/0000000000000000-0000000000000000.wal"
	f := openRW(t, name)
	defer f.Close()
	for i := 0; i < noIoErrRounds; i++ {
		cmd := unix.F_OFD_SETLKW
		if i%2 == 1 {
			cmd = unix.F_OFD_SETLK
		}
		if err := ofdLk(f, cmd, syscall.F_WRLCK); err != nil {
			t.Fatalf("round %d: OFD lock (cmd %d): %v", i, cmd, err)
		}
		how := syscall.LOCK_EX
		if i%2 == 1 {
			how |= syscall.LOCK_NB
		}
		if err := syscall.Flock(int(f.Fd()), how); err != nil {
			t.Fatalf("round %d: flock(%d): %v", i, how, err)
		}
		if err := syscall.Flock(int(f.Fd()), syscall.LOCK_UN); err != nil {
			t.Fatalf("round %d: flock(LOCK_UN): %v", i, err)
		}
		if err := ofdLk(f, unix.F_OFD_SETLK, syscall.F_UNLCK); err != nil {
			t.Fatalf("round %d: OFD unlock: %v", i, err)
		}
	}
	// a fresh open file description each round, as WAL.cut's LockFile of a new tail
	for i := 0; i < noIoErrRounds/10; i++ {
		g, err := os.OpenFile(name, os.O_WRONLY, 0o600)
		if err != nil {
			t.Fatal(err)
		}
		if err := ofdLk(g, unix.F_OFD_SETLKW, syscall.F_WRLCK); err != nil {
			t.Fatalf("round %d: OFD lock on a fresh description: %v", i, err)
		}
		g.Close()
	}
}

// Readdirnames(-1) of a fresh empty directory (fileutil.CreateDirAll's ReadDir) and of a directory
// of a few entries (a WAL directory) succeeds every round, with the names it holds.
func TestNoIoErrReaddir(t *testing.T) {
	base := extDir(t)
	empty := base + "/wal.tmp"
	if err := os.Mkdir(empty, 0o700); err != nil {
		t.Fatal(err)
	}
	full := base + "/wal"
	if err := os.Mkdir(full, 0o700); err != nil {
		t.Fatal(err)
	}
	for k := 0; k < 8; k++ {
		if err := os.WriteFile(full+"/"+strconv.Itoa(k)+".wal", nil, 0o600); err != nil {
			t.Fatal(err)
		}
	}
	for i := 0; i < noIoErrRounds/10; i++ {
		for _, c := range []struct {
			dir string
			n   int
		}{{empty, 0}, {full, 8}} {
			d, err := os.Open(c.dir)
			if err != nil {
				t.Fatal(err)
			}
			names, err := d.Readdirnames(-1)
			if err != nil {
				t.Fatalf("round %d: Readdirnames(%s): %v", i, c.dir, err)
			}
			if len(names) != c.n {
				t.Fatalf("round %d: Readdirnames(%s): %d names, want %d", i, c.dir, len(names), c.n)
			}
			if err := d.Close(); err != nil {
				t.Fatalf("round %d: Close(%s): %v", i, c.dir, err)
			}
		}
	}
}

// The errnos of PathErrno (premise_no_io_err.go), every round: unlink and rmdir of an absent name in
// an existing directory give ENOENT, unlink of a directory EISDIR, rmdir of a non-empty directory
// ENOTEMPTY, each with no effect; and os.RemoveAll of an absent path returns nil, of a non-empty
// directory removes it (wal.Create's renameWAL and a crash's leftover dir.tmp).
func TestNoIoErrPathErrno(t *testing.T) {
	base := extDir(t)
	dir := base + "/wal.tmp"
	for i := 0; i < noIoErrRounds/10; i++ {
		absent := base + "/wal"
		if err := syscall.Unlink(absent); err != syscall.ENOENT {
			t.Fatalf("round %d: unlink of an absent name: %v", i, err)
		}
		if err := syscall.Rmdir(absent); err != syscall.ENOENT {
			t.Fatalf("round %d: rmdir of an absent name: %v", i, err)
		}
		if err := os.RemoveAll(absent); err != nil {
			t.Fatalf("round %d: RemoveAll of an absent path: %v", i, err)
		}
		if err := os.Mkdir(dir, 0o700); err != nil {
			t.Fatal(err)
		}
		if err := os.WriteFile(dir+"/0.wal", nil, 0o600); err != nil {
			t.Fatal(err)
		}
		if err := syscall.Unlink(dir); err != syscall.EISDIR {
			t.Fatalf("round %d: unlink of a directory: %v", i, err)
		}
		if err := syscall.Rmdir(dir); err != syscall.ENOTEMPTY {
			t.Fatalf("round %d: rmdir of a non-empty directory: %v", i, err)
		}
		if _, err := os.Stat(dir + "/0.wal"); err != nil {
			t.Fatalf("round %d: the failed calls changed the tree: %v", i, err)
		}
		if err := os.RemoveAll(dir); err != nil {
			t.Fatalf("round %d: RemoveAll of a non-empty directory: %v", i, err)
		}
		if _, err := os.Stat(dir); !os.IsNotExist(err) {
			t.Fatalf("round %d: RemoveAll left the directory: %v", i, err)
		}
	}
}
