//go:build linux

package semantics

// Measurements behind premise_no_io_err.go's lock requests and directory reads, on configuration
// C (env_config.go): run-models-on-c.sh runs them with the other models' tests. Support only: the
// premise is an environment assumption (no ENOLCK, no I/O error); these show that on C, with no
// memory pressure and a healthy device, the calls it covers succeed whenever the semantics lets
// them.

import (
	"fmt"
	"os"
	"os/exec"
	"strconv"
	"strings"
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

// Configuration C's permissions (premise_no_io_err.go, Impl.lean's "Environment", 2026-11-19): the
// premise assumes the process may search and write the covered directories, no sticky bit, no
// immutable or append-only attribute and no security module denies a path call. The contrast,
// why it is an assumption: with the immutable or the append-only attribute on a file, its unlink
// and its rename fail with EPERM, even as root; a process that may not write the directory gets
// EACCES. Needs root (to set the attributes and to run the child as another user).
func TestNoIoErrPermissions(t *testing.T) {
	if os.Getuid() != 0 {
		t.Skip("needs root")
	}
	dir := extDir(t)
	f := dir + "/0.wal"
	for _, attr := range []struct {
		name string
		flag int
	}{{"immutable", 0x10}, {"append-only", 0x20}} { // FS_IMMUTABLE_FL, FS_APPEND_FL (linux/fs.h)
		if err := os.WriteFile(f, []byte("x"), 0o600); err != nil {
			t.Fatal(err)
		}
		setFlags := func(v int) error {
			g, err := os.Open(f)
			if err != nil {
				t.Fatal(err)
			}
			defer g.Close()
			return unix.IoctlSetPointerInt(int(g.Fd()), unix.FS_IOC_SETFLAGS, v)
		}
		if err := setFlags(attr.flag); err != nil {
			// no CAP_LINUX_IMMUTABLE here (a container, an idmapped mount): not measured
			t.Logf("%s: FS_IOC_SETFLAGS: %v: not measured", attr.name, err)
			os.Remove(f)
			continue
		}
		if err := syscall.Unlink(f); err != syscall.EPERM {
			setFlags(0)
			t.Fatalf("%s: unlink: %v, want EPERM", attr.name, err)
		}
		if err := syscall.Rename(f, dir+"/1.wal"); err != syscall.EPERM {
			setFlags(0)
			t.Fatalf("%s: rename: %v, want EPERM", attr.name, err)
		}
		setFlags(0)
		if err := syscall.Unlink(f); err != nil {
			t.Fatalf("%s cleared: unlink: %v", attr.name, err)
		}
	}
	// a child running as nobody: unlink in a directory it may not write
	if err := os.WriteFile(f, []byte("x"), 0o666); err != nil {
		t.Fatal(err)
	}
	// the test binary, copied where nobody may run it
	bin, err := os.MkdirTemp("", "noioerr-perm-")
	if err != nil {
		t.Fatal(err)
	}
	defer os.RemoveAll(bin)
	self, err := os.ReadFile(os.Args[0])
	if err != nil {
		t.Fatal(err)
	}
	if err := os.Chmod(bin, 0o755); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(bin+"/t", self, 0o755); err != nil {
		t.Fatal(err)
	}
	cmd := exec.Command(bin+"/t", "-test.run=^TestNoIoErrPermHelper$", "-test.count=1")
	cmd.Env = append(os.Environ(), "NOIOERR_PERM_HELPER="+f)
	cmd.SysProcAttr = &syscall.SysProcAttr{Credential: &syscall.Credential{Uid: 65534, Gid: 65534}}
	out, err := cmd.CombinedOutput()
	if err != nil {
		t.Fatalf("child: %v\n%s", err, out)
	}
	if !strings.Contains(string(out), "UNLINK-ERRNO 13") {
		t.Fatalf("child's unlink: %s, want EACCES (13)", out)
	}
	if _, err := os.Stat(f); err != nil {
		t.Fatalf("the child's failed unlink removed the file: %v", err)
	}
}

// The child of TestNoIoErrPermissions (runs only with NOIOERR_PERM_HELPER set).
func TestNoIoErrPermHelper(t *testing.T) {
	f := os.Getenv("NOIOERR_PERM_HELPER")
	if f == "" {
		t.Skip("helper")
	}
	err := syscall.Unlink(f)
	e, _ := err.(syscall.Errno)
	fmt.Printf("UNLINK-ERRNO %d\n", int(e))
}

// Finding A1 of the attack on PathErrno (notes/wal-units/noioerr.md, session 5): the model bounds
// neither a name's nor a path's length, Linux does: a component longer than NAME_MAX (255 bytes)
// or a path of PATH_MAX (4096) bytes or more fails with ENAMETOOLONG, whatever the tree holds, for
// mkdir, open with O_CREAT, unlink, rmdir and rename; 255 bytes and a 4095-byte path are fine.
func TestNoIoErrNameTooLong(t *testing.T) {
	dir := extDir(t)
	ok := dir + "/" + strings.Repeat("a", 255)
	long := dir + "/" + strings.Repeat("b", 256)
	if err := syscall.Mkdir(ok, 0o700); err != nil {
		t.Fatalf("mkdir of a 255-byte name: %v", err)
	}
	if err := syscall.Rmdir(ok); err != nil {
		t.Fatalf("rmdir of a 255-byte name: %v", err)
	}
	if err := syscall.Mkdir(long, 0o700); err != syscall.ENAMETOOLONG {
		t.Fatalf("mkdir of a 256-byte name: %v, want ENAMETOOLONG", err)
	}
	if _, err := syscall.Open(long, syscall.O_RDWR|syscall.O_CREAT, 0o600); err != syscall.ENAMETOOLONG {
		t.Fatalf("open O_CREAT of a 256-byte name: %v, want ENAMETOOLONG", err)
	}
	if err := syscall.Unlink(long); err != syscall.ENAMETOOLONG {
		t.Fatalf("unlink of a 256-byte name: %v, want ENAMETOOLONG", err)
	}
	if err := syscall.Rmdir(long); err != syscall.ENAMETOOLONG {
		t.Fatalf("rmdir of a 256-byte name: %v, want ENAMETOOLONG", err)
	}
	if err := os.WriteFile(dir+"/f", nil, 0o600); err != nil {
		t.Fatal(err)
	}
	if err := syscall.Rename(dir+"/f", long); err != syscall.ENAMETOOLONG {
		t.Fatalf("rename to a 256-byte name: %v, want ENAMETOOLONG", err)
	}
	// a path of 4096 bytes, every component short: dir/c/c/.../x
	p := dir
	for len(p)+201 < 4096 {
		p += "/" + strings.Repeat("c", 200)
		if err := syscall.Mkdir(p, 0o700); err != nil {
			t.Fatalf("mkdir at length %d: %v", len(p), err)
		}
	}
	fit := p + "/" + strings.Repeat("d", 4095-len(p)-1)
	if len(fit) != 4095 {
		t.Fatalf("length %d", len(fit))
	}
	if err := syscall.Mkdir(fit, 0o700); err != nil {
		t.Fatalf("mkdir of a 4095-byte path: %v", err)
	}
	over := p + "/" + strings.Repeat("e", 4096-len(p)-1)
	if err := syscall.Mkdir(over, 0o700); err != syscall.ENAMETOOLONG {
		t.Fatalf("mkdir of a 4096-byte path: %v, want ENAMETOOLONG", err)
	}
	if err := syscall.Unlink(over); err != syscall.ENAMETOOLONG {
		t.Fatalf("unlink of a 4096-byte path: %v, want ENAMETOOLONG", err)
	}
}
