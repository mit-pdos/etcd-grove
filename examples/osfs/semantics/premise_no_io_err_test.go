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
// and its rename fail with EPERM, even as root; a process that may not search or write the
// directory gets EACCES (extDir's directory is 0700, root's: the child's EACCES is a search
// failure). Needs root (to set the attributes and to run the child as another user).
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
	// a child running as nobody: unlink in a directory it may not search or write
	if err := os.WriteFile(f, []byte("x"), 0o666); err != nil {
		t.Fatal(err)
	}
	if e := asNobody(t, "unlink", f); e != syscall.EACCES {
		t.Fatalf("child's unlink: %v, want EACCES", e)
	}
	if _, err := os.Stat(f); err != nil {
		t.Fatalf("the child's failed unlink removed the file: %v", err)
	}
}

// asNobody runs op on path in a child process (this test binary, as TestNoIoErrPermHelper) with
// uid and gid 65534 (nobody), and returns its errno (0 on success). op: unlink, rmdir, mkdir,
// create (open O_CREAT|O_RDWR), openrw (open O_RDWR), open (O_RDONLY). Needs root.
func asNobody(t *testing.T, op, path string) syscall.Errno {
	t.Helper()
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
	cmd.Env = append(os.Environ(), "NOIOERR_PERM_HELPER="+op+" "+path)
	cmd.SysProcAttr = &syscall.SysProcAttr{Credential: &syscall.Credential{Uid: 65534, Gid: 65534}}
	out, err := cmd.CombinedOutput()
	if err != nil {
		t.Fatalf("child: %v\n%s", err, out)
	}
	i := strings.Index(string(out), "HELPER-ERRNO ")
	if i < 0 {
		t.Fatalf("child: %s", out)
	}
	var e int
	if _, err := fmt.Sscanf(string(out[i:]), "HELPER-ERRNO %d", &e); err != nil {
		t.Fatalf("child: %s: %v", out, err)
	}
	return syscall.Errno(e)
}

// The child of asNobody (runs only with NOIOERR_PERM_HELPER set to "op path").
func TestNoIoErrPermHelper(t *testing.T) {
	arg := os.Getenv("NOIOERR_PERM_HELPER")
	if arg == "" {
		t.Skip("helper")
	}
	op, path, _ := strings.Cut(arg, " ")
	var err error
	switch op {
	case "unlink":
		err = syscall.Unlink(path)
	case "rmdir":
		err = syscall.Rmdir(path)
	case "mkdir":
		err = syscall.Mkdir(path, 0o700)
	case "create", "openrw", "open":
		fl := syscall.O_RDWR | syscall.O_CLOEXEC
		if op == "create" {
			fl |= syscall.O_CREAT
		}
		if op == "open" {
			fl = syscall.O_RDONLY | syscall.O_CLOEXEC
		}
		var fd int
		fd, err = syscall.Open(path, fl, 0o600)
		if err == nil {
			syscall.Close(fd)
		}
	default:
		t.Fatalf("op %q", op)
	}
	e, _ := err.(syscall.Errno)
	fmt.Printf("HELPER-ERRNO %d\n", int(e))
}

// permDir is a fresh directory of mode m, root's, whose ancestors nobody may search (extDir's
// directory is made 0755 for it, as the mount point above it is). Needs root.
func permDir(t *testing.T, m os.FileMode) string {
	t.Helper()
	base := extDir(t)
	if err := os.Chmod(base, 0o755); err != nil {
		t.Fatal(err)
	}
	d := base + "/d"
	if err := os.Mkdir(d, 0o700); err != nil {
		t.Fatal(err)
	}
	if err := os.Chmod(d, m); err != nil {
		t.Fatal(err)
	}
	return d
}

// The search permission on a root's ancestors (Impl.lean's "Environment": the process may search
// every ancestor of every root): under an ancestor nobody may not search (0700, root's), a
// directory nobody may write (0777) still gives nobody EACCES for unlink and rmdir of an absent
// name (where PathErrno would say ENOENT) and for an O_CREAT open (where the semantics has a
// success). Control: with the ancestor 0755, unlink of the absent name gives ENOENT. Needs root.
func TestNoIoErrPermAncestor(t *testing.T) {
	if os.Getuid() != 0 {
		t.Skip("needs root")
	}
	anc := permDir(t, 0o700)
	root := anc + "/root"
	if err := os.Mkdir(root, 0o777); err != nil {
		t.Fatal(err)
	}
	if err := os.Chmod(root, 0o777); err != nil {
		t.Fatal(err)
	}
	for _, op := range []string{"unlink", "rmdir", "create"} {
		if e := asNobody(t, op, root+"/absent"); e != syscall.EACCES {
			t.Fatalf("ancestor 0700: %s: %v, want EACCES", op, e)
		}
	}
	if err := os.Chmod(anc, 0o755); err != nil {
		t.Fatal(err)
	}
	if e := asNobody(t, "unlink", root+"/absent"); e != syscall.ENOENT {
		t.Fatalf("ancestor 0755: unlink: %v, want ENOENT", e)
	}
}

// The write permission on a file (Impl.lean's "Environment": the process may read and write every
// file of the roots' trees): an open O_RDWR of a 0444 file in a directory nobody may search and
// write gives nobody EACCES (the semantics' open succeeds). Control: 0666, success. Needs root.
func TestNoIoErrPermFileWrite(t *testing.T) {
	if os.Getuid() != 0 {
		t.Skip("needs root")
	}
	d := permDir(t, 0o777)
	f := d + "/0.wal"
	if err := os.WriteFile(f, nil, 0o444); err != nil {
		t.Fatal(err)
	}
	if err := os.Chmod(f, 0o444); err != nil {
		t.Fatal(err)
	}
	if e := asNobody(t, "openrw", f); e != syscall.EACCES {
		t.Fatalf("0444: open O_RDWR: %v, want EACCES", e)
	}
	if err := os.Chmod(f, 0o666); err != nil {
		t.Fatal(err)
	}
	if e := asNobody(t, "openrw", f); e != 0 {
		t.Fatalf("0666: open O_RDWR: %v, want success", e)
	}
}

// sysctl reads /proc/sys/fs/<name> as an integer (-1 if unreadable).
func sysctl(name string) int {
	b, err := os.ReadFile("/proc/sys/fs/" + name)
	if err != nil {
		return -1
	}
	n, err := strconv.Atoi(strings.TrimSpace(string(b)))
	if err != nil {
		return -1
	}
	return n
}

// fs.protected_symlinks (Impl.lean's "Environment"): with it set, a symlink in a sticky
// world-writable directory, owned by neither the directory's owner nor the follower, is not
// followed as a path's last component: nobody's read-only open of it (as the open of a root's
// ancestor, which may be a symlink to a directory) gives EACCES, where the open of its target
// succeeds. (As an inner component it is followed: an unlink through it reaches the target.)
// Needs root; skipped if the sysctl is 0.
func TestNoIoErrProtectedSymlinks(t *testing.T) {
	if os.Getuid() != 0 {
		t.Skip("needs root")
	}
	if sysctl("protected_symlinks") < 1 {
		t.Skip("fs.protected_symlinks is not set")
	}
	d := permDir(t, os.ModeSticky|0o777)
	target := d + "/target"
	if err := os.Mkdir(target, 0o777); err != nil {
		t.Fatal(err)
	}
	if err := os.Chmod(target, 0o777); err != nil {
		t.Fatal(err)
	}
	link := d + "/link"
	if err := os.Symlink(target, link); err != nil {
		t.Fatal(err)
	}
	if err := os.Lchown(link, 65533, 65533); err != nil {
		t.Fatal(err)
	}
	if e := asNobody(t, "open", link); e != syscall.EACCES {
		t.Fatalf("the protected symlink: open: %v, want EACCES", e)
	}
	if e := asNobody(t, "open", target); e != 0 {
		t.Fatalf("its target: open: %v, want success", e)
	}
	if e := asNobody(t, "unlink", link+"/absent"); e != syscall.ENOENT {
		t.Fatalf("through the symlink as an inner component: unlink: %v, want ENOENT", e)
	}
}

// fs.protected_regular (Impl.lean's "Environment"): with it set, an O_CREAT open of an existing
// regular file in a sticky world-writable directory, owned by neither the directory's owner nor
// the caller, fails with EACCES, even as root and with the file's mode 0666 (the semantics' open
// succeeds). Control: without O_CREAT, success. Needs root; skipped if the sysctl is 0.
func TestNoIoErrProtectedRegular(t *testing.T) {
	if os.Getuid() != 0 {
		t.Skip("needs root")
	}
	if sysctl("protected_regular") < 1 {
		t.Skip("fs.protected_regular is not set")
	}
	d := permDir(t, os.ModeSticky|0o777)
	f := d + "/0.wal"
	if err := os.WriteFile(f, nil, 0o666); err != nil {
		t.Fatal(err)
	}
	if err := os.Chmod(f, 0o666); err != nil {
		t.Fatal(err)
	}
	if err := os.Chown(f, 65533, 65533); err != nil {
		t.Fatal(err)
	}
	if _, err := syscall.Open(f, syscall.O_RDWR|syscall.O_CREAT|syscall.O_CLOEXEC, 0o600); err != syscall.EACCES {
		t.Fatalf("as root: open O_CREAT: %v, want EACCES", err)
	}
	fd, err := syscall.Open(f, syscall.O_RDWR|syscall.O_CLOEXEC, 0)
	if err != nil {
		t.Fatalf("as root: open without O_CREAT: %v", err)
	}
	syscall.Close(fd)
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
