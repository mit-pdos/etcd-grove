//go:build linux

package semantics

// Measurements behind the trusted models' Go examples (model_*.go), run on
// this machine (Linux 7.0, ext4 with its defaults: configuration C,
// env_config.go). The tests make their files in a directory under the working
// directory (the package's, on ext4), not in $TMPDIR (often a tmpfs).

import (
	"errors"
	"os"
	"syscall"
	"testing"

	"golang.org/x/sys/unix"
)

// extDir is a fresh directory under the working directory, removed after the test.
func extDir(t *testing.T) string {
	t.Helper()
	d, err := os.MkdirTemp(".", "models-test-")
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { os.RemoveAll(d) })
	return d
}

// model_os_close_nil.go: a nil *File's Close is ErrInvalid.
func TestCloseNil(t *testing.T) {
	var f *os.File
	if err := f.Close(); err != os.ErrInvalid {
		t.Fatalf("Close of a nil *File: %v, want os.ErrInvalid", err)
	}
}

// model_syscall_fallocate.go: syscall.Fallocate's mode 0 grows the size, mode 1 does not.
func TestSyscallFallocate(t *testing.T) {
	d := extDir(t)
	f, err := os.Create(d + "/seg")
	if err != nil {
		t.Fatal(err)
	}
	defer f.Close()
	if err := syscall.Fallocate(int(f.Fd()), 0, 0, 4096); err != nil {
		t.Fatal(err)
	}
	if err := syscall.Fallocate(int(f.Fd()), 1, 0, 8192); err != nil {
		t.Fatal(err)
	}
	fi, _ := f.Stat()
	if fi.Size() != 4096 {
		t.Fatalf("size %d, want 4096", fi.Size())
	}
	if err := syscall.Fallocate(int(f.Fd()), 0, 0, 0); !errors.Is(err, syscall.EINVAL) {
		t.Fatalf("len 0: %v, want EINVAL", err)
	}
}

// model_syscall_fcntlflock.go: F_OFD_GETLK on a closed fd is EBADF; on /dev/null and on a
// regular file with no lock, nil and Type F_UNLCK.
func TestOFDGetlk(t *testing.T) {
	// a closed fd: a fresh fd, closed
	fd, err := syscall.Open("/dev/null", syscall.O_RDONLY|syscall.O_CLOEXEC, 0)
	if err != nil {
		t.Fatal(err)
	}
	syscall.Close(fd)
	lk := syscall.Flock_t{Type: syscall.F_RDLCK}
	if err := syscall.FcntlFlock(uintptr(fd), unix.F_OFD_GETLK, &lk); err != syscall.EBADF {
		t.Fatalf("closed fd: %v, want EBADF", err)
	}
	if lk.Type != syscall.F_RDLCK {
		t.Fatalf("closed fd: Type %d changed", lk.Type)
	}
	for _, name := range []string{"/dev/null", extDir(t) + "/LOCK"} {
		f, err := os.OpenFile(name, os.O_RDWR|os.O_CREATE, 0o600)
		if err != nil {
			t.Fatal(err)
		}
		lk := syscall.Flock_t{Type: syscall.F_RDLCK}
		if err := syscall.FcntlFlock(f.Fd(), unix.F_OFD_GETLK, &lk); err != nil {
			t.Fatalf("%s: %v", name, err)
		}
		if lk.Type != syscall.F_UNLCK {
			t.Fatalf("%s: Type %d, want F_UNLCK", name, lk.Type)
		}
		f.Close()
	}
	// a conflicting OFD lock held through another open file description
	name := extDir(t) + "/LOCK2"
	a, _ := os.Create(name)
	defer a.Close()
	w := syscall.Flock_t{Type: syscall.F_WRLCK}
	if err := syscall.FcntlFlock(a.Fd(), unix.F_OFD_SETLK, &w); err != nil {
		t.Fatal(err)
	}
	b, _ := os.Open(name)
	defer b.Close()
	q := syscall.Flock_t{Type: syscall.F_RDLCK}
	if err := syscall.FcntlFlock(b.Fd(), unix.F_OFD_GETLK, &q); err != nil {
		t.Fatal(err)
	}
	if q.Type != syscall.F_WRLCK || q.Pid != -1 {
		t.Fatalf("conflict: Type %d Pid %d, want F_WRLCK and -1", q.Type, q.Pid)
	}
}

// model_syscall_fcntlflock.go: F_OFD_GETLK writes the description's padding back as it was
// (with no concurrent writer).
func TestOFDGetlkPadding(t *testing.T) {
	f, err := os.Create(extDir(t) + "/LOCK")
	if err != nil {
		t.Fatal(err)
	}
	defer f.Close()
	lk := syscall.Flock_t{Type: syscall.F_RDLCK,
		Pad_cgo_0: [4]byte{0xaa, 0xbb, 0xcc, 0xdd}, Pad_cgo_1: [4]byte{0x11, 0x22, 0x33, 0x44}}
	if err := syscall.FcntlFlock(f.Fd(), unix.F_OFD_GETLK, &lk); err != nil {
		t.Fatal(err)
	}
	if lk.Pad_cgo_0 != [4]byte{0xaa, 0xbb, 0xcc, 0xdd} || lk.Pad_cgo_1 != [4]byte{0x11, 0x22, 0x33, 0x44} {
		t.Fatalf("padding changed: %x %x", lk.Pad_cgo_0, lk.Pad_cgo_1)
	}
}

// model_os_writefile.go: an empty Write is (0, nil) on a writable fd and EBADF on a read-only
// one, and changes nothing; WriteFile of an empty slice makes an empty file.
func TestEmptyWrite(t *testing.T) {
	d := extDir(t)
	f, _ := os.Create(d + "/f")
	f.Write([]byte("abc"))
	if n, err := f.Write(nil); n != 0 || err != nil {
		t.Fatalf("writable: (%d, %v), want (0, nil)", n, err)
	}
	if off, _ := f.Seek(0, 1); off != 3 {
		t.Fatalf("offset %d, want 3", off)
	}
	f.Close()
	r, _ := os.Open(d + "/f")
	if _, err := r.Write(nil); !errors.Is(err, syscall.EBADF) {
		t.Fatalf("read-only: %v, want EBADF", err)
	}
	r.Close()
	if err := os.WriteFile(d+"/.touch", []byte(""), 0o600); err != nil {
		t.Fatal(err)
	}
	if fi, err := os.Stat(d + "/.touch"); err != nil || fi.Size() != 0 {
		t.Fatalf("Stat: %v %v", fi, err)
	}
}

// model_os_stat.go: Stat's mode of a directory and of a file: the type, and the permission
// bits (Mkdir's and OpenFile's perm under the umask).
func TestStatMode(t *testing.T) {
	d := extDir(t)
	if err := os.Mkdir(d+"/d", 0o700); err != nil {
		t.Fatal(err)
	}
	f, _ := os.OpenFile(d+"/f", os.O_RDWR|os.O_CREATE, 0o600)
	f.Close()
	di, err := os.Stat(d + "/d")
	if err != nil || !di.IsDir() || di.Mode()&os.ModeType != os.ModeDir || di.Mode().Perm() != 0o700 {
		t.Fatalf("dir: %v %v", di.Mode(), err)
	}
	fi, err := os.Stat(d + "/f")
	if err != nil || fi.IsDir() || !fi.Mode().IsRegular() || fi.Mode().Perm() != 0o600 || fi.Size() != 0 {
		t.Fatalf("file: %v %v", fi.Mode(), err)
	}
	if _, err := os.Stat(d + "/none"); !errors.Is(err, syscall.ENOENT) {
		t.Fatalf("missing: %v", err)
	}
	li, err := os.Lstat(d + "/d")
	if err != nil || !li.IsDir() {
		t.Fatalf("Lstat: %v %v", li, err)
	}
}

// model_os_mkdirall.go and model_os_removeall.go: MkdirAll makes the chain; RemoveAll removes
// the tree, and nil on a missing path.
func TestMkdirAllRemoveAll(t *testing.T) {
	d := extDir(t)
	if err := os.MkdirAll(d+"/a/b/c", 0o700); err != nil {
		t.Fatal(err)
	}
	if err := os.MkdirAll(d+"/a/b/c", 0o700); err != nil {
		t.Fatalf("again: %v", err)
	}
	f, _ := os.Create(d + "/a/b/f")
	f.Close()
	if err := os.MkdirAll(d+"/a/b/f", 0o700); !errors.Is(err, syscall.ENOTDIR) {
		t.Fatalf("over a file: %v, want ENOTDIR", err)
	}
	if err := os.RemoveAll(d + "/a"); err != nil {
		t.Fatal(err)
	}
	if _, err := os.Stat(d + "/a"); !errors.Is(err, syscall.ENOENT) {
		t.Fatalf("a after RemoveAll: %v", err)
	}
	if err := os.RemoveAll(d + "/a"); err != nil {
		t.Fatalf("missing: %v", err)
	}
	var pe *os.PathError
	if err := os.RemoveAll(d + "/."); !errors.As(err, &pe) || pe.Op != "RemoveAll" || !errors.Is(err, syscall.EINVAL) {
		t.Fatalf("dot: %v", err)
	}
}
