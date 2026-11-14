//go:build linux

package semantics

// Measurements behind the trusted models' Go examples (model_*.go), on
// configuration C (env_config.go): run-models-on-c.sh makes and mounts a C
// filesystem with notes/axiom-review/fs-config/mkfs-mount.sh, checks it with
// check.sh (its output is the record) and runs these tests in it
// ($SEMANTICS_C_DIR). Run with plain `go test`, they use a directory under the
// working directory, not $TMPDIR (often a tmpfs).

import (
	"errors"
	"fmt"
	"os"
	"path/filepath"
	"sync"
	"syscall"
	"testing"

	"golang.org/x/sys/unix"
)

// extDir is a fresh directory under $SEMANTICS_C_DIR (a configuration-C mount made by
// run-models-on-c.sh) or, if unset, under the working directory, removed after the test.
func extDir(t *testing.T) string {
	t.Helper()
	base := os.Getenv("SEMANTICS_C_DIR")
	if base == "" {
		base = "."
	}
	d, err := os.MkdirTemp(base, "models-test-")
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

// model_os_mkdirall_above.go: at an existing directory (a root) and at its parent (an
// ancestor), Stat succeeds with a directory, Mkdir fails with EEXIST and changes nothing, and
// MkdirAll returns nil.
func TestMkdirAllAboveRoot(t *testing.T) {
	d, err := filepath.Abs(extDir(t))
	if err != nil {
		t.Fatal(err)
	}
	f, _ := os.Create(d + "/f")
	f.Close()
	for _, p := range []string{d, filepath.Dir(d)} {
		var before syscall.Stat_t
		if err := syscall.Stat(p, &before); err != nil {
			t.Fatal(err)
		}
		names0, _ := os.ReadDir(p)
		if fi, err := os.Stat(p); err != nil || !fi.IsDir() {
			t.Fatalf("Stat(%s): %v %v", p, fi, err)
		}
		if err := os.Mkdir(p, 0o700); !errors.Is(err, syscall.EEXIST) {
			t.Fatalf("Mkdir(%s): %v, want EEXIST", p, err)
		}
		if err := os.MkdirAll(p, 0o700); err != nil {
			t.Fatalf("MkdirAll(%s): %v", p, err)
		}
		var after syscall.Stat_t
		if err := syscall.Stat(p, &after); err != nil || after.Ino != before.Ino || after.Nlink != before.Nlink {
			t.Fatalf("%s changed: ino %d->%d nlink %d->%d (%v)", p, before.Ino, after.Ino, before.Nlink, after.Nlink, err)
		}
		names1, _ := os.ReadDir(p)
		if p == d && len(names1) != len(names0) {
			t.Fatalf("%s: entries %d -> %d", p, len(names0), len(names1))
		}
	}
}

// model_os_stat_above.go and model_os_open_above.go: at "/" and at a root's parent (an
// ancestor of a directory of C), Stat and Lstat succeed with a directory; a read-only open
// succeeds, its fsync and close return 0; the directory is unchanged; a writable open fails with
// EISDIR. Lstat of a symlink to a directory sees a symlink, Stat a directory.
func TestStatOpenAboveRoot(t *testing.T) {
	d, err := filepath.Abs(extDir(t))
	if err != nil {
		t.Fatal(err)
	}
	for _, p := range []string{"/", filepath.Dir(d)} {
		var before syscall.Stat_t
		if err := syscall.Stat(p, &before); err != nil {
			t.Fatal(err)
		}
		if fi, err := os.Stat(p); err != nil || !fi.IsDir() {
			t.Fatalf("Stat(%s): %v %v", p, fi, err)
		}
		if fi, err := os.Lstat(p); err != nil || !fi.IsDir() {
			t.Fatalf("Lstat(%s): %v %v", p, fi, err)
		}
		f, err := os.Open(p)
		if err != nil {
			t.Fatalf("Open(%s): %v", p, err)
		}
		if err := f.Sync(); err != nil {
			t.Fatalf("Sync(%s): %v", p, err)
		}
		if err := f.Close(); err != nil {
			t.Fatalf("Close(%s): %v", p, err)
		}
		for _, fl := range []int{os.O_WRONLY, os.O_RDWR} {
			if _, err := os.OpenFile(p, fl, 0); !errors.Is(err, syscall.EISDIR) {
				t.Fatalf("OpenFile(%s, %d): %v, want EISDIR", p, fl, err)
			}
		}
		var after syscall.Stat_t
		if err := syscall.Stat(p, &after); err != nil || after.Ino != before.Ino ||
			after.Nlink != before.Nlink || after.Mtim != before.Mtim {
			t.Fatalf("%s changed: ino %d->%d nlink %d->%d (%v)", p, before.Ino, after.Ino,
				before.Nlink, after.Nlink, err)
		}
	}
	if err := os.Mkdir(d+"/dir", 0o700); err != nil {
		t.Fatal(err)
	}
	if err := os.Symlink(d+"/dir", d+"/link"); err != nil {
		t.Fatal(err)
	}
	if fi, err := os.Lstat(d + "/link"); err != nil || fi.Mode()&os.ModeType != os.ModeSymlink {
		t.Fatalf("Lstat(link): %v %v", fi, err)
	}
	if fi, err := os.Stat(d + "/link"); err != nil || !fi.IsDir() {
		t.Fatalf("Stat(link): %v %v", fi, err)
	}
}

// model_os_filestat_name.go: Name is the base name of the path given to Stat, "/" for "/", and
// the base name of the *File's name for File.Stat.
func TestFileStatName(t *testing.T) {
	d, err := filepath.Abs(extDir(t))
	if err != nil {
		t.Fatal(err)
	}
	if err := os.Mkdir(d+"/wal", 0o700); err != nil {
		t.Fatal(err)
	}
	f, err := os.Create(d + "/wal/0000-0000.wal")
	if err != nil {
		t.Fatal(err)
	}
	defer f.Close()
	if fi, err := os.Stat(d + "/wal"); err != nil || fi.Name() != "wal" {
		t.Fatalf("Stat(wal): %v %v", fi, err)
	}
	if fi, err := os.Lstat(d + "/wal"); err != nil || fi.Name() != "wal" {
		t.Fatalf("Lstat(wal): %v %v", fi, err)
	}
	if fi, err := os.Stat("/"); err != nil || fi.Name() != "/" {
		t.Fatalf("Stat(/): %v %v", fi, err)
	}
	if fi, err := f.Stat(); err != nil || fi.Name() != "0000-0000.wal" {
		t.Fatalf("File.Stat: %v %v", fi, err)
	}
}

// meta_enoent.go: ENOENT from open only for a path that does not resolve, from getdents only
// for a removed directory; never for a present directory, a file in it, or a read of it, while
// other goroutines create, rename and remove other entries of the directory and of its parent.
func TestEnoent(t *testing.T) {
	d := extDir(t)
	isNoent := func(err error) bool { return errors.Is(err, syscall.ENOENT) }
	if _, err := os.Open(d + "/missing"); !isNoent(err) {
		t.Fatalf("Open(missing): %v, want ENOENT", err)
	}
	if _, err := os.Open(d + "/missing/x"); !isNoent(err) {
		t.Fatalf("Open(missing/x): %v, want ENOENT", err)
	}
	if err := os.Mkdir(d+"/gone", 0o700); err != nil {
		t.Fatal(err)
	}
	g, err := os.Open(d + "/gone")
	if err != nil {
		t.Fatal(err)
	}
	if err := os.Remove(d + "/gone"); err != nil {
		t.Fatal(err)
	}
	if _, err := os.OpenFile(d+"/gone/x", os.O_RDWR|os.O_CREATE, 0o600); !isNoent(err) {
		t.Fatalf("OpenFile(gone/x, O_CREAT): %v, want ENOENT", err)
	}
	if names, err := g.Readdirnames(-1); !isNoent(err) {
		t.Fatalf("Readdirnames of a removed directory: %v %v, want ENOENT", names, err)
	}
	g.Close()

	// A directory large enough for an htree index (ext4 dir_index: more than one block).
	w := d + "/wal"
	if err := os.Mkdir(w, 0o700); err != nil {
		t.Fatal(err)
	}
	seg := func(i int) string { return filepath.Join(w, fmt.Sprintf("%016x-%016x.wal", i, i)) }
	for i := 0; i < 2000; i++ {
		f, err := os.Create(seg(i))
		if err != nil {
			t.Fatal(err)
		}
		f.Close()
	}
	stop := make(chan struct{})
	var wg sync.WaitGroup
	churn := func(dir string, k int) {
		defer wg.Done()
		for n := 0; ; n++ {
			select {
			case <-stop:
				return
			default:
			}
			a := filepath.Join(dir, fmt.Sprintf("churn-%d-%d", k, n%64))
			b := a + ".tmp"
			if f, err := os.Create(b); err == nil {
				f.Close()
			}
			os.Rename(b, a)
			os.Remove(a)
			os.Mkdir(b, 0o700)
			os.Remove(b)
		}
	}
	for k := 0; k < 4; k++ {
		wg.Add(2)
		go churn(w, k)
		go churn(d, k)
	}
	fails := 0
	for i := 0; i < 3000; i++ {
		if f, err := os.Open(w); err != nil {
			fails++
			if isNoent(err) {
				t.Errorf("Open(wal) under churn: ENOENT (%v)", err)
			}
		} else {
			if _, err := f.Readdirnames(-1); err != nil {
				fails++
				if isNoent(err) {
					t.Errorf("Readdirnames(wal) under churn: ENOENT (%v)", err)
				}
			}
			f.Close()
		}
		if f, err := os.Open(seg(i % 2000)); err != nil {
			fails++
			if isNoent(err) {
				t.Errorf("Open(wal/seg) under churn: ENOENT (%v)", err)
			}
		} else {
			f.Close()
		}
	}
	close(stop)
	wg.Wait()
	t.Logf("3000 rounds of open/readdir under churn: %d failures, none ENOENT", fails)
}
