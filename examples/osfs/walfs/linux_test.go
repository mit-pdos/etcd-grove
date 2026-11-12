package walfs

import (
	"errors"
	"io"
	"os"
	"sort"
	"syscall"
	"testing"

	"golang.org/x/sys/unix"
)

// The Linux facts the namespace of the file extension rests on
// (notes/walfs-ext-plan.md), where they are not obvious. Crash behaviour
// (N1, the ordered metadata journal) cannot be tested here.

func must(t *testing.T, err error) {
	t.Helper()
	if err != nil {
		t.Fatal(err)
	}
}

// Readdirnames(-1) lists the entries without "." and "..", and a second call
// on the same fd returns nothing.
func TestReaddir(t *testing.T) {
	d := t.TempDir()
	must(t, os.WriteFile(d+"/a", nil, 0o666))
	must(t, os.Mkdir(d+"/b", 0o750))
	f, err := os.Open(d)
	must(t, err)
	defer f.Close()
	ns, err := f.Readdirnames(-1)
	must(t, err)
	sort.Strings(ns)
	if len(ns) != 2 || ns[0] != "a" || ns[1] != "b" {
		t.Fatalf("names %v", ns)
	}
	ns, err = f.Readdirnames(-1)
	if err != nil || len(ns) != 0 {
		t.Fatalf("second read: %v %v", ns, err)
	}
}

// An fd follows its file across a rename and an unlink: its name is not its
// identity (the extension's fds name the inode, not the path).
func TestFdFollowsFile(t *testing.T) {
	d := t.TempDir()
	f, err := os.OpenFile(d+"/a", os.O_RDWR|os.O_CREATE, 0o666)
	must(t, err)
	defer f.Close()
	_, err = f.WriteAt([]byte("x"), 0)
	must(t, err)
	must(t, os.Rename(d+"/a", d+"/b"))
	_, err = f.WriteAt([]byte("y"), 1)
	must(t, err)
	if b, _ := os.ReadFile(d + "/b"); string(b) != "xy" {
		t.Fatalf("b is %q", b)
	}
	// rename over an existing name: the replaced file stays readable by its fd
	g, err := os.OpenFile(d+"/c", os.O_RDWR|os.O_CREATE, 0o666)
	must(t, err)
	defer g.Close()
	_, err = g.WriteAt([]byte("old"), 0)
	must(t, err)
	must(t, os.Rename(d+"/b", d+"/c"))
	buf := make([]byte, 3)
	_, err = g.ReadAt(buf, 0)
	must(t, err)
	if string(buf) != "old" {
		t.Fatalf("replaced file reads %q", buf)
	}
	// unlink: the fd still reads and writes
	must(t, os.Remove(d+"/c"))
	_, err = f.WriteAt([]byte("z"), 2)
	must(t, err)
	_, err = f.ReadAt(buf, 0)
	must(t, err)
	if string(buf) != "xyz" {
		t.Fatalf("unlinked file reads %q", buf)
	}
}

// A directory holding an OFD-locked open file can be renamed (the WAL's
// renameWAL holds its locks), and the fd keeps working.
func TestRenameDirWithLockedFile(t *testing.T) {
	p := t.TempDir()
	must(t, os.Mkdir(p+"/w.tmp", 0o750))
	f, err := os.OpenFile(p+"/w.tmp/seg", os.O_RDWR|os.O_CREATE, 0o666)
	must(t, err)
	defer f.Close()
	must(t, lockFile(f))
	must(t, os.Rename(p+"/w.tmp", p+"/w"))
	_, err = f.WriteAt([]byte("q"), 0)
	must(t, err)
	if b, _ := os.ReadFile(p + "/w/seg"); string(b) != "q" {
		t.Fatalf("seg is %q", b)
	}
}

// Go's os.Rename refuses an existing directory as the destination, even an
// empty one (file_unix.go's rename: EEXIST, before the system call; the WAL removes
// the destination first); rename of a file onto a directory fails; a directory
// into its own subtree fails.
func TestRenameDirRules(t *testing.T) {
	p := t.TempDir()
	must(t, os.Mkdir(p+"/a", 0o750))
	must(t, os.Mkdir(p+"/b", 0o750))
	if err := os.Rename(p+"/a", p+"/b"); !errors.Is(err, syscall.EEXIST) {
		t.Fatalf("rename onto an empty directory: %v", err)
	}
	must(t, os.WriteFile(p+"/b/x", nil, 0o666))
	must(t, os.WriteFile(p+"/f", nil, 0o666))
	if err := os.Rename(p+"/f", p+"/a"); !errors.Is(err, syscall.EEXIST) {
		t.Fatalf("rename of a file onto a directory: %v", err)
	}
	// a file onto a file replaces it; a directory onto a file is ENOTDIR
	must(t, os.WriteFile(p+"/g", nil, 0o666))
	must(t, os.Rename(p+"/f", p+"/g"))
	if err := os.Rename(p+"/a", p+"/g"); !errors.Is(err, syscall.ENOTDIR) {
		t.Fatalf("rename of a directory onto a file: %v", err)
	}
	if err := os.Rename(p+"/b", p+"/b/x2"); err == nil {
		t.Fatal("rename of a directory into itself succeeded")
	}
	// os.Remove of a non-empty directory fails, of an empty one succeeds
	if err := os.Remove(p + "/b"); err == nil {
		t.Fatal("remove of a non-empty directory succeeded")
	}
	must(t, os.Remove(p+"/a"))
}

// A directory opens read-only only; its fd syncs; a read on it is EISDIR.
func TestDirFd(t *testing.T) {
	d := t.TempDir()
	if _, err := os.OpenFile(d, os.O_RDWR, 0); !errors.Is(err, syscall.EISDIR) {
		t.Fatalf("open O_RDWR of a directory: %v", err)
	}
	f, err := os.Open(d)
	must(t, err)
	defer f.Close()
	must(t, f.Sync())
	buf := make([]byte, 1)
	if _, err := f.ReadAt(buf, 0); !errors.Is(err, syscall.EISDIR) {
		t.Fatalf("read of a directory fd: %v", err)
	}
}

// fallocate: KEEP_SIZE leaves the size; mode 0 extends it with zeros and never
// shrinks it.
func TestFallocate(t *testing.T) {
	f, err := os.OpenFile(t.TempDir()+"/f", os.O_RDWR|os.O_CREATE, 0o666)
	must(t, err)
	defer f.Close()
	_, err = f.WriteAt([]byte("abc"), 0)
	must(t, err)
	must(t, unix.Fallocate(int(f.Fd()), unix.FALLOC_FL_KEEP_SIZE, 0, 4096))
	if fi, _ := f.Stat(); fi.Size() != 3 {
		t.Fatalf("size after KEEP_SIZE %d", fi.Size())
	}
	must(t, unix.Fallocate(int(f.Fd()), 0, 0, 10))
	if fi, _ := f.Stat(); fi.Size() != 10 {
		t.Fatalf("size after mode 0 %d", fi.Size())
	}
	must(t, unix.Fallocate(int(f.Fd()), 0, 0, 5))
	if fi, _ := f.Stat(); fi.Size() != 10 {
		t.Fatalf("mode 0 shrank the file to %d", fi.Size())
	}
	buf := make([]byte, 10)
	_, err = f.ReadAt(buf, 0)
	must(t, err)
	if string(buf) != "abc\x00\x00\x00\x00\x00\x00\x00" {
		t.Fatalf("contents %q", buf)
	}
}

// Seek and Write: the offset is the fd's; SeekEnd is from the size.
func TestSeekWrite(t *testing.T) {
	f, err := os.OpenFile(t.TempDir()+"/f", os.O_RDWR|os.O_CREATE, 0o666)
	must(t, err)
	defer f.Close()
	_, err = f.Write([]byte("abc"))
	must(t, err)
	if off, _ := f.Seek(0, io.SeekCurrent); off != 3 {
		t.Fatalf("offset %d", off)
	}
	if off, _ := f.Seek(-1, io.SeekEnd); off != 2 {
		t.Fatalf("end offset %d", off)
	}
	_, err = f.Write([]byte("Z"))
	must(t, err)
	if _, err := f.Seek(-1, io.SeekStart); err == nil {
		t.Fatal("a negative seek succeeded")
	}
	buf := make([]byte, 4)
	_, err = f.Seek(0, io.SeekStart)
	must(t, err)
	n, err := f.Read(buf)
	if n != 3 || string(buf[:3]) != "abZ" {
		t.Fatalf("read %d %q %v", n, buf[:n], err)
	}
	if n, err := f.Read(buf); n != 0 || err != io.EOF {
		t.Fatalf("read at EOF %d %v", n, err)
	}
}

// OFD locks conflict between two open file descriptions of one process (which
// fileutil.TryLockFile, in the purge of old segments, relies on). The
// extension's lock is trivial (any errno), which covers this but proves nothing
// of it.
func TestOfdLockConflict(t *testing.T) {
	p := t.TempDir() + "/f"
	f, err := os.OpenFile(p, os.O_RDWR|os.O_CREATE, 0o666)
	must(t, err)
	defer f.Close()
	g, err := os.OpenFile(p, os.O_RDWR, 0)
	must(t, err)
	defer g.Close()
	must(t, lockFile(f))
	if err := lockFile(g); err == nil {
		t.Fatal("a second OFD lock in the same process succeeded")
	}
}
