package walfs

import (
	"bytes"
	"os"
	"sort"
	"testing"
)

func mustRead(t *testing.T, p string) []byte {
	t.Helper()
	b, err := os.ReadFile(p)
	if err != nil {
		t.Fatal(err)
	}
	return b
}

func names(t *testing.T, dir string) []string {
	t.Helper()
	ns, ok := readNames(dir)
	if !ok {
		t.Fatalf("readNames(%s) failed", dir)
	}
	sort.Strings(ns)
	return ns
}

// committed: dir holds seg with the data, and nothing else.
func committed(t *testing.T, dir string) {
	t.Helper()
	if ns := names(t, dir); len(ns) != 1 || ns[0] != "seg" {
		t.Fatalf("names %v", ns)
	}
	if b := mustRead(t, dir+"/seg"); !bytes.Equal(b, newData()) {
		t.Fatalf("seg is %x", b)
	}
}

// TestBoot boots a fresh directory, then the committed one, then each
// directory a crash of a commit may leave (the model's crash images: seg.tmp
// with any prefix of the data or garbage, with or without the committed seg).
func TestBoot(t *testing.T) {
	dir := t.TempDir()
	Boot(dir)
	committed(t, dir)
	Boot(dir)
	committed(t, dir)
	tmps := [][]byte{nil, {}, {1, 2, 3}, newData()[:5], newData(), append(newData(), 9)}
	for _, tmp := range tmps {
		for _, withSeg := range []bool{false, true} {
			d := t.TempDir()
			if tmp != nil {
				if err := os.WriteFile(d+"/seg.tmp", tmp, 0o666); err != nil {
					t.Fatal(err)
				}
			}
			if withSeg {
				if err := os.WriteFile(d+"/seg", newData(), 0o666); err != nil {
					t.Fatal(err)
				}
			}
			Boot(d)
			committed(t, d)
		}
	}
}

// TestBootDir: a fresh parent, the created one, and the crash images of a
// Create: wal.tmp with or without its seg, under the ordered-metadata model.
func TestBootDir(t *testing.T) {
	dir := t.TempDir()
	BootDir(dir)
	committed(t, dir+"/wal")
	BootDir(dir)
	committed(t, dir+"/wal")
	for _, withSeg := range []bool{false, true} {
		d := t.TempDir()
		if err := os.Mkdir(d+"/wal.tmp", 0o750); err != nil {
			t.Fatal(err)
		}
		if withSeg {
			if err := os.WriteFile(d+"/wal.tmp/seg", []byte{1}, 0o666); err != nil {
				t.Fatal(err)
			}
		}
		BootDir(d)
		committed(t, d+"/wal")
	}
}

// TestBootDirPOSIX: the image the POSIX model allows and the ordered model
// does not (the rename kept, the segment's entry lost) makes BootDir panic.
func TestBootDirPOSIX(t *testing.T) {
	d := t.TempDir()
	if err := os.Mkdir(d+"/wal", 0o750); err != nil {
		t.Fatal(err)
	}
	defer func() {
		if recover() == nil {
			t.Fatal("no panic on a WAL directory without its segment")
		}
	}()
	BootDir(d)
}

// TestSegment: the segment's calls, and ZeroToEnd.
func TestSegment(t *testing.T) {
	p := t.TempDir() + "/0.wal"
	off, err := Segment(p, []byte("abc"))
	if err != nil {
		t.Fatal(err)
	}
	if off != 3 {
		t.Fatalf("offset %d", off)
	}
	fi, err := os.Stat(p)
	if err != nil {
		t.Fatal(err)
	}
	if fi.Size() != segSize {
		t.Fatalf("size %d", fi.Size())
	}
	b, err := Reread(p, 4)
	if err != nil {
		t.Fatal(err)
	}
	if !bytes.Equal(b, []byte{'a', 'b', 'c', 0}) {
		t.Fatalf("read %x", b)
	}
	f, err := os.OpenFile(p, os.O_RDWR, 0)
	if err != nil {
		t.Fatal(err)
	}
	defer f.Close()
	if _, err := f.Seek(1, 0); err != nil {
		t.Fatal(err)
	}
	if err := ZeroToEnd(f); err != nil {
		t.Fatal(err)
	}
	if b := mustRead(t, p); len(b) != segSize || b[0] != 'a' || b[1] != 0 || b[2] != 0 {
		t.Fatalf("after ZeroToEnd: len %d, %x", len(b), b[:3])
	}
}
