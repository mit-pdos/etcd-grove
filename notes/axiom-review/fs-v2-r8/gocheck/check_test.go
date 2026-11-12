// Round 8 checks (../../fs-v2-r8.md): Go 1.27.3's os calls whose answer the trusted models of
// TrustedCode/os.lean give without asking the extension. Run by ../run.sh on a C filesystem
// (R8_DIR); each test logs what Go returned.
package fsv2r8check

import (
	"errors"
	"io"
	"os"
	"syscall"
	"testing"
)

func dir(t *testing.T) string {
	d := os.Getenv("R8_DIR")
	if d == "" {
		t.Skip("R8_DIR not set: run ../run.sh")
	}
	return d
}

// R1: Seek past ext4's maximum file size (2^44 - 4096 with 4 KiB blocks), below the model's
// offMax (2^62): the model's Seek.impl returns (n, nil) for SEEK_SET.
func TestSeekPastMaxBytes(t *testing.T) {
	f, err := os.OpenFile(dir(t)+"/seek", os.O_RDWR|os.O_CREATE, 0o666)
	if err != nil {
		t.Fatal(err)
	}
	defer f.Close()
	for _, off := range []int64{1<<44 - 4096, 1<<44 - 4095, 1 << 44, 1 << 50, 1<<62 - 1} {
		n, err := f.Seek(off, io.SeekStart)
		t.Logf("Seek(%#x, SeekStart) = %#x, %v (EINVAL: %v)", off, n, err, errors.Is(err, syscall.EINVAL))
	}
	n, err := f.WriteAt([]byte{1}, 1<<50)
	t.Logf("WriteAt(1 byte, 2^50) = %d, %v", n, err)
}

// R2: an empty Write on a read-only file: Go issues write(fd, buf, 0), which Linux answers
// EBADF; the model's Write.impl returns (0, nil) without a system call.
func TestEmptyWriteReadOnly(t *testing.T) {
	p := dir(t) + "/ro"
	if err := os.WriteFile(p, []byte("x"), 0o666); err != nil {
		t.Fatal(err)
	}
	f, err := os.Open(p)
	if err != nil {
		t.Fatal(err)
	}
	defer f.Close()
	n, err := f.Write(nil)
	t.Logf("Write(nil) on O_RDONLY = %d, %v (EBADF: %v)", n, err, errors.Is(err, syscall.EBADF))
	n, err = f.WriteAt(nil, 0)
	t.Logf("WriteAt(nil, 0) on O_RDONLY = %d, %v", n, err)
}

// R3: empty Write/Read and a SEEK_SET after Close: Go returns ErrClosed; the model returns
// success (Write.impl, Read.impl, Seek.impl touch no fd for these).
func TestAfterClose(t *testing.T) {
	f, err := os.OpenFile(dir(t)+"/closed", os.O_RDWR|os.O_CREATE, 0o666)
	if err != nil {
		t.Fatal(err)
	}
	f.Close()
	n, err := f.Write(nil)
	t.Logf("Write(nil) after Close = %d, %v (ErrClosed: %v)", n, err, errors.Is(err, os.ErrClosed))
	n, err = f.Read(nil)
	t.Logf("Read(nil) after Close = %d, %v (ErrClosed: %v)", n, err, errors.Is(err, os.ErrClosed))
	o, err := f.Seek(0, io.SeekStart)
	t.Logf("Seek(0, SeekStart) after Close = %d, %v (ErrClosed: %v)", o, err, errors.Is(err, os.ErrClosed))
	n, err = f.WriteAt(nil, 0)
	t.Logf("WriteAt(nil, 0) after Close = %d, %v", n, err)
	n, err = f.ReadAt(nil, 0)
	t.Logf("ReadAt(nil, 0) after Close = %d, %v", n, err)
}

// R4: a directory fd after Readdirnames: Go's Seek returns EISDIR for a nonzero result; the model
// (SEEK_SET makes no extension call) returns success.
func TestDirSeek(t *testing.T) {
	d, err := os.Open(dir(t))
	if err != nil {
		t.Fatal(err)
	}
	defer d.Close()
	if _, err := d.Readdirnames(-1); err != nil {
		t.Fatal(err)
	}
	o, err := d.Seek(5, io.SeekStart)
	t.Logf("dir Seek(5, SeekStart) after Readdirnames = %d, %v (EISDIR: %v)", o, err, errors.Is(err, syscall.EISDIR))
}
