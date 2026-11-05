package walfs

import (
	"io"
	"os"
	"syscall"

	"golang.org/x/sys/unix"
)

// seglog.go: the calls a WAL segment's life makes on its file, in the order the
// WAL makes them (file_pipeline.go's alloc: LockFile, Seek(0, io.SeekEnd),
// Preallocate; the encoder's Write through ioutil.PageWriter; Fdatasync in
// sync(); ZeroToEnd and Truncate in Open/ReadAll's repair of the tail):
//
//   - an OFD write lock (fileutil.LockFile's F_OFD_SETLKW, here the
//     non-blocking F_OFD_SETLK of TryLockFile);
//   - Seek(0, io.SeekEnd) and Seek(0, io.SeekCurrent);
//   - Write at the file offset;
//   - fallocate keeping the size (Preallocate(f, n, false)) and extending it
//     (Preallocate(f, n, true));
//   - Fdatasync;
//   - Truncate at the offset, and ZeroToEnd's "truncate, then fallocate back".
//
// No property is claimed of it: it pins down the calls the extension's
// trusted models must cover (notes/walfs-ext-plan.md, "Calls").

// segSize is the preallocated size of a segment (SegmentSizeBytes, scaled down).
const segSize = 64 * 1024

// lockFile takes an OFD write lock on the whole file without waiting.
func lockFile(f *os.File) error {
	lk := unix.Flock_t{Type: syscall.F_WRLCK, Whence: io.SeekStart, Start: 0, Len: 0}
	return unix.FcntlFlock(f.Fd(), unix.F_OFD_SETLK, &lk)
}

// Segment appends rec to the segment at path, preallocated to segSize, makes it
// durable, and returns the offset past it.
func Segment(path string, rec []byte) (int64, error) {
	f, err := os.OpenFile(path, os.O_RDWR|os.O_CREATE, 0o600)
	if err != nil {
		return 0, err
	}
	defer f.Close()
	if err := lockFile(f); err != nil {
		return 0, err
	}
	end, err := f.Seek(0, io.SeekEnd)
	if err != nil {
		return 0, err
	}
	if end == 0 {
		// Preallocate(f, segSize, true): the size becomes segSize.
		if err := unix.Fallocate(int(f.Fd()), 0, 0, segSize); err != nil {
			return 0, err
		}
		if _, err := f.Seek(0, io.SeekStart); err != nil {
			return 0, err
		}
	}
	if _, err := f.Write(rec); err != nil {
		return 0, err
	}
	// Preallocate(f, segSize, false): the blocks, not the size.
	if err := unix.Fallocate(int(f.Fd()), unix.FALLOC_FL_KEEP_SIZE, 0, segSize); err != nil {
		return 0, err
	}
	if err := syscall.Fdatasync(int(f.Fd())); err != nil {
		return 0, err
	}
	return f.Seek(0, io.SeekCurrent)
}

// ZeroToEnd zeroes the file from the offset on, keeping its size and the
// offset (fileutil.ZeroToEnd).
func ZeroToEnd(f *os.File) error {
	off, err := f.Seek(0, io.SeekCurrent)
	if err != nil {
		return err
	}
	lenf, err := f.Seek(0, io.SeekEnd)
	if err != nil {
		return err
	}
	if err := f.Truncate(off); err != nil {
		return err
	}
	// Preallocate(f, lenf, true): fallocate(0, 0, lenf) extends the file back.
	if err := unix.Fallocate(int(f.Fd()), 0, 0, lenf); err != nil {
		return err
	}
	_, err = f.Seek(off, io.SeekStart)
	return err
}

// Reread reads the segment at path sequentially from the start, n bytes.
func Reread(path string, n int) ([]byte, error) {
	f, err := os.OpenFile(path, os.O_RDONLY, 0)
	if err != nil {
		return nil, err
	}
	defer f.Close()
	buf := make([]byte, n)
	if _, err := io.ReadFull(f, buf); err != nil {
		return nil, err
	}
	return buf, nil
}
