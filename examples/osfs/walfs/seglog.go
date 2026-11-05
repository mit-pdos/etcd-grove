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
	// Preallocate(f, lenf, true): fallocate(0, 0, lenf) extends the file back
	// (Preallocate returns at once for 0 bytes).
	if lenf > 0 {
		if err := unix.Fallocate(int(f.Fd()), 0, 0, lenf); err != nil {
			return err
		}
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
	if err := readFull(f, buf); err != nil {
		return nil, err
	}
	return buf, nil
}

// readFull fills buf by Reads at the file offset, as io.ReadFull does, returning
// the first error (io.ReadFull's io.ErrUnexpectedEOF for a short file is an error
// too, here the Read's own).
func readFull(f *os.File, buf []byte) error {
	n := 0
	for n < len(buf) {
		m, err := f.Read(buf[n:])
		if err != nil {
			return err
		}
		n += m
	}
	return nil
}

// Run is seglog's boot program over the directory dir: it removes a leftover
// segment dir/seg.log, appends the data to a new one (Segment), zeroes it past
// the data (ZeroToEnd, from the offset Segment returned) and reads the data back
// (Reread). Every call it makes is one the extension's trusted models cover
// (their panics never fire, however often the node crashes:
// Proof/github_com/mit_pdos/etcd_grove/examples/osfs/walfs/SegLog*.lean).
func Run(dir string) {
	path := dir + "/seg.log"
	names, ok := readNames(dir)
	if !ok {
		return
	}
	for _, n := range names {
		if n == "seg.log" {
			if err := os.Remove(path); err != nil {
				return
			}
		}
	}
	end, err := Segment(path, newData())
	if err != nil {
		return
	}
	f, err := os.OpenFile(path, os.O_RDWR|os.O_CREATE, 0o600)
	if err != nil {
		return
	}
	if _, err := f.Seek(end, io.SeekStart); err != nil {
		f.Close()
		return
	}
	if err := ZeroToEnd(f); err != nil {
		f.Close()
		return
	}
	f.Close()
	Reread(path, int(end))
}
