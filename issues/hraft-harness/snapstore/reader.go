package snapstore

import "io"

// Moved here from the lab's examples/inproc (inproc.go at fork 02f88d5, unchanged but for the
// package), which etcd-grove does not import: Open's reader, and ReadAll for the transports that
// read a snapshot into a request.

// Reader: an io.Reader over a byte slice (each call copies up to len(p) bytes; io.EOF at the end)
type Reader struct {
	b   []byte
	off int
}

// NewReader: a Reader over a copy of b
func NewReader(b []byte) *Reader {
	return &Reader{b: copyBytes(b)}
}

func (r *Reader) Read(p []byte) (int, error) {
	if r.off >= len(r.b) {
		return 0, io.EOF
	}
	n := copy(p, r.b[r.off:])
	r.off += n
	return n, nil
}

// Close: nothing to release (a Reader is also an io.ReadCloser)
func (r *Reader) Close() error {
	return nil
}

// ReadAll: every byte of r until io.EOF (read 512 bytes at a time), or r's other error
func ReadAll(r io.Reader) ([]byte, error) {
	var out []byte
	buf := make([]byte, 512)
	for {
		n, err := r.Read(buf)
		out = append(out, buf[:n]...)
		if err == io.EOF {
			return out, nil
		}
		if err != nil {
			return out, err
		}
	}
}

func copyBytes(b []byte) []byte {
	if b == nil {
		return nil
	}
	c := make([]byte, len(b))
	copy(c, b)
	return c
}
