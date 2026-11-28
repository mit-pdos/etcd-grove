package disk

import "errors"

// The files' encoding: unsigned integers as 8 bytes, little-endian; byte strings length-prefixed;
// lists count-prefixed (the fork's encoding.go's, which raft does not export). A decoder returns
// ErrCorrupt on input it did not write.

// ErrCorrupt is a decoder's error on input it cannot decode.
var ErrCorrupt = errors.New("disk: corrupt file")

func putUint64(b []byte, x uint64) []byte {
	for i := uint64(0); i < 8; i++ {
		b = append(b, byte(x>>(8*i)))
	}
	return b
}

func putBytes(b []byte, s []byte) []byte {
	return append(putUint64(b, uint64(len(s))), s...)
}

// reader is a decoder's position in its input; err is set by the first read past the end.
type reader struct {
	b   []byte
	err bool
}

func (r *reader) uint64() uint64 {
	if r.err || len(r.b) < 8 {
		r.err = true
		return 0
	}
	var x uint64
	for i := uint64(0); i < 8; i++ {
		x |= uint64(r.b[i]) << (8 * i)
	}
	r.b = r.b[8:]
	return x
}

func (r *reader) bytes() []byte {
	n := r.uint64()
	if r.err || uint64(len(r.b)) < n {
		r.err = true
		return nil
	}
	out := make([]byte, n)
	copy(out, r.b[:n])
	r.b = r.b[n:]
	return out
}

// done is nil if every read was in bounds and the input is consumed.
func (r *reader) done() error {
	if r.err || len(r.b) != 0 {
		return ErrCorrupt
	}
	return nil
}
