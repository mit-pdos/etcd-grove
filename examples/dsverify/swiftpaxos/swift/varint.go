package swift

import (
	"errors"
	"io"
)

// Verification workaround (no behaviour change): readVarint and readUvarint are Go's
// encoding/binary.ReadVarint and ReadUvarint (go1.27, encoding/binary/varint.go), copied so that
// Goose translates their bodies (Perennial's encoding/binary gives them names only). The callers
// in this package's marshaling only test the error for nil, so the distinct overflow error value
// is not observable.

const maxVarintLen64 = 10

var errVarintOverflow = errors.New("binary: varint overflows a 64-bit integer")

func readUvarint(r io.ByteReader) (uint64, error) {
	var x uint64
	var s uint
	for i := 0; i < maxVarintLen64; i++ {
		b, err := r.ReadByte()
		if err != nil {
			if i > 0 && err == io.EOF {
				err = io.ErrUnexpectedEOF
			}
			return x, err
		}
		if b < 0x80 {
			if i == maxVarintLen64-1 && b > 1 {
				return x, errVarintOverflow
			}
			return x | uint64(b)<<s, nil
		}
		x |= uint64(b&0x7f) << s
		s += 7
	}
	return x, errVarintOverflow
}

func readVarint(r io.ByteReader) (int64, error) {
	ux, err := readUvarint(r) // ok to continue in presence of error
	x := int64(ux >> 1)
	if ux&1 != 0 {
		x = ^x
	}
	return x, err
}

// Verification workaround (no behaviour change): putUvarint and putVarint are Go's
// encoding/binary.PutUvarint and PutVarint (go1.27, encoding/binary/varint.go), copied verbatim
// so that Goose translates their bodies (Perennial's encoding/binary gives them names only).

func putUvarint(buf []byte, x uint64) int {
	i := 0
	for x >= 0x80 {
		buf[i] = byte(x) | 0x80
		x >>= 7
		i++
	}
	buf[i] = byte(x)
	return i + 1
}

func putVarint(buf []byte, x int64) int {
	ux := uint64(x) << 1
	if x < 0 {
		ux = ^ux
	}
	return putUvarint(buf, ux)
}
