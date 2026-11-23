package epaxos

import (
	"errors"
	"io"
)

// putVarint and readVarint are encoding/binary's PutVarint and ReadVarint (with PutUvarint and
// ReadUvarint), copied from Go 1.27.1's src/encoding/binary/varint.go, so that the verification
// has their code: Perennial's model of encoding/binary has them as names only (no semantics).
// Behavior is Go's, byte for byte; the only difference is the identity of the overflow error
// (errVarintOverflow, with binary's errOverflow's message), which no caller compares.

// maxVarintLen64 is binary.MaxVarintLen64.
const maxVarintLen64 = 10

// errVarintOverflow is binary's errOverflow.
var errVarintOverflow = errors.New("binary: varint overflows a 64-bit integer")

// putUvarint is binary.PutUvarint.
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

// putVarint is binary.PutVarint.
func putVarint(buf []byte, x int64) int {
	ux := uint64(x) << 1
	if x < 0 {
		ux = ^ux
	}
	return putUvarint(buf, ux)
}

// readUvarint is binary.ReadUvarint.
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

// readVarint is binary.ReadVarint.
func readVarint(r io.ByteReader) (int64, error) {
	ux, err := readUvarint(r) // ok to continue in presence of error
	x := int64(ux >> 1)
	if ux&1 != 0 {
		x = ^x
	}
	return x, err
}
