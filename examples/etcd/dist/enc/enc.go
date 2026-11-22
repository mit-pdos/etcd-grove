// Package enc is the byte encoding of the values the etcd-dist workloads send between machines
// through examples/lib/remote (txnlin's inputs and outputs, the writers' and principals' reports):
// unsigned and signed integers as 8 bytes, little-endian; a bool as one byte, 0 or 1; a string as
// its length, then its bytes. A decoder fails (Ok false) on bytes that are not an encoding: too
// short, a bool byte other than 0 and 1, or bytes left at the end (Done). Every encoding decodes to
// the value encoded (the round-trip tests).
package enc

// Enc builds an encoding.
type Enc struct {
	B []byte
}

// U64 appends x.
func (e *Enc) U64(x uint64) {
	for i := uint64(0); i < 8; i++ {
		e.B = append(e.B, byte(x>>(8*i)))
	}
}

// I64 appends x (as its two's complement).
func (e *Enc) I64(x int64) {
	e.U64(uint64(x))
}

// Int appends x (as an int64).
func (e *Enc) Int(x int) {
	e.U64(uint64(int64(x)))
}

// Bool appends x as one byte.
func (e *Enc) Bool(x bool) {
	if x {
		e.B = append(e.B, 1)
	} else {
		e.B = append(e.B, 0)
	}
}

// Str appends s: its length, then its bytes.
func (e *Enc) Str(s string) {
	e.U64(uint64(len(s)))
	e.B = append(e.B, []byte(s)...)
}

// Dec reads an encoding: B is what is left, Ok whether every read so far succeeded (a failed read
// returns a zero value and leaves Ok false).
type Dec struct {
	B  []byte
	Ok bool
}

// NewDec is a decoder of b.
func NewDec(b []byte) *Dec {
	return &Dec{B: b, Ok: true}
}

// U64 reads an unsigned integer.
func (d *Dec) U64() uint64 {
	if uint64(len(d.B)) < 8 {
		d.Ok = false
		return 0
	}
	x := uint64(0)
	for i := uint64(0); i < 8; i++ {
		x = x | (uint64(d.B[i]) << (8 * i))
	}
	d.B = d.B[8:]
	return x
}

// I64 reads a signed integer.
func (d *Dec) I64() int64 {
	return int64(d.U64())
}

// Int reads an int (an int64).
func (d *Dec) Int() int {
	return int(int64(d.U64()))
}

// Bool reads a bool: one byte, 0 or 1.
func (d *Dec) Bool() bool {
	if len(d.B) < 1 || d.B[0] > 1 {
		d.Ok = false
		return false
	}
	x := d.B[0] == 1
	d.B = d.B[1:]
	return x
}

// Str reads a string.
func (d *Dec) Str() string {
	n := d.U64()
	if !d.Ok || uint64(len(d.B)) < n {
		d.Ok = false
		return ""
	}
	s := string(d.B[:n])
	d.B = d.B[n:]
	return s
}

// Done reports whether every read succeeded and nothing is left.
func (d *Dec) Done() bool {
	return d.Ok && len(d.B) == 0
}
