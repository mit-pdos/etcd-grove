// Package pbcodec holds the protobuf wire format that a generated protobuf codec uses (pbgen.py,
// in the repository that keeps this module: per message type, plain marshal and unmarshal code in
// place of protobuf-go's reflection, which a model of google.golang.org/protobuf calls): varints,
// tags, length-delimited values,
// fixed-width values, skipping a field of any wire type, and UTF-8 validation.
//
// The trusted claim: each function is the real module's (google.golang.org/protobuf v1.36.12):
// the Append functions write protowire's bytes; the Consume functions accept exactly the inputs
// protowire's do, consume as many bytes and return the same values; ConsumeFieldTag is the real
// Unmarshal's tag check (internal/impl, which is stricter than protowire's ConsumeTag on the field
// number); SkipField is protowire's ConsumeFieldValue (with its group nesting limit); ValidUTF8
// is Go's unicode/utf8.Valid. Errors are reported as ok = false (only error-or-not is modeled, not
// protowire's error codes). Tested against protowire and unicode/utf8 by pbcodec_test.go and
// protowire_test.go, and, through the generated codecs, against the real proto.Marshal and
// proto.Unmarshal by each generated codec's test (pb_gen_test.go).
package pbcodec

// Stuck is the model's not-modelled point (MODEL: not in protobuf-go; models/README.md, "Not modelled:
// stuck"): where the model does not model protobuf-go's behavior it calls Stuck (after a comment
// `MODEL: not modelled (stuck): ...`), which has no behavior. Its Lean model is Perennial's
// internal/gomodel.Stuck, `Panic "not modelled"`: a stuck panic, which no recover catches and no
// WP rule steps, so a proof of the program shows that it never gets here. Not a value panic, which
// a program could recover and so observe a behavior protobuf-go does not have; not a bare `select {}`,
// whose WP has the precondition True and so would prove anything after it. Its Go body blocks
// forever, which the tests detect (models/internal/stuck).
//
// For the codecs pbgen.py generates in codec mode (their not-modelled points: a value of a type the
// codec was not generated for), which call it. Lean: Net/Code/models_lab/pbcodec.toml (trusted),
// Net/TrustedCode/models_lab/pbcodec.lean.
func Stuck() {
	select {}
}

// Wire types (protowire.Type).
const (
	VarintType     uint64 = 0
	Fixed64Type    uint64 = 1
	BytesType      uint64 = 2
	StartGroupType uint64 = 3
	EndGroupType   uint64 = 4
	Fixed32Type    uint64 = 5
)

// MaxValidNumber is the largest field number a message's field may have (protowire's).
const MaxValidNumber uint64 = 1<<29 - 1

// maxTagNumber is the largest field number protowire's ConsumeTag accepts (math.MaxInt32: it
// allows MessageSet's larger numbers; only a skipped group's fields get this far).
const maxTagNumber uint64 = 1<<31 - 1

// DefaultRecursionLimit is protowire's and proto.Unmarshal's nesting limit.
const DefaultRecursionLimit uint64 = 10000

// Error is the codec's error (only error-or-not is modeled).
type Error struct {
	Msg string
}

func (e *Error) Error() string {
	return "proto: " + e.Msg
}

// SizeVarint returns the number of bytes AppendVarint writes for v.
func SizeVarint(v uint64) uint64 {
	n := uint64(1)
	x := v
	for x >= 0x80 {
		x = x >> 7
		n++
	}
	return n
}

// AppendVarint appends v as a base-128 varint (protowire.AppendVarint).
func AppendVarint(b []byte, v uint64) []byte {
	out := b
	x := v
	for x >= 0x80 {
		out = append(out, byte(x&0x7f)|0x80)
		x = x >> 7
	}
	return append(out, byte(x))
}

// AppendTag appends the tag of field num with wire type typ (protowire.AppendTag).
func AppendTag(b []byte, num uint64, typ uint64) []byte {
	return AppendVarint(b, num<<3|typ&7)
}

// AppendBytes appends v length-delimited (protowire.AppendBytes).
func AppendBytes(b []byte, v []byte) []byte {
	b1 := AppendVarint(b, uint64(len(v)))
	return append(b1, v...)
}

// AppendString appends s length-delimited (protowire.AppendString).
func AppendString(b []byte, s string) []byte {
	b1 := AppendVarint(b, uint64(len(s)))
	return append(b1, s...)
}

// AppendFixed32 appends v little-endian in 4 bytes (protowire.AppendFixed32).
func AppendFixed32(b []byte, v uint32) []byte {
	return append(b, byte(v), byte(v>>8), byte(v>>16), byte(v>>24))
}

// AppendFixed64 appends v little-endian in 8 bytes (protowire.AppendFixed64).
func AppendFixed64(b []byte, v uint64) []byte {
	return append(b, byte(v), byte(v>>8), byte(v>>16), byte(v>>24),
		byte(v>>32), byte(v>>40), byte(v>>48), byte(v>>56))
}

// EncodeZigZag encodes a signed integer as sint64's unsigned value (protowire.EncodeZigZag).
func EncodeZigZag(v int64) uint64 {
	return uint64(v<<1) ^ uint64(v>>63)
}

// DecodeZigZag decodes sint64's unsigned value (protowire.DecodeZigZag).
func DecodeZigZag(x uint64) int64 {
	return int64(x>>1) ^ int64(x)<<63>>63
}

// EncodeBool is a bool's varint value (protowire.EncodeBool).
func EncodeBool(v bool) uint64 {
	if v {
		return 1
	}
	return 0
}

// CopyBytes returns a copy of v, never nil (the real Unmarshal's value for an element of a
// repeated bytes field).
func CopyBytes(v []byte) []byte {
	out := make([]byte, 0, len(v))
	return append(out, v...)
}

// CopyBytesOrNil returns a copy of v, nil if v is empty (the real Unmarshal's value for a proto3
// bytes field, which has no presence).
func CopyBytesOrNil(v []byte) []byte {
	if len(v) == 0 {
		return nil
	}
	return CopyBytes(v)
}

// DecodeZigZag32 decodes a sint32 field's varint value as the real Unmarshal does (its low 32
// bits, zigzag-decoded).
func DecodeZigZag32(x uint64) int32 {
	return int32(DecodeZigZag(x & 0xffffffff))
}

// ConsumeVarint parses a varint at the start of b: its value and length, or ok = false if b
// ends before the varint does or the varint has more than 10 bytes or overflows 64 bits (the
// 10th byte above 1), as protowire.ConsumeVarint.
func ConsumeVarint(b []byte) (uint64, uint64, bool) {
	var v uint64
	i := uint64(0)
	for i < 10 {
		if i >= uint64(len(b)) {
			return 0, 0, false
		}
		y := uint64(b[i])
		if i == 9 && y > 1 {
			return 0, 0, false
		}
		v = v | (y&0x7f)<<(7*i)
		if y < 0x80 {
			return v, i + 1, true
		}
		i++
	}
	return 0, 0, false
}

// ConsumeTag parses a tag at the start of b: field number, wire type and length, or ok =
// false if the varint is malformed or the field number is 0 or above 2^31-1, as
// protowire.ConsumeTag.
func ConsumeTag(b []byte) (uint64, uint64, uint64, bool) {
	v, n, ok := ConsumeVarint(b)
	if !ok {
		return 0, 0, 0, false
	}
	num := v >> 3
	if num < 1 || num > maxTagNumber {
		return 0, 0, 0, false
	}
	return num, v & 7, n, true
}

// ConsumeFieldTag parses the tag of a message's field at the start of b, as the real
// Unmarshal does (internal/impl's unmarshalPointer): field number, wire type and length, or ok =
// false if the varint is malformed or the field number is 0 or above MaxValidNumber.
func ConsumeFieldTag(b []byte) (uint64, uint64, uint64, bool) {
	v, n, ok := ConsumeVarint(b)
	if !ok {
		return 0, 0, 0, false
	}
	num := v >> 3
	if num < 1 || num > MaxValidNumber {
		return 0, 0, 0, false
	}
	return num, v & 7, n, true
}

// ConsumeBytes parses a length-delimited value at the start of b: its contents (a subslice of
// b) and total length, or ok = false (protowire.ConsumeBytes).
func ConsumeBytes(b []byte) ([]byte, uint64, bool) {
	m, n, ok := ConsumeVarint(b)
	if !ok {
		return nil, 0, false
	}
	rest := uint64(len(b)) - n
	if m > rest {
		return nil, 0, false
	}
	return b[n : n+m], n + m, true
}

// ConsumeFixed32 parses a little-endian 4-byte value (protowire.ConsumeFixed32).
func ConsumeFixed32(b []byte) (uint32, uint64, bool) {
	if len(b) < 4 {
		return 0, 0, false
	}
	v := uint32(b[0]) | uint32(b[1])<<8 | uint32(b[2])<<16 | uint32(b[3])<<24
	return v, 4, true
}

// ConsumeFixed64 parses a little-endian 8-byte value (protowire.ConsumeFixed64).
func ConsumeFixed64(b []byte) (uint64, uint64, bool) {
	if len(b) < 8 {
		return 0, 0, false
	}
	v := uint64(b[0]) | uint64(b[1])<<8 | uint64(b[2])<<16 | uint64(b[3])<<24 |
		uint64(b[4])<<32 | uint64(b[5])<<40 | uint64(b[6])<<48 | uint64(b[7])<<56
	return v, 8, true
}

// skipScalar returns the length of the value of wire type typ (not a group) at the start of b,
// or ok = false (a malformed value; an end-group or reserved wire type).
func skipScalar(typ uint64, b []byte) (uint64, bool) {
	if typ == VarintType {
		_, n, ok := ConsumeVarint(b)
		return n, ok
	}
	if typ == Fixed32Type {
		_, n, ok := ConsumeFixed32(b)
		return n, ok
	}
	if typ == Fixed64Type {
		_, n, ok := ConsumeFixed64(b)
		return n, ok
	}
	if typ == BytesType {
		_, n, ok := ConsumeBytes(b)
		return n, ok
	}
	return 0, false
}

// SkipField returns the length of the value of field num with wire type typ at the start of b
// (the bytes after its tag), or ok = false, as protowire.ConsumeFieldValue: a group's fields
// are skipped up to its matching end-group tag (field numbers as ConsumeTag accepts them), with
// at most DefaultRecursionLimit groups nested inside the outermost; an end-group tag that does
// not match, an end-group or reserved (6, 7) wire type, or malformed input is an error.
func SkipField(num uint64, typ uint64, b []byte) (uint64, bool) {
	if typ != StartGroupType {
		return skipScalar(typ, b)
	}
	// open: the field numbers of the groups not yet ended, outermost first
	open := []uint64{num}
	i := uint64(0)
	for {
		num2, typ2, n, ok := ConsumeTag(b[i:])
		if !ok {
			return 0, false
		}
		i = i + n
		if typ2 == EndGroupType {
			last := uint64(len(open)) - 1
			if open[last] != num2 {
				return 0, false
			}
			open = open[:last]
			if len(open) == 0 {
				return i, true
			}
			continue
		}
		if typ2 == StartGroupType {
			if uint64(len(open)) > DefaultRecursionLimit {
				return 0, false
			}
			open = append(open, num2)
			continue
		}
		m, ok2 := skipScalar(typ2, b[i:])
		if !ok2 {
			return 0, false
		}
		i = i + m
	}
}

// cont reports whether c is a UTF-8 continuation byte (0x80..0xbf).
func cont(c byte) bool {
	return 0x80 <= c && c <= 0xbf
}

// ValidUTF8 reports whether b is valid UTF-8, as Go's unicode/utf8.Valid: no overlong
// encodings, no surrogates (U+D800..U+DFFF), nothing above U+10FFFF, nothing cut short.
func ValidUTF8(b []byte) bool {
	n := uint64(len(b))
	i := uint64(0)
	for i < n {
		c := b[i]
		if c < 0x80 {
			i++
			continue
		}
		if c < 0xc2 || c > 0xf4 {
			return false
		}
		if c < 0xe0 {
			if i+1 >= n || !cont(b[i+1]) {
				return false
			}
			i = i + 2
			continue
		}
		// the second byte's range
		lo := byte(0x80)
		hi := byte(0xbf)
		if c == 0xe0 {
			lo = 0xa0
		}
		if c == 0xed {
			hi = 0x9f
		}
		if c == 0xf0 {
			lo = 0x90
		}
		if c == 0xf4 {
			hi = 0x8f
		}
		if i+1 >= n || b[i+1] < lo || b[i+1] > hi {
			return false
		}
		if c < 0xf0 {
			if i+2 >= n || !cont(b[i+2]) {
				return false
			}
			i = i + 3
			continue
		}
		if i+3 >= n || !cont(b[i+2]) || !cont(b[i+3]) {
			return false
		}
		i = i + 4
	}
	return true
}

// ValidString reports whether s is valid UTF-8 (unicode/utf8.ValidString).
func ValidString(s string) bool {
	return ValidUTF8([]byte(s))
}
