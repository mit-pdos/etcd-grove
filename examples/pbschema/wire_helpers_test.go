package pbschema

// The wire-format helpers of the D1/D2/P2 tests (d1post_test.go): the Go copy of the Lean
// unknown-field predicate and the input generators.
//
//   - schemas: the five raftpb message types the instances reach (Message, Entry, Snapshot,
//     SnapshotMetadata, ConfState), field number -> kind; takes(schema, num, wt) is the wire types
//     protobuf-go's decoder takes for a declared field (the table TestSchemas checks against the
//     descriptors and the Lean pbSchemaOf).
//   - ufPred / valueLen: the Go copy of `ufWire` / `WVal`
//     (Spec/google_golang_org/protobuf/proto/UnmarshalPb.lean): outer tags minimal, outer numbers
//     1..2^29-1, an outer (number, wire type) never one the decoder takes, groups well formed with
//     matching ends, nesting at most maxGroupDepth, inner numbers 1..2^31-1 (inner tags of any
//     length).
//   - encodeWithUF / genUF: valid encodings with unknown fields at every level (adversarial with
//     ufOpts: non-minimal tags, bad numbers and wire types, mismatched ends); genAdv: adversarial,
//     often invalid, encodings (wrong wire types, packed ConfState lists, Responses, non-minimal
//     tags); packedConfStateMsg: the size bound's extreme family; deepGroup: nested groups.
//
// Copied from the c9 entry-size harness (per-type models, stage A), which ran them in package
// raft of the raft fork.

import (
	"fmt"
	"math"
	"math/rand"

	"google.golang.org/protobuf/encoding/protowire"
	"google.golang.org/protobuf/proto"
	"google.golang.org/protobuf/reflect/protoreflect"
)

// appendVarintPad encodes v with pad extra (non-minimal) bytes; total <= 10.
func appendVarintPad(b []byte, v uint64, pad int) []byte {
	m := protowire.AppendVarint(nil, v)
	if len(m)+pad > 10 {
		pad = 10 - len(m)
	}
	if pad <= 0 {
		return append(b, m...)
	}
	m[len(m)-1] |= 0x80
	for i := 0; i < pad-1; i++ {
		m = append(m, 0x80)
	}
	m = append(m, 0x00)
	return append(b, m...)
}

func tagPad(b []byte, num int, wt protowire.Type, pad int) []byte {
	return appendVarintPad(b, uint64(num)<<3|uint64(wt), pad)
}

type fkind int

const (
	kU64 fkind = iota
	kEnum
	kBool
	kBytes
	kMsg
	kRepU64
	kRepMsg
)

type fdesc struct {
	k   fkind
	sub string
}

var schemas = map[string]map[int]fdesc{
	"Message": {1: {k: kEnum}, 2: {k: kU64}, 3: {k: kU64}, 4: {k: kU64}, 5: {k: kU64}, 6: {k: kU64},
		7: {k: kRepMsg, sub: "Entry"}, 8: {k: kU64}, 9: {k: kMsg, sub: "Snapshot"}, 10: {k: kBool},
		11: {k: kU64}, 12: {k: kBytes}, 13: {k: kU64}, 14: {k: kRepMsg, sub: "Message"}},
	"Entry":            {1: {k: kEnum}, 2: {k: kU64}, 3: {k: kU64}, 4: {k: kBytes}},
	"Snapshot":         {1: {k: kBytes}, 2: {k: kMsg, sub: "SnapshotMetadata"}},
	"SnapshotMetadata": {1: {k: kMsg, sub: "ConfState"}, 2: {k: kU64}, 3: {k: kU64}},
	"ConfState":        {1: {k: kRepU64}, 2: {k: kRepU64}, 3: {k: kRepU64}, 4: {k: kRepU64}, 5: {k: kBool}},
}

func rpad(r *rand.Rand) int {
	if r.Intn(3) == 0 {
		return r.Intn(10)
	}
	return 0
}

func rval(r *rand.Rand) uint64 {
	switch r.Intn(6) {
	case 0:
		return 0
	case 1:
		return uint64(r.Intn(128))
	case 2:
		return uint64(r.Intn(1 << 14))
	case 3:
		return r.Uint64()
	case 4:
		return math.MaxUint64
	default:
		return uint64(r.Intn(30))
	}
}

func rwt(r *rand.Rand) protowire.Type {
	return []protowire.Type{0, 1, 2, 5, 3}[r.Intn(5)]
}

// genUnknown: one well-formed field of any number/wire type (value raw).
// minimalTag controls the outer tag only; inner group content is arbitrary.
func genUnknownField(r *rand.Rand, num int, wt protowire.Type, depth int, minimalTag bool) []byte {
	pad := 0
	if !minimalTag {
		pad = rpad(r)
	}
	var b []byte
	b = tagPad(b, num, wt, pad)
	switch wt {
	case 0:
		b = appendVarintPad(b, rval(r), rpad(r))
	case 1:
		b = protowire.AppendFixed64(b, r.Uint64())
	case 5:
		b = protowire.AppendFixed32(b, r.Uint32())
	case 2:
		n := r.Intn(12)
		b = appendVarintPad(b, uint64(n), rpad(r))
		for i := 0; i < n; i++ {
			b = append(b, byte(r.Intn(256)))
		}
	case 3:
		if depth < 3 {
			k := r.Intn(4)
			for i := 0; i < k; i++ {
				b = append(b, genUnknownField(r, 1+r.Intn(40), rwt(r), depth+1, false)...)
			}
		}
		b = tagPad(b, num, 4, rpad(r)) // the end group tag, possibly non-minimal
	}
	return b
}

func undeclared(r *rand.Rand, schema map[int]fdesc) int {
	for {
		var n int
		switch r.Intn(3) {
		case 0:
			n = 1 + r.Intn(40)
		case 1:
			n = 1 + r.Intn(1<<20)
		default:
			n = (1 << 29) - 1 - r.Intn(5)
		}
		if n >= 19000 && n <= 19999 {
			continue // the reserved range: skipped
		}
		if _, ok := schema[n]; !ok {
			return n
		}
	}
}

// genAdv generates an adversarial (possibly invalid) encoding of message kind.
func genAdv(r *rand.Rand, kind string, depth int) []byte {
	schema := schemas[kind]
	var b []byte
	n := r.Intn(7)
	for i := 0; i < n; i++ {
		if r.Intn(4) == 0 {
			b = append(b, genUnknownField(r, undeclared(r, schema), rwt(r), 0, r.Intn(2) == 0)...)
			continue
		}
		// a known field
		num := 1 + r.Intn(len(schema))
		fd := schema[num]
		if r.Intn(10) == 0 { // wrong wire type
			b = append(b, genUnknownField(r, num, rwt(r), 0, r.Intn(2) == 0)...)
			continue
		}
		switch fd.k {
		case kU64, kEnum, kBool:
			b = tagPad(b, num, 0, rpad(r))
			v := rval(r)
			if fd.k == kEnum && r.Intn(2) == 0 {
				v = uint64(r.Intn(25))
			}
			b = appendVarintPad(b, v, rpad(r))
		case kBytes:
			b = append(b, genUnknownField(r, num, 2, 0, r.Intn(2) == 0)...)
		case kRepU64:
			if r.Intn(2) == 0 {
				// packed
				var body []byte
				k := r.Intn(20)
				for j := 0; j < k; j++ {
					v := rval(r)
					if r.Intn(2) == 0 {
						v = 0
					}
					body = appendVarintPad(body, v, rpad(r))
				}
				b = tagPad(b, num, 2, rpad(r))
				b = appendVarintPad(b, uint64(len(body)), rpad(r))
				b = append(b, body...)
			} else {
				b = tagPad(b, num, 0, rpad(r))
				b = appendVarintPad(b, rval(r), rpad(r))
			}
		case kMsg, kRepMsg:
			var sub []byte
			if depth < 4 {
				sub = genAdv(r, fd.sub, depth+1)
			}
			b = tagPad(b, num, 2, rpad(r))
			b = appendVarintPad(b, uint64(len(sub)), rpad(r))
			b = append(b, sub...)
		}
	}
	return b
}

// packedConfStateMsg: Message{snapshot{metadata{conf_state{voters packed k zeros}}}}, optionally
// split across the 4 repeated fields and wrapped in `resp` levels of Responses.
func packedConfStateMsg(k int, fields int, resp int) []byte {
	var cs []byte
	per := k / fields
	for f := 1; f <= fields; f++ {
		body := make([]byte, per)
		cs = protowire.AppendTag(cs, protowire.Number(f), 2)
		cs = protowire.AppendBytes(cs, body)
	}
	md := protowire.AppendTag(nil, 1, 2)
	md = protowire.AppendBytes(md, cs)
	sn := protowire.AppendTag(nil, 2, 2)
	sn = protowire.AppendBytes(sn, md)
	m := protowire.AppendTag(nil, 9, 2)
	m = protowire.AppendBytes(m, sn)
	for i := 0; i < resp; i++ {
		w := protowire.AppendTag(nil, 14, 2)
		m = protowire.AppendBytes(w, m)
	}
	return m
}

// takes reports whether protobuf-go's decoder takes (num, wt) as a known field of schema.
func takes(schema map[int]fdesc, num int, wt protowire.Type) bool {
	fd, ok := schema[num]
	if !ok {
		return false
	}
	switch fd.k {
	case kU64, kEnum, kBool:
		return wt == 0
	case kBytes, kMsg, kRepMsg:
		return wt == 2
	case kRepU64:
		return wt == 0 || wt == 2
	}
	return false
}

const maxGroupDepth = 10001

// innerMax is the largest field number accepted inside an unknown group: protowire.ConsumeTag only
// checks num >= 1, and DecodeTag rejects only x>>3 > MaxInt32 (wire.go:168-178, 525-531).
const innerMax = 1<<31 - 1

// ufPred checks the D1 predicate on one level's unknown bytes. innerLimit is the inner number limit
// being tested; checkTaken adds "the outer (number, wire type) is not taken by schema".
func ufPred(uf []byte, schema map[int]fdesc, innerLimit uint64, checkTaken bool) string {
	b := uf
	for len(b) > 0 {
		v, n := protowire.ConsumeVarint(b)
		if n < 0 {
			return "outer tag: bad varint"
		}
		if n != protowire.SizeVarint(v) {
			return "outer tag not minimal"
		}
		num, wt := v>>3, protowire.Type(v&7)
		if num < 1 || num > uint64(protowire.MaxValidNumber) {
			return fmt.Sprintf("outer number %d out of 1..2^29-1", num)
		}
		if checkTaken && takes(schema, int(num), wt) {
			return fmt.Sprintf("outer (%d,%d) taken by the decoder", num, wt)
		}
		b = b[n:]
		k, why := valueLen(b, num, wt, 1, innerLimit)
		if why != "" {
			return why
		}
		b = b[k:]
	}
	return ""
}

// valueLen parses one field value (after its tag); depth is the group level of a StartGroup value.
func valueLen(b []byte, num uint64, wt protowire.Type, depth int, innerLimit uint64) (int, string) {
	switch wt {
	case protowire.VarintType:
		_, n := protowire.ConsumeVarint(b)
		if n < 0 {
			return 0, "bad varint value"
		}
		return n, ""
	case protowire.Fixed32Type:
		if len(b) < 4 {
			return 0, "short fixed32"
		}
		return 4, ""
	case protowire.Fixed64Type:
		if len(b) < 8 {
			return 0, "short fixed64"
		}
		return 8, ""
	case protowire.BytesType:
		l, n := protowire.ConsumeVarint(b)
		if n < 0 || uint64(len(b)-n) < l {
			return 0, "bad bytes length"
		}
		return n + int(l), ""
	case protowire.StartGroupType:
		if depth > maxGroupDepth {
			return 0, fmt.Sprintf("group depth > %d", maxGroupDepth)
		}
		off := 0
		for {
			v, n := protowire.ConsumeVarint(b[off:])
			if n < 0 {
				return 0, "inner tag: bad varint"
			}
			off += n
			inum, iwt := v>>3, protowire.Type(v&7)
			if inum < 1 || inum > innerLimit {
				return 0, fmt.Sprintf("inner number %d out of range", inum)
			}
			if iwt == protowire.EndGroupType {
				if inum != num {
					return 0, "end group number mismatch"
				}
				return off, ""
			}
			k, why := valueLen(b[off:], inum, iwt, depth+1, innerLimit)
			if why != "" {
				return 0, why
			}
			off += k
		}
	}
	return 0, fmt.Sprintf("wire type %d", wt)
}

type level struct {
	name string
	uf   []byte
}

type ufOpts struct {
	nonMinOuter, badNums, badEnds, takenOK bool
	innerNumMax                            uint64
}

func genGroupBody(r *rand.Rand, num uint64, depth int, o ufOpts) []byte {
	var b []byte
	if depth < 4 {
		for k := r.Intn(4); k > 0; k-- {
			inum := 1 + uint64(r.Int63n(int64(o.innerNumMax)))
			if r.Intn(3) == 0 {
				inum = 1 + uint64(r.Intn(20))
			}
			wt := rwt(r)
			b = appendVarintPad(b, inum<<3|uint64(wt), rpad(r)) // inner tags: any length
			b = append(b, genValue(r, inum, wt, depth+1, o)...)
		}
	}
	end := num
	if o.badEnds && r.Intn(5) == 0 {
		end = num + 1
	}
	return appendVarintPad(b, end<<3|4, rpad(r)) // end tag: any length
}

func genValue(r *rand.Rand, num uint64, wt protowire.Type, depth int, o ufOpts) []byte {
	switch wt {
	case 0:
		return appendVarintPad(nil, rval(r), rpad(r))
	case 1:
		return protowire.AppendFixed64(nil, r.Uint64())
	case 5:
		return protowire.AppendFixed32(nil, r.Uint32())
	case 2:
		n := r.Intn(10)
		b := appendVarintPad(nil, uint64(n), rpad(r))
		return append(b, make([]byte, n)...)
	}
	return genGroupBody(r, num, depth, o)
}

func genUF(r *rand.Rand, schema map[int]fdesc, o ufOpts) []byte {
	var b []byte
	for k := r.Intn(4); k > 0; k-- {
		var num uint64
		var wt protowire.Type
		for {
			switch r.Intn(4) {
			case 0:
				num = uint64(1 + r.Intn(len(schema)+2))
			case 1:
				num = uint64(protowire.MaxValidNumber) - uint64(r.Intn(3))
			default:
				num = uint64(1 + r.Intn(1<<20))
			}
			wt = rwt(r)
			if o.badNums && r.Intn(6) == 0 {
				num = []uint64{0, 1 << 29, 1<<31 - 1}[r.Intn(3)]
			}
			if o.badNums && r.Intn(10) == 0 {
				wt = protowire.Type([]int{4, 6, 7}[r.Intn(3)])
			}
			if o.takenOK || num > 1<<28 || !takes(schema, int(num), wt) {
				break
			}
		}
		pad := 0
		if o.nonMinOuter && r.Intn(3) == 0 {
			pad = 1 + r.Intn(4)
		}
		b = appendVarintPad(b, num<<3|uint64(wt), pad)
		if wt == 4 || wt == 6 || wt == 7 {
			continue
		}
		b = append(b, genValue(r, num, wt, 1, o)...)
	}
	return b
}

// encodeWithUF: a random valid encoding of kind with uf chunks interleaved between known fields.
func encodeWithUF(r *rand.Rand, kind string, depth int, o ufOpts) []byte {
	schema := schemas[kind]
	var b []byte
	for k := r.Intn(5); k > 0; k-- {
		if r.Intn(2) == 0 {
			b = append(b, genUF(r, schema, o)...)
			continue
		}
		num := 1 + r.Intn(len(schema))
		fd := schema[num]
		switch fd.k {
		case kU64, kEnum, kBool:
			b = protowire.AppendTag(b, protowire.Number(num), 0)
			b = protowire.AppendVarint(b, rval(r)&0xff)
		case kBytes:
			b = protowire.AppendTag(b, protowire.Number(num), 2)
			b = protowire.AppendBytes(b, make([]byte, r.Intn(8)))
		case kRepU64:
			b = protowire.AppendTag(b, protowire.Number(num), 0)
			b = protowire.AppendVarint(b, rval(r))
		case kMsg, kRepMsg:
			if fd.sub == "Message" || depth > 3 {
				continue
			}
			b = protowire.AppendTag(b, protowire.Number(num), 2)
			b = protowire.AppendBytes(b, encodeWithUF(r, fd.sub, depth+1, o))
		}
	}
	return b
}

func deepGroup(num uint64, d int, nonMinInner bool) []byte {
	var b []byte
	b = protowire.AppendVarint(b, num<<3|3) // outer: minimal
	for i := 1; i < d; i++ {
		pad := 0
		if nonMinInner {
			pad = 2
		}
		b = appendVarintPad(b, num<<3|3, pad)
	}
	for i := 0; i < d; i++ {
		pad := 0
		if nonMinInner {
			pad = 3
		}
		b = appendVarintPad(b, num<<3|4, pad)
	}
	return b
}

func setUF(m proto.Message, uf []byte) {
	m.ProtoReflect().SetUnknown(protoreflect.RawFields(uf))
}
