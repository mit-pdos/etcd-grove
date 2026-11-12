package pbschema

// out_size C3, B2 (the Freeze package /shared/tmp/out-size/freeze-b2.md): the Go evidence for the
// per-type instances of raftpb.ConfChange and raftpb.ConfChangeV2 (Proof/go_etcd_io/raft/v3/
// PbConfChangeType.lean, drafted in the package), tested against protobuf-go (examples/go.mod's pin)
// and the raft fork's raftpb. The Lean statements these tests check, all trusted:
//
//   - ccEncC_ok / cc2EncC_ok, the encoders' facts (TestB2CCEncoder, TestB2CC2Encoder): for a random
//     content (every optional scalar present or not, the enums any int32, Context nil, empty or
//     not, ConfChangeV2's changes each with its own unknown fields, unknown fields satisfying
//     `ufWire` at every level's schema), proto.Marshal's length and proto.Size are the instance's
//     size (ccSizeC / cc2SizeC, transcribing `ccSizeE` / `cc2SizeE`), and Unmarshal of the encoding
//     gives back exactly the content (the `wire` conjunct, the round trip; also against the
//     independent reference decoders below), with the getters' model.
//   - the pure bound (TestB2CCBound, not trusted: proved in Lean, `ccSizeE_le`/`cc2SizeE_le`):
//     the encoding is at most `ccSize cc + 64` bytes (ccMeasure transcribes `ccSize`), on random
//     contents and on the extremes (every scalar present at its widest value, negative enums,
//     long Context, many changes).
//   - the schemas' D1 at the decoder (TestB2CCDecoderUf): what protobuf-go's Unmarshal leaves in
//     the unknown fields of a ConfChange, a ConfChangeV2 and each of its ConfChangeSingles satisfies
//     `ufWire` at the schemas the package adds to `pbSchemaOf` (proposal A1), on random encodings
//     with unknown fields interleaved, mutated, and every input of length at most 2.

import (
	"fmt"
	"math"
	"math/rand"
	"testing"

	"go.etcd.io/etcd/pkg/v3/pbutil"
	"google.golang.org/protobuf/encoding/protowire"
	"google.golang.org/protobuf/proto"

	pb "go.etcd.io/raft/v3/raftpb"
)

func init() {
	schemas["ConfChange"] = map[int]fdesc{1: {k: kU64}, 2: {k: kEnum}, 3: {k: kU64}, 4: {k: kBytes}}
	schemas["ConfChangeSingle"] = map[int]fdesc{1: {k: kEnum}, 2: {k: kU64}}
	schemas["ConfChangeV2"] = map[int]fdesc{1: {k: kEnum}, 2: {k: kRepMsg, sub: "ConfChangeSingle"}, 3: {k: kBytes}}
}

const nEncCC = 100000

type ccC struct {
	typ        *int32
	nodeID, id *uint64
	ctx        *[]byte
	uf         []byte
}

type ccsC struct {
	typ    *int32
	nodeID *uint64
	uf     []byte
}

type cc2C struct {
	trans   *int32
	changes []ccsC
	ctx     *[]byte
	uf      []byte
}

func (c ccC) show() string {
	return fmt.Sprintf("CC{type:%s node:%s id:%s ctx:%s uf:%x}", sI(c.typ), sU(c.nodeID), sU(c.id), sD(c.ctx), c.uf)
}

func (c ccsC) show() string {
	return fmt.Sprintf("{type:%s node:%s uf:%x}", sI(c.typ), sU(c.nodeID), c.uf)
}

func (c cc2C) show() string {
	s := fmt.Sprintf("CC2{trans:%s ctx:%s uf:%x changes:[", sI(c.trans), sD(c.ctx), c.uf)
	for _, ch := range c.changes {
		s += ch.show()
	}
	return s + "]}"
}

func toPbCC(c ccC) *pb.ConfChange {
	m := &pb.ConfChange{NodeId: cpU(c.nodeID), Id: cpU(c.id)}
	if c.typ != nil {
		m.Type = pb.ConfChangeType(*c.typ).Enum()
	}
	if c.ctx != nil {
		m.Context = append([]byte{}, (*c.ctx)...)
	}
	setUF(m, append([]byte(nil), c.uf...))
	return m
}

func toPbCCS(c ccsC) *pb.ConfChangeSingle {
	m := &pb.ConfChangeSingle{NodeId: cpU(c.nodeID)}
	if c.typ != nil {
		m.Type = pb.ConfChangeType(*c.typ).Enum()
	}
	setUF(m, append([]byte(nil), c.uf...))
	return m
}

func toPbCC2(c cc2C) *pb.ConfChangeV2 {
	m := &pb.ConfChangeV2{}
	if c.trans != nil {
		m.Transition = pb.ConfChangeTransition(*c.trans).Enum()
	}
	for _, ch := range c.changes {
		m.Changes = append(m.Changes, toPbCCS(ch))
	}
	if c.ctx != nil {
		m.Context = append([]byte{}, (*c.ctx)...)
	}
	setUF(m, append([]byte(nil), c.uf...))
	return m
}

func contentOfCC(m *pb.ConfChange) ccC {
	c := ccC{nodeID: cpU(m.NodeId), id: cpU(m.Id), ctx: cpD(m.Context), uf: cpUF(m)}
	if m.Type != nil {
		v := int32(*m.Type)
		c.typ = &v
	}
	return c
}

func contentOfCCS(m *pb.ConfChangeSingle) ccsC {
	c := ccsC{nodeID: cpU(m.NodeId), uf: cpUF(m)}
	if m.Type != nil {
		v := int32(*m.Type)
		c.typ = &v
	}
	return c
}

func contentOfCC2(m *pb.ConfChangeV2) cc2C {
	c := cc2C{ctx: cpD(m.Context), uf: cpUF(m)}
	if m.Transition != nil {
		v := int32(*m.Transition)
		c.trans = &v
	}
	for _, ch := range m.Changes {
		c.changes = append(c.changes, contentOfCCS(ch))
	}
	return c
}

// ---------------- the Lean formulas (drafted in freeze-b2.md) ----------------

// ccSizeE: the encoding's exact size.
func ccSizeC(c ccC) int {
	return optVarintSizeU(c.id) + optEnumSize(c.typ) + optVarintSizeU(c.nodeID) + optBytesSize(c.ctx) + len(c.uf)
}

func ccsSizeC(c ccsC) int {
	return optEnumSize(c.typ) + optVarintSizeU(c.nodeID) + len(c.uf)
}

// cc2SizeE: each change a length-delimited field 2 (tag, length, body).
func cc2SizeC(c cc2C) int {
	s := optEnumSize(c.trans) + optBytesSize(c.ctx) + len(c.uf)
	for _, ch := range c.changes {
		s += lenSize(ccsSizeC(ch))
	}
	return s
}

// ccSize (PbContentOwn.lean, raft-entsize §3): the byte content plus 32 per V2 change.
func ccMeasure(c ccC) int {
	n := len(c.uf)
	if c.ctx != nil {
		n += len(*c.ctx)
	}
	return n
}

func cc2Measure(c cc2C) int {
	n := len(c.uf)
	if c.ctx != nil {
		n += len(*c.ctx)
	}
	for _, ch := range c.changes {
		n += len(ch.uf) + 32
	}
	return n
}

// the models (ConfChangeM, ConfChangeV2M: the getters' values).
func ccModel(c ccC) string {
	return fmt.Sprintf("%d/%d/%d/%x", gI(c.typ), gU(c.nodeID), gU(c.id), gD(c.ctx))
}

func ccGetters(m *pb.ConfChange) string {
	return fmt.Sprintf("%d/%d/%d/%x", int32(m.GetType()), m.GetNodeId(), m.GetId(), m.GetContext())
}

func cc2Model(c cc2C) string {
	s := fmt.Sprintf("%d/%x/", gI(c.trans), gD(c.ctx))
	for _, ch := range c.changes {
		s += fmt.Sprintf("(%d,%d)", gI(ch.typ), gU(ch.nodeID))
	}
	return s
}

func cc2Getters(m *pb.ConfChangeV2) string {
	s := fmt.Sprintf("%d/%x/", int32(m.GetTransition()), m.GetContext())
	for _, ch := range m.GetChanges() {
		s += fmt.Sprintf("(%d,%d)", int32(ch.GetType()), ch.GetNodeId())
	}
	return s
}

// ---------------- reference decoders (not protobuf-go's code) ----------------

func refDecodeCC(b []byte, c *ccC) bool {
	for len(b) > 0 {
		num, wt, n, ok := refTag(b)
		if !ok {
			return false
		}
		b = b[n:]
		if !takes(schemas["ConfChange"], int(num), wt) {
			k, ok := refUnknown(&c.uf, b, num, wt)
			if !ok {
				return false
			}
			b = b[k:]
			continue
		}
		if num == 4 {
			v, k, ok := refBytes(b)
			if !ok {
				return false
			}
			c.ctx = pdat(v)
			b = b[k:]
			continue
		}
		v, k, ok := refVarint(b)
		if !ok {
			return false
		}
		switch num {
		case 1:
			c.id = pu(v)
		case 2:
			c.typ = pi32(v)
		case 3:
			c.nodeID = pu(v)
		}
		b = b[k:]
	}
	return true
}

func refDecodeCCS(b []byte, c *ccsC) bool {
	for len(b) > 0 {
		num, wt, n, ok := refTag(b)
		if !ok {
			return false
		}
		b = b[n:]
		if !takes(schemas["ConfChangeSingle"], int(num), wt) {
			k, ok := refUnknown(&c.uf, b, num, wt)
			if !ok {
				return false
			}
			b = b[k:]
			continue
		}
		v, k, ok := refVarint(b)
		if !ok {
			return false
		}
		if num == 1 {
			c.typ = pi32(v)
		} else {
			c.nodeID = pu(v)
		}
		b = b[k:]
	}
	return true
}

func refDecodeCC2(b []byte, c *cc2C) bool {
	for len(b) > 0 {
		num, wt, n, ok := refTag(b)
		if !ok {
			return false
		}
		b = b[n:]
		if !takes(schemas["ConfChangeV2"], int(num), wt) {
			k, ok := refUnknown(&c.uf, b, num, wt)
			if !ok {
				return false
			}
			b = b[k:]
			continue
		}
		switch num {
		case 1:
			v, k, ok := refVarint(b)
			if !ok {
				return false
			}
			c.trans = pi32(v)
			b = b[k:]
		case 2:
			v, k, ok := refBytes(b)
			if !ok {
				return false
			}
			var ch ccsC
			if !refDecodeCCS(v, &ch) {
				return false
			}
			c.changes = append(c.changes, ch)
			b = b[k:]
		case 3:
			v, k, ok := refBytes(b)
			if !ok {
				return false
			}
			c.ctx = pdat(v)
			b = b[k:]
		}
	}
	return true
}

// ---------------- generators ----------------

func randCCC(t *testing.T, r *rand.Rand) ccC {
	return ccC{typ: randOptEnum(r, 4), nodeID: randOptU64(r), id: randOptU64(r), ctx: randOptData(r),
		uf: randValidUF(t, r, "ConfChange")}
}

func randCC2C(t *testing.T, r *rand.Rand) cc2C {
	c := cc2C{trans: randOptEnum(r, 3), ctx: randOptData(r), uf: randValidUF(t, r, "ConfChangeV2")}
	for k := r.Intn(6); k > 0; k-- {
		c.changes = append(c.changes, ccsC{typ: randOptEnum(r, 4), nodeID: randOptU64(r),
			uf: randValidUF(t, r, "ConfChangeSingle")})
	}
	return c
}

// ---------------- the tests ----------------

func TestB2CCEncoder(t *testing.T) {
	r := rand.New(rand.NewSource(41))
	fails := map[string]int{}
	ex := map[string]string{}
	f := func(k string, c ccC) {
		fails[k]++
		if _, ok := ex[k]; !ok {
			ex[k] = c.show()
		}
	}
	for it := 0; it < nEncCC; it++ {
		c := randCCC(t, r)
		m := toPbCC(c)
		enc, err := proto.Marshal(m)
		if err != nil {
			f("marshal error", c)
			continue
		}
		if len(enc) != ccSizeC(c) {
			f(fmt.Sprintf("len(Marshal) != ccSizeE (enc %x)", enc), c)
		}
		if proto.Size(m) != ccSizeC(c) {
			f("proto.Size != ccSizeE", c)
		}
		var d pb.ConfChange
		if proto.Unmarshal(enc, &d) != nil {
			f("Unmarshal(Marshal) fails", c)
			continue
		}
		if contentOfCC(&d).show() != c.show() {
			f("Unmarshal(Marshal) content differs", c)
		}
		if ccGetters(&d) != ccModel(c) {
			f("decoded getters != the content's model", c)
		}
		var rc ccC
		if !refDecodeCC(enc, &rc) || rc.show() != c.show() {
			f("reference decode of Marshal differs", c)
		}
	}
	t.Logf("B2 ConfChange: %d random contents: %d failure kinds", nEncCC, len(fails))
	for k, n := range fails {
		t.Errorf("B2 ConfChange FAIL %s: %d (first: %s)", k, n, ex[k])
	}
}

func TestB2CC2Encoder(t *testing.T) {
	r := rand.New(rand.NewSource(42))
	fails := map[string]int{}
	ex := map[string]string{}
	f := func(k string, c cc2C) {
		fails[k]++
		if _, ok := ex[k]; !ok {
			ex[k] = c.show()
		}
	}
	for it := 0; it < nEncCC; it++ {
		c := randCC2C(t, r)
		m := toPbCC2(c)
		enc, err := proto.Marshal(m)
		if err != nil {
			f("marshal error", c)
			continue
		}
		if len(enc) != cc2SizeC(c) {
			f(fmt.Sprintf("len(Marshal) != cc2SizeE (enc %x)", enc), c)
		}
		if proto.Size(m) != cc2SizeC(c) {
			f("proto.Size != cc2SizeE", c)
		}
		var d pb.ConfChangeV2
		if proto.Unmarshal(enc, &d) != nil {
			f("Unmarshal(Marshal) fails", c)
			continue
		}
		if contentOfCC2(&d).show() != c.show() {
			f("Unmarshal(Marshal) content differs", c)
		}
		if cc2Getters(&d) != cc2Model(c) {
			f("decoded getters != the content's model", c)
		}
		var rc cc2C
		if !refDecodeCC2(enc, &rc) || rc.show() != c.show() {
			f("reference decode of Marshal differs", c)
		}
	}
	t.Logf("B2 ConfChangeV2: %d random contents: %d failure kinds", nEncCC, len(fails))
	for k, n := range fails {
		t.Errorf("B2 ConfChangeV2 FAIL %s: %d (first: %s)", k, n, ex[k])
	}
}

func TestB2CCBound(t *testing.T) {
	r := rand.New(rand.NewSource(43))
	worst1, worst2 := 0, 0
	check1 := func(c ccC) {
		n := proto.Size(toPbCC(c))
		if n > ccMeasure(c)+64 {
			t.Errorf("ConfChange: size %d > ccSize %d + 64: %s", n, ccMeasure(c), c.show())
		}
		if d := n - ccMeasure(c); d > worst1 {
			worst1 = d
		}
	}
	check2 := func(c cc2C) {
		n := proto.Size(toPbCC2(c))
		if n > cc2Measure(c)+64 {
			t.Errorf("ConfChangeV2: size %d > ccSize %d + 64: %s", n, cc2Measure(c), c.show())
		}
		if d := n - cc2Measure(c); d > worst2 {
			worst2 = d
		}
	}
	for it := 0; it < nEncCC; it++ {
		check1(randCCC(t, r))
		check2(randCC2C(t, r))
	}
	neg := int32(math.MinInt32)
	maxU := uint64(math.MaxUint64)
	for _, n := range []int{0, 127, 128, 16383, 16384, 1 << 21} {
		ctx := make([]byte, n)
		check1(ccC{typ: &neg, nodeID: &maxU, id: &maxU, ctx: &ctx})
		c2 := cc2C{trans: &neg, ctx: &ctx}
		for k := 0; k < 50; k++ {
			c2.changes = append(c2.changes, ccsC{typ: &neg, nodeID: &maxU})
		}
		check2(c2)
		// one change with long unknown fields (its length varint widest)
		uf := protowire.AppendTag(nil, 1000, 2)
		uf = protowire.AppendBytes(uf, make([]byte, n))
		check2(cc2C{trans: &neg, ctx: &ctx, changes: []ccsC{{typ: &neg, nodeID: &maxU, uf: uf}}})
	}
	t.Logf("B2 bound: worst size - ccSize: ConfChange %d, ConfChangeV2 %d (bound 64)", worst1, worst2)
}

func TestB2CCDecoderUf(t *testing.T) {
	r := rand.New(rand.NewSource(44))
	bad := 0
	checkCC := func(bs []byte) {
		var d pb.ConfChange
		if proto.Unmarshal(bs, &d) != nil {
			return
		}
		if why := ufPred(cpUF(&d), schemas["ConfChange"], innerMax, true); why != "" {
			bad++
			if bad < 5 {
				t.Errorf("ConfChange decode of %x: uf violates ufWire: %s", trunc(bs), why)
			}
		}
	}
	checkCC2 := func(bs []byte) {
		var d pb.ConfChangeV2
		if proto.Unmarshal(bs, &d) != nil {
			return
		}
		if why := ufPred(cpUF(&d), schemas["ConfChangeV2"], innerMax, true); why != "" {
			bad++
			if bad < 5 {
				t.Errorf("ConfChangeV2 decode of %x: uf violates ufWire: %s", trunc(bs), why)
			}
		}
		for _, ch := range d.Changes {
			if why := ufPred(cpUF(ch), schemas["ConfChangeSingle"], innerMax, true); why != "" {
				bad++
				if bad < 5 {
					t.Errorf("ConfChangeV2 decode of %x: a change's uf violates ufWire: %s", trunc(bs), why)
				}
			}
		}
	}
	o := ufOpts{nonMinOuter: true, takenOK: true, innerNumMax: 1<<31 - 1}
	for it := 0; it < nEncCC; it++ {
		b1 := encodeWithUF(r, "ConfChange", 0, o)
		checkCC(b1)
		checkCC(mutate(r, b1))
		b2 := encodeWithUF(r, "ConfChangeV2", 0, o)
		checkCC2(b2)
		checkCC2(mutate(r, b2))
	}
	for a := 0; a < 256; a++ {
		checkCC([]byte{byte(a)})
		checkCC2([]byte{byte(a)})
		for b := 0; b < 256; b++ {
			checkCC([]byte{byte(a), byte(b)})
			checkCC2([]byte{byte(a), byte(b)})
		}
	}
	t.Logf("B2 decoder: %d random encodings (and mutations, every input of length <= 2) of ConfChange and ConfChangeV2: %d ufWire violations", nEncCC, bad)
}

// --- out_size B2 Revision 1 (A3'): the length bound of proto.MarshalConfChange[V2]'s post ---

// fieldVarintSize, enumWire (PbContentOwn.lean): a varint field's tag and value; an int32 enum
// sign-extended to 64 bits.
func fieldVarintSize(v uint64) int { return 1 + protowire.SizeVarint(v) }
func enumWire(t int32) uint64      { return uint64(int64(t)) }

func derefI32(p *int32) int32 {
	if p == nil {
		return 0
	}
	return *p
}

func derefU64(p *uint64) uint64 {
	if p == nil {
		return 0
	}
	return *p
}

func derefB(p *[]byte) []byte {
	if p == nil {
		return nil
	}
	return *p
}

func lenSizeGo(n int) int { return 1 + protowire.SizeVarint(uint64(n)) + n }

// ccLenMaxGo: an independent transcription of ccLenMax (R1.2): every field counted present, at the
// model's values (what ccPtsCC's cellRO cells give: an unset field reads as zero).
func ccLenMaxGo(c ccC) int {
	return fieldVarintSize(derefU64(c.id)) + fieldVarintSize(enumWire(derefI32(c.typ))) +
		fieldVarintSize(derefU64(c.nodeID)) + lenSizeGo(len(derefB(c.ctx))) + len(c.uf)
}

func cc2LenMaxGo(c cc2C) int {
	s := fieldVarintSize(enumWire(derefI32(c.trans))) + lenSizeGo(len(derefB(c.ctx))) + len(c.uf)
	for _, ch := range c.changes {
		s += lenSizeGo(fieldVarintSize(enumWire(derefI32(ch.typ))) + fieldVarintSize(derefU64(ch.nodeID)) + len(ch.uf))
	}
	return s
}

func a3Extremes() ([]ccC, []cc2C) {
	neg := int32(math.MinInt32)
	m1 := int32(-1)
	maxI := int32(math.MaxInt32)
	maxU := uint64(math.MaxUint64)
	zero := uint64(0)
	var c1 []ccC
	var c2 []cc2C
	for _, n := range []int{0, 127, 128, 16383, 16384, 1 << 21} {
		ctx := make([]byte, n)
		empty := []byte{}
		for _, ty := range []*int32{nil, &neg, &m1, &maxI} {
			c1 = append(c1, ccC{typ: ty, nodeID: &maxU, id: &maxU, ctx: &ctx},
				ccC{typ: ty, nodeID: &zero, id: nil, ctx: &empty}, ccC{typ: ty})
			x := cc2C{trans: ty, ctx: &ctx}
			for k := 0; k < 50; k++ {
				x.changes = append(x.changes, ccsC{typ: &neg, nodeID: &maxU})
			}
			c2 = append(c2, x, cc2C{trans: ty})
		}
		uf := protowire.AppendTag(nil, 1000, 2)
		uf = protowire.AppendBytes(uf, make([]byte, n))
		c1 = append(c1, ccC{typ: &neg, nodeID: &maxU, id: &maxU, ctx: &ctx, uf: uf})
		c2 = append(c2, cc2C{trans: &neg, ctx: &ctx, uf: uf, changes: []ccsC{{typ: &neg, nodeID: &maxU, uf: uf}}})
	}
	return c1, c2
}

func TestA3CCLen(t *testing.T) {
	r := rand.New(rand.NewSource(45))
	worst := 0
	check := func(c ccC) {
		bs, err := proto.Marshal(toPbCC(c))
		if err != nil {
			t.Fatalf("Marshal: %v", err)
		}
		if len(bs) > ccLenMaxGo(c) {
			t.Errorf("ConfChange: len(Marshal) %d > ccLenMax %d: %s", len(bs), ccLenMaxGo(c), c.show())
		}
		if ccLenMaxGo(c) > ccMeasure(c)+64 {
			t.Errorf("ConfChange: ccLenMax %d > ccSize %d + 64: %s", ccLenMaxGo(c), ccMeasure(c), c.show())
		}
		if d := ccLenMaxGo(c) - ccMeasure(c); d > worst {
			worst = d
		}
	}
	for it := 0; it < nEncCC; it++ {
		check(randCCC(t, r))
	}
	c1, _ := a3Extremes()
	for _, c := range c1 {
		check(c)
	}
	t.Logf("A3' ConfChange: len(Marshal) <= ccLenMax <= ccSize + 64 on %d random contents and %d extremes; worst ccLenMax - ccSize %d", nEncCC, len(c1), worst)
}

func TestA3CC2Len(t *testing.T) {
	r := rand.New(rand.NewSource(46))
	worst := 0
	check := func(c cc2C) {
		bs, err := proto.Marshal(toPbCC2(c))
		if err != nil {
			t.Fatalf("Marshal: %v", err)
		}
		if len(bs) > cc2LenMaxGo(c) {
			t.Errorf("ConfChangeV2: len(Marshal) %d > ccLenMax %d: %s", len(bs), cc2LenMaxGo(c), c.show())
		}
		if cc2LenMaxGo(c) > cc2Measure(c)+64 {
			t.Errorf("ConfChangeV2: ccLenMax %d > ccSize %d + 64: %s", cc2LenMaxGo(c), cc2Measure(c), c.show())
		}
		if d := cc2LenMaxGo(c) - cc2Measure(c); d > worst {
			worst = d
		}
	}
	for it := 0; it < nEncCC; it++ {
		check(randCC2C(t, r))
	}
	_, c2 := a3Extremes()
	for _, c := range c2 {
		check(c)
	}
	t.Logf("A3' ConfChangeV2: len(Marshal) <= ccLenMax <= ccSize + 64 on %d random contents and %d extremes; worst ccLenMax - ccSize %d", nEncCC, len(c2), worst)
}

// pbutil.MustUnmarshalMessage's ConfChange case (applyConfChange): etcd's decoder (proto.Unmarshal
// into the given message, panicking on an error) leaves the unknown fields routed at ccSchema.
func TestB2MustUnmarshalCC(t *testing.T) {
	r := rand.New(rand.NewSource(47))
	bad, decoded := 0, 0
	check := func(bs []byte) {
		var d pb.ConfChange
		if proto.Unmarshal(bs, &(pb.ConfChange{})) != nil {
			return // MustUnmarshalMessage panics: not a case of its post
		}
		pbutil.MustUnmarshalMessage(&d, bs)
		decoded++
		if why := ufPred(cpUF(&d), schemas["ConfChange"], innerMax, true); why != "" {
			bad++
			if bad < 5 {
				t.Errorf("MustUnmarshalMessage(ConfChange) of %x: uf violates ufWire: %s", trunc(bs), why)
			}
		}
	}
	o := ufOpts{nonMinOuter: true, takenOK: true, innerNumMax: 1<<31 - 1}
	for it := 0; it < nEncCC; it++ {
		b := encodeWithUF(r, "ConfChange", 0, o)
		check(b)
		check(mutate(r, b))
	}
	for a := 0; a < 256; a++ {
		check([]byte{byte(a)})
		for b := 0; b < 256; b++ {
			check([]byte{byte(a), byte(b)})
		}
	}
	t.Logf("B2 MustUnmarshalMessage(ConfChange): %d decoded inputs, %d ufWire violations", decoded, bad)
}
