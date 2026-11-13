package pbschema

// The trusted post of `proto.UnmarshalPb` and the trusted encoder axioms, at raftpb.Entry and
// raftpb.Message, tested against protobuf-go (the version examples/go.mod pins) and the raft fork's
// raftpb. The Lean statements these tests check, all trusted:
//
//   - D1, the decoder's post (Spec/google_golang_org/protobuf/proto/UnmarshalPb.lean), on every input
//     the decoder accepts (TestD1PostMessage, TestD1PostEntry): proto.Size of the result is the
//     instance's size of its content and at most 2|bs| (the size bound); every level's unknown
//     fields satisfy `ufWire` (ufValid); the content is the one the bytes encode (the `wire`
//     conjunct, the opaque decoder read as an independent reference decoder) and its model is what
//     the getters return; and under the instance's decOk the decoded ConfState has no unknown
//     fields (dec). Targeted: `72 00` decodes with one response (D1 says nothing of Responses);
//     `4a 08 12 06 0a 04 08 01 30 00` decodes with decOk false; the packed ConfState zeros family
//     (the size bound's extreme, ratio tending to 2); group nesting 10001/10002 in Entry.
//   - D2, the round trip, and the encoder axioms `entryEncC_ok` and `msgEncC_ok`
//     (TestD2P2EntryEncoder, TestD2P2MessageEncoder): for a random content (every optional scalar
//     present or not, Data/Context nil, empty or not, unknown fields satisfying `ufWire` at every
//     level, no responses), proto.Marshal's length and proto.Size are the instance's size, and
//     Unmarshal of the encoding gives back exactly the content (decOk preserved) with the expected
//     getters; D1 holds on the encoding too. Group nesting 10000/10001 at every level of a Message.
//
// The instances' formulas, transcribed (Proof/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/
// PerTypeEntry.lean and PerTypeMessage.lean):
//   - entC / msgC (and csC, metaC, snapC) are EntryC / MsgC: every proto2 optional scalar's
//     presence (a nil pointer is `none`), `Data`/`Context` nil or not (`*[]byte`), the unknown
//     fields of every level, and (msgC) the responses' contents (the `Loc`s are not compared).
//   - entrySizeC / msgSizeC transcribe `entrySize` / `msgSize` (lenSize, optVarintSize, repW64Size,
//     csSize, metaSize, snapSize, MsgFC.size, respsSize), the enum sign-extended to 64 bits.
//   - levelsC transcribes `MsgC.levels` (responses included), checked with ufPred (the Go copy of
//     `ufWire`, wire_helpers_test.go).
//   - entModel / wireModel transcribe `EntryC.model` / `MsgC.model` (getD at the zero value,
//     csZero, metaZero); wireModel drops the responses (MsgDecOk does not mention them).
//   - csUfNil transcribes `MsgC.csUfNil` (the Message instance's decOk; the Entry instance's is
//     True); MsgMarshals = no responses.
//   - refDecodeMsg / refDecodeEnt: an independent proto2 decoder (not protobuf-go's code; unknown
//     values parsed with valueLen, the Go copy of Lean's `WVal`).
//
// CI size: each test runs a few seconds (nRand etc. below); the c9 harness these come from ran
// 300000 inputs per generator and every input of length 3.

import (
	"fmt"
	"math"
	"math/rand"
	"strings"
	"testing"

	"google.golang.org/protobuf/encoding/protowire"
	"google.golang.org/protobuf/proto"

	pb "go.etcd.io/raft/v3/raftpb"
)

// The input counts (CI size).
const (
	nRand     = 60000  // per generator in the D1 tests
	nLen3     = 100000 // random inputs of length 3 in the D1 tests
	nEncEntry = 100000 // random contents in TestD2P2EntryEncoder
	nEncMsg   = 50000  // random contents in TestD2P2MessageEncoder
)

// forShortInputs runs f on every input of length <= 2 and on nLen3 random inputs of length 3.
func forShortInputs(r *rand.Rand, f func([]byte)) {
	buf := make([]byte, 3)
	for l := 0; l <= 2; l++ {
		for x := 0; x < 1<<(8*l); x++ {
			for i := 0; i < l; i++ {
				buf[i] = byte(x >> (8 * i))
			}
			f(buf[:l])
		}
	}
	for it := 0; it < nLen3; it++ {
		r.Read(buf)
		f(buf)
	}
}

// ---------------- the wire contents ----------------

type entC struct {
	term, index *uint64
	typ         *int32
	data        *[]byte
	uf          []byte
}

type csC struct {
	voters, learners, vout, lnext []uint64
	autoLeave                     *bool
	uf                            []byte
}

type metaC struct {
	cs          *csC
	index, term *uint64
	uf          []byte
}

type snapC struct {
	data *[]byte
	meta *metaC
	uf   []byte
}

type msgC struct {
	typ                            *int32
	to, from, term, logTerm, index *uint64
	entries                        []entC
	commit, vote                   *uint64
	snap                           *snapC
	reject                         *bool
	rejectHint                     *uint64
	context                        *[]byte
	uf                             []byte
	resps                          []msgC
}

// ---- show: a canonical text of a content (equality of contents = equality of texts) ----

func sU(p *uint64) string {
	if p == nil {
		return "-"
	}
	return fmt.Sprint(*p)
}
func sI(p *int32) string {
	if p == nil {
		return "-"
	}
	return fmt.Sprint(*p)
}
func sB(p *bool) string {
	if p == nil {
		return "-"
	}
	return fmt.Sprint(*p)
}
func sD(p *[]byte) string {
	if p == nil {
		return "-"
	}
	return fmt.Sprintf("[%x]", *p)
}

func (e entC) show() string {
	return fmt.Sprintf("E{t%s i%s y%s d%s u%x}", sU(e.term), sU(e.index), sI(e.typ), sD(e.data), e.uf)
}

func (c *csC) show() string {
	if c == nil {
		return "-"
	}
	return fmt.Sprintf("CS{%v %v %v %v al%s u%x}", c.voters, c.learners, c.vout, c.lnext, sB(c.autoLeave), c.uf)
}

func (m *metaC) show() string {
	if m == nil {
		return "-"
	}
	return fmt.Sprintf("MD{%s i%s t%s u%x}", m.cs.show(), sU(m.index), sU(m.term), m.uf)
}

func (s *snapC) show() string {
	if s == nil {
		return "-"
	}
	return fmt.Sprintf("S{d%s %s u%x}", sD(s.data), s.meta.show(), s.uf)
}

func (c msgC) show() string {
	var b strings.Builder
	fmt.Fprintf(&b, "M{y%s to%s fr%s te%s lt%s ix%s [", sI(c.typ), sU(c.to), sU(c.from), sU(c.term), sU(c.logTerm), sU(c.index))
	for _, e := range c.entries {
		b.WriteString(e.show())
	}
	fmt.Fprintf(&b, "] co%s vo%s %s rj%s rh%s cx%s u%x R[", sU(c.commit), sU(c.vote), c.snap.show(), sB(c.reject), sU(c.rejectHint), sD(c.context), c.uf)
	for _, r := range c.resps {
		b.WriteString(r.show())
	}
	b.WriteString("]}")
	return b.String()
}

// ---- Go objects <-> contents ----

func cpU(p *uint64) *uint64 {
	if p == nil {
		return nil
	}
	v := *p
	return &v
}
func cpB(p *bool) *bool {
	if p == nil {
		return nil
	}
	v := *p
	return &v
}
func cpD(d []byte) *[]byte {
	if d == nil {
		return nil
	}
	x := append([]byte{}, d...)
	return &x
}
func cpUF(m proto.Message) []byte { return append([]byte(nil), m.ProtoReflect().GetUnknown()...) }

func contentOfEnt(e *pb.Entry) entC {
	c := entC{term: cpU(e.Term), index: cpU(e.Index), data: cpD(e.Data), uf: cpUF(e)}
	if e.Type != nil {
		v := int32(*e.Type)
		c.typ = &v
	}
	return c
}

func contentOfMsg(m *pb.Message) msgC {
	c := msgC{to: cpU(m.To), from: cpU(m.From), term: cpU(m.Term), logTerm: cpU(m.LogTerm), index: cpU(m.Index),
		commit: cpU(m.Commit), vote: cpU(m.Vote), reject: cpB(m.Reject), rejectHint: cpU(m.RejectHint),
		context: cpD(m.Context), uf: cpUF(m)}
	if m.Type != nil {
		v := int32(*m.Type)
		c.typ = &v
	}
	for _, e := range m.Entries {
		c.entries = append(c.entries, contentOfEnt(e))
	}
	if s := m.Snapshot; s != nil {
		sc := &snapC{data: cpD(s.Data), uf: cpUF(s)}
		if md := s.Metadata; md != nil {
			mc := &metaC{index: cpU(md.Index), term: cpU(md.Term), uf: cpUF(md)}
			if cs := md.ConfState; cs != nil {
				mc.cs = &csC{voters: append([]uint64(nil), cs.Voters...), learners: append([]uint64(nil), cs.Learners...),
					vout: append([]uint64(nil), cs.VotersOutgoing...), lnext: append([]uint64(nil), cs.LearnersNext...),
					autoLeave: cpB(cs.AutoLeave), uf: cpUF(cs)}
			}
			sc.meta = mc
		}
		c.snap = sc
	}
	for _, r := range m.Responses {
		c.resps = append(c.resps, contentOfMsg(r))
	}
	return c
}

func toPbEnt(c entC) *pb.Entry {
	e := &pb.Entry{Term: cpU(c.term), Index: cpU(c.index)}
	if c.typ != nil {
		e.Type = pb.EntryType(*c.typ).Enum()
	}
	if c.data != nil {
		e.Data = append([]byte{}, (*c.data)...)
	}
	setUF(e, append([]byte(nil), c.uf...))
	return e
}

func toPbMsg(c msgC) *pb.Message {
	m := &pb.Message{To: cpU(c.to), From: cpU(c.from), Term: cpU(c.term), LogTerm: cpU(c.logTerm), Index: cpU(c.index),
		Commit: cpU(c.commit), Vote: cpU(c.vote), Reject: cpB(c.reject), RejectHint: cpU(c.rejectHint)}
	if c.typ != nil {
		m.Type = pb.MessageType(*c.typ).Enum()
	}
	if c.context != nil {
		m.Context = append([]byte{}, (*c.context)...)
	}
	for _, e := range c.entries {
		m.Entries = append(m.Entries, toPbEnt(e))
	}
	if s := c.snap; s != nil {
		ps := &pb.Snapshot{}
		if s.data != nil {
			ps.Data = append([]byte{}, (*s.data)...)
		}
		if md := s.meta; md != nil {
			pm := &pb.SnapshotMetadata{Index: cpU(md.index), Term: cpU(md.term)}
			if cs := md.cs; cs != nil {
				pc := &pb.ConfState{Voters: append([]uint64(nil), cs.voters...), Learners: append([]uint64(nil), cs.learners...),
					VotersOutgoing: append([]uint64(nil), cs.vout...), LearnersNext: append([]uint64(nil), cs.lnext...),
					AutoLeave: cpB(cs.autoLeave)}
				setUF(pc, append([]byte(nil), cs.uf...))
				pm.ConfState = pc
			}
			setUF(pm, append([]byte(nil), md.uf...))
			ps.Metadata = pm
		}
		setUF(ps, append([]byte(nil), s.uf...))
		m.Snapshot = ps
	}
	for _, r := range c.resps {
		m.Responses = append(m.Responses, toPbMsg(r))
	}
	setUF(m, append([]byte(nil), c.uf...))
	return m
}

// ---------------- the Lean formulas ----------------

func optVarintSizeU(p *uint64) int {
	if p == nil {
		return 0
	}
	return 1 + protowire.SizeVarint(*p)
}

// enum: `uint.Z (W64 (sint.Z t))`: the int32 sign-extended to 64 bits.
func optEnumSize(p *int32) int {
	if p == nil {
		return 0
	}
	return 1 + protowire.SizeVarint(uint64(int64(*p)))
}

func lenSize(n int) int { return 1 + protowire.SizeVarint(uint64(n)) + n }

func optBytesSize(p *[]byte) int {
	if p == nil {
		return 0
	}
	return lenSize(len(*p))
}

func optBoolSize(p *bool) int {
	if p == nil {
		return 0
	}
	return 2
}

func entrySizeC(e entC) int {
	s := optEnumSize(e.typ) + optVarintSizeU(e.term) + optVarintSizeU(e.index)
	if e.data != nil {
		s += 1 + protowire.SizeVarint(uint64(len(*e.data))) + len(*e.data)
	}
	return s + len(e.uf)
}

func repW64Size(xs []uint64) int {
	s := 0
	for _, v := range xs {
		s += 1 + protowire.SizeVarint(v)
	}
	return s
}

func csSize(c *csC) int {
	return repW64Size(c.voters) + repW64Size(c.learners) + repW64Size(c.vout) + repW64Size(c.lnext) +
		optBoolSize(c.autoLeave) + len(c.uf)
}

func metaSize(m *metaC) int {
	s := 0
	if m.cs != nil {
		s += lenSize(csSize(m.cs))
	}
	return s + optVarintSizeU(m.index) + optVarintSizeU(m.term) + len(m.uf)
}

func snapSize(s *snapC) int {
	n := optBytesSize(s.data)
	if s.meta != nil {
		n += lenSize(metaSize(s.meta))
	}
	return n + len(s.uf)
}

func msgFSize(f msgC) int {
	s := optEnumSize(f.typ) + optVarintSizeU(f.to) + optVarintSizeU(f.from) + optVarintSizeU(f.term) +
		optVarintSizeU(f.logTerm) + optVarintSizeU(f.index)
	for _, e := range f.entries {
		s += lenSize(entrySizeC(e))
	}
	s += optVarintSizeU(f.commit) + optVarintSizeU(f.vote)
	if f.snap != nil {
		s += lenSize(snapSize(f.snap))
	}
	return s + optBoolSize(f.reject) + optVarintSizeU(f.rejectHint) + optBytesSize(f.context) + len(f.uf)
}

func msgSizeC(c msgC) int {
	s := msgFSize(c)
	for _, r := range c.resps {
		s += lenSize(msgSizeC(r))
	}
	return s
}

// levelsC: `MsgC.levels` (own, entries', snapshot's, then each response's).
func levelsC(c msgC) []level {
	ls := []level{{"Message", c.uf}}
	for _, e := range c.entries {
		ls = append(ls, level{"Entry", e.uf})
	}
	if s := c.snap; s != nil {
		ls = append(ls, level{"Snapshot", s.uf})
		if m := s.meta; m != nil {
			ls = append(ls, level{"SnapshotMetadata", m.uf})
			if cs := m.cs; cs != nil {
				ls = append(ls, level{"ConfState", cs.uf})
			}
		}
	}
	for _, r := range c.resps {
		ls = append(ls, levelsC(r)...)
	}
	return ls
}

func ufValidC(c msgC) string {
	for _, lv := range levelsC(c) {
		if why := ufPred(lv.uf, schemas[lv.name], innerMax, true); why != "" {
			return lv.name + ": " + why
		}
	}
	return ""
}

// csUfNil: `MsgC.csUfNil` (the Message instance's decOk).
func csUfNil(c msgC) bool {
	return c.snap == nil || c.snap.meta == nil || c.snap.meta.cs == nil || len(c.snap.meta.cs.uf) == 0
}

// ---- models: `EntryC.model`, `MsgC.model` (from contents) and the getters' view (from Go) ----

func gU(p *uint64) uint64 {
	if p == nil {
		return 0
	}
	return *p
}
func gI(p *int32) int32 {
	if p == nil {
		return 0
	}
	return *p
}
func gB(p *bool) bool { return p != nil && *p }
func gD(p *[]byte) []byte {
	if p == nil {
		return nil
	}
	return *p
}

func entModel(e entC) string {
	return fmt.Sprintf("(%d %d %d %x)", gU(e.term), gU(e.index), gI(e.typ), gD(e.data))
}

// wireModel: `wireOf (MsgC.model c)` (msg, ents, snap, ctx); the responses' count separately.
func wireModel(c msgC) string {
	var b strings.Builder
	fmt.Fprintf(&b, "(%d %d %d %d %d %d %d %d %v %d) [", gI(c.typ), gU(c.to), gU(c.from), gU(c.term), gU(c.logTerm),
		gU(c.index), gU(c.commit), gU(c.vote), gB(c.reject), gU(c.rejectHint))
	for _, e := range c.entries {
		b.WriteString(entModel(e))
	}
	b.WriteString("] ")
	if s := c.snap; s == nil {
		b.WriteString("none")
	} else {
		fmt.Fprintf(&b, "some(%x ", gD(s.data))
		if m := s.meta; m == nil {
			b.WriteString("([] [] [] [] false) 0 0") // metaZero, csZero
		} else {
			if cs := m.cs; cs == nil {
				b.WriteString("([] [] [] [] false)")
			} else {
				fmt.Fprintf(&b, "(%v %v %v %v %v)", nz(cs.voters), nz(cs.learners), nz(cs.vout), nz(cs.lnext), gB(cs.autoLeave))
			}
			fmt.Fprintf(&b, " %d %d", gU(m.index), gU(m.term))
		}
		b.WriteString(")")
	}
	fmt.Fprintf(&b, " %x", gD(c.context))
	return b.String()
}

func nz(xs []uint64) []uint64 {
	if xs == nil {
		return []uint64{}
	}
	return xs
}

func entGetters(e *pb.Entry) string {
	return fmt.Sprintf("(%d %d %d %x)", e.GetTerm(), e.GetIndex(), int32(e.GetType()), e.GetData())
}

func msgGetters(m *pb.Message) string {
	var b strings.Builder
	fmt.Fprintf(&b, "(%d %d %d %d %d %d %d %d %v %d) [", int32(m.GetType()), m.GetTo(), m.GetFrom(), m.GetTerm(), m.GetLogTerm(),
		m.GetIndex(), m.GetCommit(), m.GetVote(), m.GetReject(), m.GetRejectHint())
	for _, e := range m.GetEntries() {
		b.WriteString(entGetters(e))
	}
	b.WriteString("] ")
	if s := m.GetSnapshot(); s == nil {
		b.WriteString("none")
	} else {
		cs := s.GetMetadata().GetConfState()
		fmt.Fprintf(&b, "some(%x (%v %v %v %v %v) %d %d)", s.GetData(), nz(cs.GetVoters()), nz(cs.GetLearners()),
			nz(cs.GetVotersOutgoing()), nz(cs.GetLearnersNext()), cs.GetAutoLeave(), s.GetMetadata().GetIndex(), s.GetMetadata().GetTerm())
	}
	fmt.Fprintf(&b, " %x", m.GetContext())
	return b.String()
}

// ---------------- the reference decoder ----------------

var errRef = fmt.Errorf("ref: decode error")

// refField reads one tag; ok=false on error.
func refTag(b []byte) (num uint64, wt protowire.Type, n int, ok bool) {
	v, n := protowire.ConsumeVarint(b)
	if n < 0 {
		return 0, 0, 0, false
	}
	num, wt = v>>3, protowire.Type(v&7)
	if num < 1 || num > uint64(protowire.MaxValidNumber) || wt == protowire.EndGroupType {
		return 0, 0, 0, false
	}
	return num, wt, n, true
}

// refUnknown appends one routed field (tag re-encoded minimally, value verbatim) and returns its length.
func refUnknown(uf *[]byte, b []byte, num uint64, wt protowire.Type) (int, bool) {
	k, why := valueLen(b, num, wt, 1, innerMax)
	if why != "" {
		return 0, false
	}
	*uf = protowire.AppendTag(*uf, protowire.Number(num), wt)
	*uf = append(*uf, b[:k]...)
	return k, true
}

func refVarint(b []byte) (uint64, int, bool) {
	v, n := protowire.ConsumeVarint(b)
	return v, n, n >= 0
}

func refBytes(b []byte) ([]byte, int, bool) {
	v, n := protowire.ConsumeBytes(b)
	return v, n, n >= 0
}

func pu(v uint64) *uint64   { return &v }
func pbool(v uint64) *bool  { x := v != 0; return &x }
func pi32(v uint64) *int32  { x := int32(v); return &x }
func pdat(v []byte) *[]byte { x := append([]byte{}, v...); return &x }

func refDecodeEnt(b []byte, c *entC) bool {
	for len(b) > 0 {
		num, wt, n, ok := refTag(b)
		if !ok {
			return false
		}
		b = b[n:]
		if !takes(schemas["Entry"], int(num), wt) {
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
			c.data = pdat(v)
			b = b[k:]
			continue
		}
		v, k, ok := refVarint(b)
		if !ok {
			return false
		}
		switch num {
		case 1:
			c.typ = pi32(v)
		case 2:
			c.term = pu(v)
		case 3:
			c.index = pu(v)
		}
		b = b[k:]
	}
	return true
}

func refRepU64(xs *[]uint64, b []byte, wt protowire.Type) (int, bool) {
	if wt == 0 {
		v, k, ok := refVarint(b)
		if !ok {
			return 0, false
		}
		*xs = append(*xs, v)
		return k, true
	}
	body, k, ok := refBytes(b)
	if !ok {
		return 0, false
	}
	for len(body) > 0 {
		v, n, ok := refVarint(body)
		if !ok {
			return 0, false
		}
		*xs = append(*xs, v)
		body = body[n:]
	}
	return k, true
}

func refDecodeCS(b []byte, c *csC) bool {
	for len(b) > 0 {
		num, wt, n, ok := refTag(b)
		if !ok {
			return false
		}
		b = b[n:]
		var k int
		if !takes(schemas["ConfState"], int(num), wt) {
			k, ok = refUnknown(&c.uf, b, num, wt)
		} else {
			switch num {
			case 1:
				k, ok = refRepU64(&c.voters, b, wt)
			case 2:
				k, ok = refRepU64(&c.learners, b, wt)
			case 3:
				k, ok = refRepU64(&c.vout, b, wt)
			case 4:
				k, ok = refRepU64(&c.lnext, b, wt)
			case 5:
				var v uint64
				v, k, ok = refVarint(b)
				c.autoLeave = pbool(v)
			}
		}
		if !ok {
			return false
		}
		b = b[k:]
	}
	return true
}

func refDecodeMeta(b []byte, c *metaC) bool {
	for len(b) > 0 {
		num, wt, n, ok := refTag(b)
		if !ok {
			return false
		}
		b = b[n:]
		var k int
		if !takes(schemas["SnapshotMetadata"], int(num), wt) {
			k, ok = refUnknown(&c.uf, b, num, wt)
		} else if num == 1 {
			var body []byte
			body, k, ok = refBytes(b)
			if ok {
				if c.cs == nil {
					c.cs = &csC{}
				}
				ok = refDecodeCS(body, c.cs) // merge
			}
		} else {
			var v uint64
			v, k, ok = refVarint(b)
			if num == 2 {
				c.index = pu(v)
			} else {
				c.term = pu(v)
			}
		}
		if !ok {
			return false
		}
		b = b[k:]
	}
	return true
}

func refDecodeSnap(b []byte, c *snapC) bool {
	for len(b) > 0 {
		num, wt, n, ok := refTag(b)
		if !ok {
			return false
		}
		b = b[n:]
		var k int
		if !takes(schemas["Snapshot"], int(num), wt) {
			k, ok = refUnknown(&c.uf, b, num, wt)
		} else {
			var body []byte
			body, k, ok = refBytes(b)
			if ok && num == 1 {
				c.data = pdat(body)
			} else if ok {
				if c.meta == nil {
					c.meta = &metaC{}
				}
				ok = refDecodeMeta(body, c.meta)
			}
		}
		if !ok {
			return false
		}
		b = b[k:]
	}
	return true
}

func refDecodeMsg(b []byte, c *msgC) bool {
	for len(b) > 0 {
		num, wt, n, ok := refTag(b)
		if !ok {
			return false
		}
		b = b[n:]
		var k int
		if !takes(schemas["Message"], int(num), wt) {
			k, ok = refUnknown(&c.uf, b, num, wt)
		} else if wt == 2 {
			var body []byte
			body, k, ok = refBytes(b)
			if ok {
				switch num {
				case 7:
					var e entC
					ok = refDecodeEnt(body, &e)
					c.entries = append(c.entries, e)
				case 9:
					if c.snap == nil {
						c.snap = &snapC{}
					}
					ok = refDecodeSnap(body, c.snap)
				case 12:
					c.context = pdat(body)
				case 14:
					var r msgC
					ok = refDecodeMsg(body, &r)
					c.resps = append(c.resps, r)
				}
			}
		} else {
			var v uint64
			v, k, ok = refVarint(b)
			switch num {
			case 1:
				c.typ = pi32(v)
			case 2:
				c.to = pu(v)
			case 3:
				c.from = pu(v)
			case 4:
				c.term = pu(v)
			case 5:
				c.logTerm = pu(v)
			case 6:
				c.index = pu(v)
			case 8:
				c.commit = pu(v)
			case 10:
				c.reject = pbool(v)
			case 11:
				c.rejectHint = pu(v)
			case 13:
				c.vote = pu(v)
			}
		}
		if !ok {
			return false
		}
		b = b[k:]
	}
	return true
}

// ---------------- the D1 checkers ----------------

type d1Stats struct {
	inputs, decoded, withResps, decOk, notDecOk int
	refRejectsGoAccepts                         int
	maxRatio                                    float64
	maxRatioIn                                  []byte
	fails                                       map[string]int
	example                                     map[string][]byte
}

func newStats() *d1Stats {
	return &d1Stats{fails: map[string]int{}, example: map[string][]byte{}}
}

func (s *d1Stats) fail(k string, bs []byte) {
	s.fails[k]++
	if _, ok := s.example[k]; !ok {
		s.example[k] = append([]byte(nil), bs...)
	}
}

func (s *d1Stats) report(t *testing.T, name string) {
	t.Logf("%s: %d inputs, %d decoded (%d with Responses, decOk %d / not decOk %d), max proto.Size/|bs| %.6f (in=%x)",
		name, s.inputs, s.decoded, s.withResps, s.decOk, s.notDecOk, s.maxRatio, trunc(s.maxRatioIn))
	if s.refRejectsGoAccepts > 0 {
		t.Logf("%s: reference decoder rejects %d inputs protobuf-go accepts", name, s.refRejectsGoAccepts)
	}
	if len(s.fails) == 0 {
		t.Logf("%s PASS", name)
	}
	for k, n := range s.fails {
		t.Errorf("%s FAIL %s: %d (first: %x)", name, k, n, trunc(s.example[k]))
	}
}

// checkMsgD1 decodes bs as a Message; on success checks the whole D1 post. Returns the content.
func checkMsgD1(s *d1Stats, bs []byte) (msgC, bool) {
	s.inputs++
	var m pb.Message
	if proto.Unmarshal(bs, &m) != nil {
		return msgC{}, false
	}
	s.decoded++
	c := contentOfMsg(&m)
	if len(c.resps) > 0 {
		s.withResps++
	}
	// (a) size: proto.Size = msgSize c <= 2|bs|.
	sz := msgSizeC(c)
	if ps := proto.Size(&m); ps != sz {
		s.fail(fmt.Sprintf("size: proto.Size %d != msgSize", ps), bs)
	}
	if sz > 2*len(bs) {
		s.fail("size: msgSize > 2|bs|", bs)
	}
	if len(bs) > 0 {
		if r := float64(sz) / float64(len(bs)); r > s.maxRatio {
			s.maxRatio, s.maxRatioIn = r, append([]byte(nil), bs...)
		}
	}
	// (b) ufValid at every level (responses included).
	if why := ufValidC(c); why != "" {
		s.fail("ufValid: "+why, bs)
	}
	// (c) wire: determinism, the reference decoder's content, the model is the getters' view.
	var m2 pb.Message
	if proto.Unmarshal(bs, &m2) != nil || contentOfMsg(&m2).show() != c.show() {
		s.fail("wire: re-decode differs", bs)
	}
	var rc msgC
	if !refDecodeMsg(bs, &rc) {
		s.refRejectsGoAccepts++
		s.fail("wire: reference decoder rejects", bs)
	} else if rc.show() != c.show() {
		s.fail("wire: reference content differs", bs)
	}
	if wireModel(c) != msgGetters(&m) {
		s.fail("wire: MsgC.model differs from the getters", bs)
	}
	// (d) dec under decOk: decOk c (csUfNil) => the decoded ConfState has no unknown fields.
	if csUfNil(c) {
		s.decOk++
		if cs := m.GetSnapshot().GetMetadata().GetConfState(); cs != nil && len(cs.ProtoReflect().GetUnknown()) != 0 {
			s.fail("decOk: csUfNil but the Go ConfState has unknown fields", bs)
		}
	} else {
		s.notDecOk++
	}
	return c, true
}

func checkEntD1(s *d1Stats, bs []byte) (entC, bool) {
	s.inputs++
	var e pb.Entry
	if proto.Unmarshal(bs, &e) != nil {
		return entC{}, false
	}
	s.decoded++
	s.decOk++ // the Entry instance's decOk is True
	c := contentOfEnt(&e)
	sz := entrySizeC(c)
	if ps := proto.Size(&e); ps != sz {
		s.fail(fmt.Sprintf("size: proto.Size %d != entrySize", ps), bs)
	}
	if sz > 2*len(bs) {
		s.fail("size: entrySize > 2|bs|", bs)
	}
	if len(bs) > 0 {
		if r := float64(sz) / float64(len(bs)); r > s.maxRatio {
			s.maxRatio, s.maxRatioIn = r, append([]byte(nil), bs...)
		}
	}
	if why := ufPred(c.uf, schemas["Entry"], innerMax, true); why != "" {
		s.fail("ufValid: "+why, bs)
	}
	var e2 pb.Entry
	if proto.Unmarshal(bs, &e2) != nil || contentOfEnt(&e2).show() != c.show() {
		s.fail("wire: re-decode differs", bs)
	}
	var rc entC
	if !refDecodeEnt(bs, &rc) {
		s.refRejectsGoAccepts++
		s.fail("wire: reference decoder rejects", bs)
	} else if rc.show() != c.show() {
		s.fail("wire: reference content differs", bs)
	}
	if entModel(c) != entGetters(&e) {
		s.fail("wire: EntryC.model differs from the getters", bs)
	}
	return c, true
}

func trunc(b []byte) []byte {
	if len(b) > 64 {
		return b[:64]
	}
	return b
}

func mutate(r *rand.Rand, src []byte) []byte {
	bs := append([]byte(nil), src...)
	for k := 1 + r.Intn(3); k > 0; k-- {
		switch r.Intn(4) {
		case 0:
			if len(bs) > 0 {
				bs[r.Intn(len(bs))] = byte(r.Intn(256))
			}
		case 1:
			p := r.Intn(len(bs) + 1)
			bs = append(bs[:p], append([]byte{byte(r.Intn(256))}, bs[p:]...)...)
		case 2:
			if len(bs) > 0 {
				p := r.Intn(len(bs))
				bs = append(bs[:p], bs[p+1:]...)
			}
		case 3:
			if len(bs) > 0 {
				bs[r.Intn(len(bs))] = []byte{0, 1, 0x7f, 0x80, 0x0a, 0x12, 0x4a, 0x72, 0x3a, 0x08}[r.Intn(10)]
			}
		}
	}
	return bs
}

func TestD1PostMessage(t *testing.T) {
	s := newStats()
	r := rand.New(rand.NewSource(21))
	adv := ufOpts{nonMinOuter: true, badNums: true, badEnds: true, takenOK: true, innerNumMax: 1<<31 - 1}
	var pool [][]byte
	// 1. encodeWithUF (uf at every level, adversarial), possibly mutated.
	for it := 0; it < nRand; it++ {
		bs := encodeWithUF(r, "Message", 0, adv)
		if r.Intn(3) == 0 {
			bs = mutate(r, bs)
		}
		if _, ok := checkMsgD1(s, bs); ok && len(pool) < 20000 {
			pool = append(pool, bs)
		}
	}
	// 2. genAdv (wrong wire types, packed ConfState lists, Responses up to depth 4, non-minimal tags).
	for it := 0; it < nRand; it++ {
		bs := genAdv(r, "Message", 0)
		if _, ok := checkMsgD1(s, bs); ok && len(pool) < 40000 {
			pool = append(pool, bs)
		}
	}
	// 3. mutations of decoded inputs.
	for it := 0; it < nRand; it++ {
		checkMsgD1(s, mutate(r, pool[r.Intn(len(pool))]))
	}
	// 4. every input of length <= 2, and random inputs of length 3.
	forShortInputs(r, func(bs []byte) { checkMsgD1(s, bs) })
	s.report(t, fmt.Sprintf("D1 Message (random encodeWithUF %d + genAdv %d + mutations %d + exhaustive len<=2 + %d random len 3)", nRand, nRand, nRand, nLen3))

	// targeted cases
	t5 := newStats()
	// (c) D1 claims nothing about Responses: `72 00` decodes with one response.
	c, ok := checkMsgD1(t5, []byte{0x72, 0x00})
	if !ok || len(c.resps) != 1 {
		t.Errorf("72 00: decoded %v, %d responses (want decoded, 1)", ok, len(c.resps))
	} else {
		t.Logf("D1 case `72 00`: decodes, len(Responses)=1, MsgMarshals=%v; the D1 checks (size, ufValid, wire=MsgDecOk, decOk) pass without resps=[] (failures so far: %d)", len(c.resps) == 0, len(t5.fails))
		// No c0 without responses encodes to these bytes: re-marshalling without responses differs.
		c0 := c
		c0.resps = nil
		e0, _ := proto.Marshal(toPbMsg(c0))
		t.Logf("  marshalling the content without its response gives %q (not 72 00): D2's premise fails, so D2 claims nothing", e0)
	}
	// (d) a ConfState with unknown fields: decOk false (the post gives no `dec`).
	csBs := []byte{0x4a, 0x08, 0x12, 0x06, 0x0a, 0x04, 0x08, 0x01, 0x30, 0x00}
	c, ok = checkMsgD1(t5, csBs)
	if !ok {
		t.Errorf("4a 08 12 06 0a 04 08 01 30 00: does not decode")
	} else if csUfNil(c) {
		t.Errorf("4a 08 12 06 0a 04 08 01 30 00: decOk (csUfNil) true, want false")
	} else {
		t.Logf("D1 case `%x`: decodes, ConfState uf %x, decOk=false (the post gives no dec here)", csBs, c.snap.meta.cs.uf)
	}
	more := []struct {
		name string
		bs   []byte
	}{
		{"empty", nil},
		{"ConfState voters [1], no uf (decOk true)", []byte{0x4a, 0x06, 0x12, 0x04, 0x0a, 0x02, 0x08, 0x01}},
		{"packed voters [0 0 0] (input 11, size 12)", []byte{0x4a, 0x09, 0x12, 0x07, 0x0a, 0x05, 0x0a, 0x03, 0, 0, 0}},
		{"two snapshot occurrences merge (data, metadata, uf)", []byte{0x4a, 0x05, 0x0a, 0x00, 0xa8, 0x06, 0x01, 0x4a, 0x06, 0x0a, 0x01, 0x05, 0xb0, 0x06, 0x02}},
		{"type = 0xFFFFFFFF (int32 -1, re-encoded in 10 bytes)", []byte{0x08, 0xff, 0xff, 0xff, 0xff, 0x0f}},
		{"type = 2^32+5 (truncated to 5)", []byte{0x08, 0x85, 0x80, 0x80, 0x80, 0x10}},
		{"reject = 7 (bool true)", []byte{0x50, 0x07}},
		{"context empty (present)", []byte{0x62, 0x00}},
		{"nested responses with uf", []byte{0x72, 0x05, 0x72, 0x03, 0xf8, 0x06, 0x01}},
		{"uf with non-minimal outer tag (re-encoded)", []byte{0xf8, 0x86, 0x00, 0x01}},
	}
	for _, mc := range more {
		before := len(t5.fails)
		c, ok := checkMsgD1(t5, mc.bs)
		t.Logf("D1 case %-55s decoded=%v decOk=%v resps=%d size=%d len=%d: %s", mc.name+":", ok, ok && csUfNil(c), len(c.resps), msgSizeC(c), len(mc.bs),
			map[bool]string{true: "checks pass", false: "CHECK FAILED"}[len(t5.fails) == before])
	}
	// the size bound's extreme family (TestC9H1DecodeExpansion): packed ConfState zeros, with Responses.
	for _, k := range []int{1, 63, 125, 126, 8190, 1 << 14, 1 << 20} {
		for _, fl := range []int{1, 4} {
			for _, resp := range []int{0, 3} {
				bs := packedConfStateMsg(k, fl, resp)
				before := len(t5.fails)
				c, ok := checkMsgD1(t5, bs)
				if k == 1<<20 || k == 126 {
					t.Logf("D1 case packed ConfState zeros k=%d fields=%d resp=%d: decoded=%v msgSize=%d len=%d ratio %.6f: %s", k, fl, resp, ok,
						msgSizeC(c), len(bs), float64(msgSizeC(c))/float64(len(bs)), map[bool]string{true: "checks pass", false: "CHECK FAILED"}[len(t5.fails) == before])
				}
			}
		}
	}
	t5.report(t, "D1 Message targeted (12 cases + 28 packed ConfState inputs)")
}

func TestD1PostEntry(t *testing.T) {
	s := newStats()
	r := rand.New(rand.NewSource(22))
	adv := ufOpts{nonMinOuter: true, badNums: true, badEnds: true, takenOK: true, innerNumMax: 1<<31 - 1}
	var pool [][]byte
	for it := 0; it < nRand; it++ {
		bs := encodeWithUF(r, "Entry", 0, adv)
		if r.Intn(3) == 0 {
			bs = mutate(r, bs)
		}
		if _, ok := checkEntD1(s, bs); ok && len(pool) < 20000 {
			pool = append(pool, bs)
		}
	}
	for it := 0; it < nRand; it++ {
		bs := genAdv(r, "Entry", 0)
		if _, ok := checkEntD1(s, bs); ok && len(pool) < 40000 {
			pool = append(pool, bs)
		}
	}
	for it := 0; it < nRand; it++ {
		checkEntD1(s, mutate(r, pool[r.Intn(len(pool))]))
	}
	forShortInputs(r, func(bs []byte) { checkEntD1(s, bs) })
	for _, bs := range [][]byte{nil, {0x22, 0x00}, {0x08, 0xff, 0xff, 0xff, 0xff, 0x0f}, {0x08, 0x07}, deepGroup(100, 10001, true), deepGroup(100, 10002, false)} {
		checkEntD1(s, bs)
	}
	s.report(t, fmt.Sprintf("D1 Entry (random encodeWithUF %d + genAdv %d + mutations %d + exhaustive len<=2 + %d random len 3 + 6 targeted)", nRand, nRand, nRand, nLen3))
}

// ---------------- D2 + P2: random contents, the encoder ----------------

func randOptU64(r *rand.Rand) *uint64 {
	if r.Intn(3) == 0 {
		return nil
	}
	return pu(rval(r))
}

func randOptBool(r *rand.Rand) *bool {
	switch r.Intn(3) {
	case 0:
		return nil
	case 1:
		return pbool(1)
	}
	return pbool(0)
}

func randOptEnum(r *rand.Rand, n int) *int32 {
	if r.Intn(3) == 0 {
		return nil
	}
	var v int32
	switch r.Intn(6) {
	case 0, 1, 2:
		v = int32(r.Intn(n))
	case 3:
		v = []int32{-1, math.MinInt32, math.MaxInt32, int32(n), int32(n) + 100}[r.Intn(5)]
	default:
		v = int32(r.Uint32())
	}
	return &v
}

func randOptData(r *rand.Rand) *[]byte {
	switch r.Intn(4) {
	case 0:
		return nil
	case 1:
		return pdat(nil) // present, empty: size 2
	}
	n := r.Intn(40)
	if r.Intn(10) == 0 {
		n = 100 + r.Intn(300) // a two-byte length
	}
	b := make([]byte, n)
	r.Read(b)
	return pdat(b)
}

// randValidUF: unknown fields satisfying ufWire at kind's schema (non-minimal inner and end tags,
// inner numbers up to 2^31-1, outer numbers up to 2^29-1), sometimes a long one.
func randValidUF(t *testing.T, r *rand.Rand, kind string) []byte {
	if r.Intn(3) == 0 {
		return nil
	}
	uf := genUF(r, schemas[kind], ufOpts{innerNumMax: 1<<31 - 1})
	if r.Intn(8) == 0 {
		n := 120 + r.Intn(200)
		uf = protowire.AppendTag(uf, protowire.Number(1000+r.Intn(1000)), 2)
		uf = protowire.AppendBytes(uf, make([]byte, n))
	}
	if why := ufPred(uf, schemas[kind], innerMax, true); why != "" {
		t.Fatalf("generator: %s uf %x violates ufWire: %s", kind, uf, why)
	}
	return uf
}

func randU64s(r *rand.Rand, max int) []uint64 {
	var xs []uint64
	for k := r.Intn(max + 1); k > 0; k-- {
		xs = append(xs, rval(r))
	}
	return xs
}

func randEntC(t *testing.T, r *rand.Rand) entC {
	return entC{term: randOptU64(r), index: randOptU64(r), typ: randOptEnum(r, 3), data: randOptData(r), uf: randValidUF(t, r, "Entry")}
}

func randMsgC(t *testing.T, r *rand.Rand) msgC {
	c := msgC{typ: randOptEnum(r, 24), to: randOptU64(r), from: randOptU64(r), term: randOptU64(r), logTerm: randOptU64(r),
		index: randOptU64(r), commit: randOptU64(r), vote: randOptU64(r), reject: randOptBool(r), rejectHint: randOptU64(r),
		context: randOptData(r), uf: randValidUF(t, r, "Message")}
	for k := r.Intn(5); k > 0; k-- {
		c.entries = append(c.entries, randEntC(t, r))
	}
	if r.Intn(3) != 0 {
		s := &snapC{data: randOptData(r), uf: randValidUF(t, r, "Snapshot")}
		if r.Intn(4) != 0 {
			m := &metaC{index: randOptU64(r), term: randOptU64(r), uf: randValidUF(t, r, "SnapshotMetadata")}
			if r.Intn(4) != 0 {
				m.cs = &csC{voters: randU64s(r, 4), learners: randU64s(r, 3), vout: randU64s(r, 3), lnext: randU64s(r, 2),
					autoLeave: randOptBool(r), uf: randValidUF(t, r, "ConfState")}
			}
			s.meta = m
		}
		c.snap = s
	}
	return c
}

func TestD2P2EntryEncoder(t *testing.T) {
	r := rand.New(rand.NewSource(31))
	const N = nEncEntry
	fails := map[string]int{}
	ex := map[string]string{}
	f := func(k string, c entC) {
		fails[k]++
		if _, ok := ex[k]; !ok {
			ex[k] = c.show()
		}
	}
	nilData, emptyData := 0, 0
	for it := 0; it < N; it++ {
		c := randEntC(t, r)
		if c.data == nil {
			nilData++
		} else if len(*c.data) == 0 {
			emptyData++
		}
		e := toPbEnt(c)
		enc, err := proto.Marshal(e)
		if err != nil {
			f("marshal error", c)
			continue
		}
		if len(enc) != entrySizeC(c) {
			f(fmt.Sprintf("len(Marshal) != entrySize (enc %x)", enc), c)
		}
		if proto.Size(e) != entrySizeC(c) {
			f("proto.Size != entrySize", c)
		}
		var d pb.Entry
		if proto.Unmarshal(enc, &d) != nil {
			f("Unmarshal(Marshal) fails", c)
			continue
		}
		dc := contentOfEnt(&d)
		if dc.show() != c.show() {
			f("Unmarshal(Marshal) content differs", c) // D2 at Entry
		}
		if entGetters(&d) != entModel(c) {
			f("EntWireOk: decoded getters != EntryC.model", c)
		}
		var rc entC
		if !refDecodeEnt(enc, &rc) || rc.show() != c.show() {
			f("reference decode of Marshal differs", c)
		}
	}
	t.Logf("P2/D2 Entry: %d random EntryC (Term/Index/Type presence, Type any int32 incl. negative/out of range, Data nil %d / empty %d / bytes, ufWire uf incl. long and non-minimal inner tags): %d failure kinds", N, nilData, emptyData, len(fails))
	for k, n := range fails {
		t.Errorf("P2 Entry FAIL %s: %d (first: %s)", k, n, ex[k])
	}
}

func TestD2P2MessageEncoder(t *testing.T) {
	r := rand.New(rand.NewSource(32))
	const N = nEncMsg
	fails := map[string]int{}
	ex := map[string]string{}
	f := func(k string, c msgC) {
		fails[k]++
		if _, ok := ex[k]; !ok {
			ex[k] = c.show()
		}
	}
	csNil, csUfNonEmpty, snaps, ents := 0, 0, 0, 0
	for it := 0; it < N; it++ {
		c := randMsgC(t, r)
		if why := ufValidC(c); why != "" {
			t.Fatalf("generator: %s", why)
		}
		if c.snap != nil {
			snaps++
		}
		ents += len(c.entries)
		decOk0 := csUfNil(c)
		if decOk0 {
			csNil++
		} else {
			csUfNonEmpty++
		}
		m := toPbMsg(c)
		enc, err := proto.Marshal(m)
		if err != nil {
			f("marshal error", c)
			continue
		}
		if len(enc) != msgSizeC(c) {
			f(fmt.Sprintf("len(Marshal) %d != msgSize %d", len(enc), msgSizeC(c)), c)
		}
		if proto.Size(m) != msgSizeC(c) {
			f("proto.Size != msgSize", c)
		}
		var d pb.Message
		if proto.Unmarshal(enc, &d) != nil {
			f("Unmarshal(Marshal) fails (D2 success)", c)
			continue
		}
		dc := contentOfMsg(&d)
		if dc.show() != c.show() {
			f("Unmarshal(Marshal) content differs (D2 c = c0)", c)
		}
		if decOk0 && !csUfNil(dc) {
			f("D2: decOk (csUfNil) not preserved", c)
		}
		if msgGetters(&d) != wireModel(c) || len(d.Responses) != 0 {
			f("MsgWireOk: decoded wire model != wireOf (MsgC.model c), or responses", c)
		}
		var rc msgC
		if !refDecodeMsg(enc, &rc) || rc.show() != c.show() {
			f("reference decode of Marshal differs", c)
		}
		// D1 on the encoding too (size <= 2|bs| etc.).
		s := newStats()
		checkMsgD1(s, enc)
		for k := range s.fails {
			f("D1 on Marshal output: "+k, c)
		}
	}
	t.Logf("P2/D2 Message: %d random MsgC (resps empty, ufValid at every level; %d with snapshot, %d entries in all; csUfNil %d / not %d): %d failure kinds", N, snaps, ents, csNil, csUfNonEmpty, len(fails))
	for k, n := range fails {
		t.Errorf("P2 Message FAIL %s: %d (first: %s)", k, n, ex[k])
	}
	// deep groups in uf at every level
	for _, d := range []int{10000, 10001} {
		c := msgC{uf: deepGroup(200, d, true), entries: []entC{{uf: deepGroup(100, d, true)}},
			snap: &snapC{uf: deepGroup(300, d, false), meta: &metaC{uf: deepGroup(301, d, true), cs: &csC{uf: deepGroup(302, d, true)}}}}
		enc, _ := proto.Marshal(toPbMsg(c))
		var dm pb.Message
		err := proto.Unmarshal(enc, &dm)
		okRT := err == nil && contentOfMsg(&dm).show() == c.show()
		t.Logf("P2 Message deep groups %d at every level: len(Marshal)==msgSize %v, exact round trip %v", d, len(enc) == msgSizeC(c), okRT)
		if !okRT || len(enc) != msgSizeC(c) {
			t.Errorf("P2 deep group %d failed", d)
		}
	}
}
