package wal

import (
	"github.com/mit-pdos/etcd-grove/examples/lib/durable"
)

// oracle is the tester's reference state, kept in a durable file (lib/durable: written whole,
// atomically and durably) beside the WAL, so that it survives the crashes it checks:
//   - created: wal.Create returned;
//   - cands: the histories the WAL may hold as of the last restart (every image the last restart's
//     read is consistent with); each is fully synced (a restart's image is durable: F-Z), with
//     bounds on the model's unlock and purge positions (unl, pur; WAL W4c, Q3);
//   - since: the operations begun since then (a Save or SaveSnapshot is added before the call);
//   - synced: how many of them are synced (moved at the return of a syncing call);
//   - lastHS: the WAL's last saved hard state (MustSync's reference; the same for every candidate);
//   - opens: the snapshot indexes the Opens since the last restart opened at (each added before
//     its Open).
//
// The history of candidate c is c.h ++ since, its synced mark len(c.h) + synced.
type oracle struct {
	created bool
	cands   []cand
	since   []walOp
	synced  uint64
	lastHS  hardState
	opens   []uint64
}

// cand is a candidate history with the bounds the model's state meets while the WAL holds it:
// its unlock position (WalDur.unl) is at most unl, its purge and read positions (pur, cut) at most
// pur.
type cand struct {
	h   []walOp
	unl uint64
	pur uint64
}

func freshOracle() oracle {
	cands := make([]cand, 0)
	cands = append(cands, cand{h: make([]walOp, 0)})
	return oracle{cands: cands, since: make([]walOp, 0), opens: make([]uint64, 0)}
}

func putU64(b []byte, x uint64) []byte {
	for i := uint64(0); i < 8; i++ {
		b = append(b, byte(x>>(8*i)))
	}
	return b
}

// decoder reads what the encoder wrote; ok goes false past the end.
type decoder struct {
	b   []byte
	off uint64
	ok  bool
}

func (d *decoder) u64() uint64 {
	if d.off+8 > uint64(len(d.b)) {
		d.ok = false
		return 0
	}
	var x uint64
	for i := uint64(0); i < 8; i++ {
		x = x | uint64(d.b[d.off+i])<<(8*i)
	}
	d.off = d.off + 8
	return x
}

func putHS(b []byte, h hardState) []byte {
	return putU64(putU64(putU64(b, h.term), h.vote), h.commit)
}

func (d *decoder) hs() hardState {
	t := d.u64()
	v := d.u64()
	c := d.u64()
	return hardState{term: t, vote: v, commit: c}
}

func putOps(b []byte, h []walOp) []byte {
	b = putU64(b, uint64(len(h)))
	for i := 0; i < len(h); i++ {
		o := h[i]
		if o.snap {
			b = putU64(b, 1)
		} else {
			b = putU64(b, 0)
		}
		b = putHS(b, o.hs)
		b = putU64(putU64(b, o.idx), o.term)
		b = putU64(b, uint64(len(o.ents)))
		for j := 0; j < len(o.ents); j++ {
			e := o.ents[j]
			b = putU64(putU64(putU64(putU64(b, e.index), e.term), e.size), e.salt)
		}
	}
	return b
}

func (d *decoder) ops() []walOp {
	n := d.u64()
	h := make([]walOp, 0)
	for i := uint64(0); i < n && d.ok; i++ {
		var o walOp
		o.snap = d.u64() == 1
		o.hs = d.hs()
		o.idx = d.u64()
		o.term = d.u64()
		ne := d.u64()
		o.ents = make([]entry, 0)
		for j := uint64(0); j < ne && d.ok; j++ {
			idx := d.u64()
			t := d.u64()
			sz := d.u64()
			salt := d.u64()
			o.ents = append(o.ents, entry{index: idx, term: t, size: sz, salt: salt})
		}
		h = append(h, o)
	}
	return h
}

func encodeOracle(o oracle) string {
	b := make([]byte, 0)
	if o.created {
		b = putU64(b, 1)
	} else {
		b = putU64(b, 0)
	}
	b = putU64(b, uint64(len(o.cands)))
	for c := 0; c < len(o.cands); c++ {
		b = putOps(b, o.cands[c].h)
		b = putU64(putU64(b, o.cands[c].unl), o.cands[c].pur)
	}
	b = putOps(b, o.since)
	b = putU64(b, o.synced)
	b = putHS(b, o.lastHS)
	b = putU64(b, uint64(len(o.opens)))
	for i := 0; i < len(o.opens); i++ {
		b = putU64(b, o.opens[i])
	}
	return string(b)
}

// decodeOracle returns false on a malformed file (which durable's atomic writes rule out).
func decodeOracle(s string) (oracle, bool) {
	d := &decoder{b: []byte(s), ok: true}
	var o oracle
	o.created = d.u64() == 1
	nc := d.u64()
	o.cands = make([]cand, 0)
	for c := uint64(0); c < nc && d.ok; c++ {
		h := d.ops()
		unl := d.u64()
		pur := d.u64()
		o.cands = append(o.cands, cand{h: h, unl: unl, pur: pur})
	}
	o.since = d.ops()
	o.synced = d.u64()
	o.lastHS = d.hs()
	no := d.u64()
	o.opens = make([]uint64, 0)
	for i := uint64(0); i < no && d.ok; i++ {
		o.opens = append(o.opens, d.u64())
	}
	return o, d.ok
}

func loadOracle(path string) oracle {
	s, ok := durable.Read(path)
	if !ok {
		return freshOracle()
	}
	o, ok2 := decodeOracle(s)
	if !ok2 {
		panic("walrobust: the oracle file is malformed")
	}
	return o
}

func storeOracle(path string, o oracle) {
	durable.Write(path, encodeOracle(o))
}
