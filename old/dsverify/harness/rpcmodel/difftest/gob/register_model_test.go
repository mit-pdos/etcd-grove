//go:build rpcmodel

package gobdifftest

import (
	"encoding/binary"
	"encoding/gob"
	"errors"
	"sort"
)

// register gives the gob model a codec for Msg (by hand, as a kit's generated one): X, S's
// length and bytes, M's presence, size and entries in key order.
func register() {
	gob.SetCodec(&gob.Codec{Encode: encode, Decode: decode})
}

func encode(v interface{}) []byte {
	var m Msg
	switch x := v.(type) {
	case Msg:
		m = x
	case *Msg:
		m = *x
	default:
		panic("not a Msg")
	}
	b := binary.LittleEndian.AppendUint32(nil, uint32(m.X))
	b = binary.LittleEndian.AppendUint64(b, uint64(len(m.S)))
	b = append(b, m.S...)
	if m.M == nil {
		return append(b, 0)
	}
	b = append(b, 1)
	b = binary.LittleEndian.AppendUint64(b, uint64(len(m.M)))
	var ks []int32
	for k := range m.M {
		ks = append(ks, k)
	}
	sort.Slice(ks, func(i, j int) bool { return ks[i] < ks[j] })
	for _, k := range ks {
		b = binary.LittleEndian.AppendUint32(b, uint32(k))
		b = binary.LittleEndian.AppendUint64(b, uint64(m.M[k]))
	}
	return b
}

var errBad = errors.New("bad Msg")

func decode(b []byte, p interface{}) error {
	mp := p.(*Msg)
	if len(b) < 12 {
		return errBad
	}
	m := Msg{X: int32(binary.LittleEndian.Uint32(b))}
	n := binary.LittleEndian.Uint64(b[4:])
	b = b[12:]
	if uint64(len(b)) < n+1 {
		return errBad
	}
	if n > 0 {
		m.S = append([]byte(nil), b[:n]...)
	}
	b = b[n:]
	if b[0] == 1 {
		if len(b) < 9 {
			return errBad
		}
		k := binary.LittleEndian.Uint64(b[1:])
		b = b[9:]
		m.M = map[int32]int64{}
		for i := uint64(0); i < k; i++ {
			if len(b) < 12 {
				return errBad
			}
			m.M[int32(binary.LittleEndian.Uint32(b))] = int64(binary.LittleEndian.Uint64(b[4:]))
			b = b[12:]
		}
	}
	*mp = m
	return nil
}
