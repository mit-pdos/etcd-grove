package paxos

import "github.com/tchajed/marshal"

// The wire format of a message (the network carries bytes): its five integer
// fields as 8-byte little-endian words, then its value, length-prefixed.
// Negative ints round-trip through uint64.

// marshalMessage encodes m.
func marshalMessage(m message) []byte {
	b := make([]byte, 0, 48+len(m.value))
	b = marshal.WriteInt(b, uint64(m.from))
	b = marshal.WriteInt(b, uint64(m.to))
	b = marshal.WriteInt(b, uint64(m.typ))
	b = marshal.WriteInt(b, uint64(m.n))
	b = marshal.WriteInt(b, uint64(m.prevn))
	b = marshal.WriteLenPrefixedBytes(b, []byte(m.value))
	return b
}

// unmarshalMessage decodes an encoding made by marshalMessage.
func unmarshalMessage(b []byte) message {
	from, b1 := marshal.ReadInt(b)
	to, b2 := marshal.ReadInt(b1)
	typ, b3 := marshal.ReadInt(b2)
	n, b4 := marshal.ReadInt(b3)
	prevn, b5 := marshal.ReadInt(b4)
	value, _ := marshal.ReadLenPrefixedBytes(b5)
	return message{
		from:  int(from),
		to:    int(to),
		typ:   msgType(typ),
		n:     int(n),
		prevn: int(prevn),
		value: string(value),
	}
}
