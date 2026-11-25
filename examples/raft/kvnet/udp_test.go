package kvnet

import (
	"bytes"
	"fmt"
	"math/rand"
	"testing"
)

// TestDatagramSize checks that no datagram the transport builds exceeds maxDatagram: the largest
// fragment (the header and a full chunk), an ack, and every fragment of bodies of many lengths.
func TestDatagramSize(t *testing.T) {
	if fragHeaderLen+chunkSize > maxDatagram {
		t.Fatalf("fragment header %d + chunk %d > maxDatagram %d", fragHeaderLen, chunkSize, maxDatagram)
	}
	if len(putAck(1, 2, 3, 4)) != ackLen || ackLen > maxDatagram {
		t.Fatalf("ack length %d", len(putAck(1, 2, 3, 4)))
	}
	for _, n := range []int{1, 2, chunkSize - 1, chunkSize, chunkSize + 1, 3*chunkSize + 7, 100000} {
		body := make([]byte, n)
		ds := fragments(1, 2, 3, 4, body)
		if len(ds) != (n+chunkSize-1)/chunkSize {
			t.Fatalf("body %d: %d fragments", n, len(ds))
		}
		for _, d := range ds {
			if len(d) > maxDatagram {
				t.Fatalf("body %d: a fragment of %d bytes", n, len(d))
			}
		}
	}
	if fragments(1, 2, 3, 4, nil) != nil {
		t.Fatal("fragments of an empty body")
	}
	if fragments(1, 2, 3, 4, make([]byte, maxFragments*chunkSize+1)) != nil {
		t.Fatal("fragments of a body longer than maxFragments chunks")
	}
	if len(fragments(1, 2, 3, 4, make([]byte, maxFragments*chunkSize))) != maxFragments {
		t.Fatal("a body of exactly maxFragments chunks")
	}
}

// TestDatagramCodec checks that getDatagram reads back putFragment's and putAck's datagrams and
// refuses malformed ones.
func TestDatagramCodec(t *testing.T) {
	chunk := []byte("hello")
	b := putFragment(7, 8, 9, 10, 2, 3, chunk)
	d, ok := getDatagram(b)
	if !ok || d.kind != kindFragment || d.from != 7 || d.to != 8 || d.boot != 9 || d.seq != 10 ||
		d.index != 2 || d.total != 3 || !bytes.Equal(d.chunk, chunk) {
		t.Fatalf("fragment read back as %+v, %v", d, ok)
	}
	b[len(b)-1] = 'X' // the chunk is a copy
	if d.chunk[len(chunk)-1] != 'o' {
		t.Fatal("the chunk aliases the datagram")
	}
	a, ok := getDatagram(putAck(1, 2, 1<<63, maxUint64))
	if !ok || a.kind != kindAck || a.from != 1 || a.to != 2 || a.boot != 1<<63 || a.seq != maxUint64 {
		t.Fatalf("ack read back as %+v, %v", a, ok)
	}
	bad := map[string][]byte{
		"empty":           nil,
		"short":           putAck(1, 2, 3, 4)[:ackLen-1],
		"ack, longer":     append(putAck(1, 2, 3, 4), 0),
		"bad magic":       append([]byte{0}, putAck(1, 2, 3, 4)[1:]...),
		"unknown kind":    putHeader(nil, 3, 1, 2, 3, 4),
		"no chunk":        putFragment(1, 2, 3, 4, 0, 1, nil),
		"chunk too long":  putFragment(1, 2, 3, 4, 0, 1, make([]byte, chunkSize+1)),
		"total 0":         putFragment(1, 2, 3, 4, 0, 0, chunk),
		"index = total":   putFragment(1, 2, 3, 4, 3, 3, chunk),
		"total too large": putFragment(1, 2, 3, 4, 0, maxFragments+1, chunk),
		"header only":     putFragment(1, 2, 3, 4, 0, 1, nil)[:fragHeaderLen-1],
	}
	for name, b := range bad {
		if _, ok := getDatagram(b); ok {
			t.Errorf("%s: accepted", name)
		}
	}
	if _, ok := getDatagram(putFragment(1, 2, 3, 4, 0, 1, make([]byte, chunkSize))); !ok {
		t.Error("a full chunk refused")
	}
	// random bytes never crash it, and any it accepts re-encode to themselves
	rnd := rand.New(rand.NewSource(1))
	for i := 0; i < 100000; i++ {
		b := make([]byte, rnd.Intn(80))
		rnd.Read(b)
		if len(b) >= 5 && rnd.Intn(2) == 0 {
			copy(b, putAck(0, 0, 0, 0)[:4])
			b[4] = byte(1 + rnd.Intn(2))
		}
		d, ok := getDatagram(b)
		if !ok {
			continue
		}
		var re []byte
		if d.kind == kindAck {
			re = putAck(d.from, d.to, d.boot, d.seq)
		} else {
			re = putFragment(d.from, d.to, d.boot, d.seq, d.index, d.total, d.chunk)
		}
		if !bytes.Equal(re, b) {
			t.Fatalf("%x read back as %+v", b, d)
		}
	}
}

// TestParseAddr checks parseAddr against AddrOk: it reads back the address of every well-formed
// one, and refuses every other string.
func TestParseAddr(t *testing.T) {
	good := []string{"1.2.3.4:5", "127.0.0.1:7001", "223.255.255.255:65535", "10.0.0.1:61000",
		"192.168.1.200:32767", "100.64.0.9:1"}
	for _, a := range good {
		ip, port, ok := parseAddr(a)
		back := fmt.Sprintf("%d.%d.%d.%d:%d", ip[0], ip[1], ip[2], ip[3], port)
		if !ok || back != a {
			t.Errorf("%s: parsed as %s, %v", a, back, ok)
		}
		ua, ok := udpAddr(a)
		if !ok || ua.String() != a || len(ua.IP) != 4 {
			t.Errorf("%s: UDP address %v, %v", a, ua, ok)
		}
	}
	bad := []string{"", "0.1.2.3:5", "1.2.3.4", "1.2.3.4:0", "1.2.3.4:40000", "01.2.3.4:5",
		"256.1.1.1:5", "a.b.c.d:1", "1.2.3.4:5:6", "1.2.3:4", "1.2.3.4.5:6", "224.0.0.1:5",
		"1.2.3.4:65536", "1.2.3.4:", ":5", "1.2.3.4:005", " 1.2.3.4:5", "1.2.3.4:5 "}
	for _, a := range bad {
		if _, _, ok := parseAddr(a); ok {
			t.Errorf("%q: accepted", a)
		}
		if _, ok := udpAddr(a); ok {
			t.Errorf("%q: a UDP address", a)
		}
	}
	// on random strings over the addresses' alphabet, parseAddr accepts exactly what AddrOk does,
	// and reads back what it accepts
	rnd := rand.New(rand.NewSource(1))
	alphabet := "0123456789.:"
	accepted := 0
	for i := 0; i < 200000; i++ {
		var a string
		if rnd.Intn(2) == 0 {
			a = fmt.Sprintf("%d.%d.%d.%d:%d", rnd.Intn(300), rnd.Intn(300), rnd.Intn(300), rnd.Intn(300), rnd.Intn(70000))
		} else {
			b := make([]byte, rnd.Intn(22))
			for j := range b {
				b[j] = alphabet[rnd.Intn(len(alphabet))]
			}
			a = string(b)
		}
		ip, port, ok := parseAddr(a)
		if ok != AddrOk(a) {
			t.Fatalf("%q: parseAddr %v, AddrOk %v", a, ok, AddrOk(a))
		}
		if ok {
			accepted++
			if back := fmt.Sprintf("%d.%d.%d.%d:%d", ip[0], ip[1], ip[2], ip[3], port); back != a {
				t.Fatalf("%q read back as %q", a, back)
			}
		}
	}
	if accepted < 1000 {
		t.Fatalf("only %d random addresses accepted", accepted)
	}
}

// frags are the fragments of body as message (boot, seq) from 1 to 2, read back.
func frags(t *testing.T, boot, seq uint64, body []byte) []datagram {
	var ds []datagram
	for _, b := range fragments(1, 2, boot, seq, body) {
		d, ok := getDatagram(b)
		if !ok {
			t.Fatal("a fragment does not read back")
		}
		ds = append(ds, d)
	}
	return ds
}

// randomBody is n random bytes.
func randomBody(rnd *rand.Rand, n int) []byte {
	b := make([]byte, n)
	rnd.Read(b)
	return b
}

// TestReassembly checks the reassembler: fragments out of order and duplicated complete their
// message once, with its body; a message missing a fragment never completes and is evicted once
// maxPending later ones start; interleaved messages, and messages of the same sequence number in
// two boots, are never mixed; a fragment of a completed message is a duplicate, and the first
// fragment of a completed snapshot asks for its ack again.
func TestReassembly(t *testing.T) {
	rnd := rand.New(rand.NewSource(2))
	stats := &Stats{}
	r := newReassembler(stats)

	// out of order, with duplicates
	body := randomBody(rnd, 5*chunkSize-3)
	ds := frags(t, 1, 1, body)
	order := []int{3, 0, 3, 4, 1, 0, 2}
	for i, k := range order {
		got, complete, _ := r.add(ds[k])
		if complete != (i == len(order)-1) {
			t.Fatalf("fragment %d (step %d): complete %v", k, i, complete)
		}
		if complete {
			if !bytes.Equal(got, body) {
				t.Fatal("reassembled body differs")
			}
			r.remember(1, msgID{1, 1}, false)
		}
	}
	s := stats.Snapshot()
	if s[StUDPFragmentsDuplicate] != 2 || s[StUDPFragmentsReordered] != 3 || s[StUDPMultiFragment] != 1 {
		t.Fatalf("counters after out of order: %s", FormatStats(s))
	}
	// a fragment of the completed message: a duplicate, no ack (not a snapshot)
	if _, complete, reack := r.add(ds[0]); complete || reack {
		t.Fatal("a completed message completed again")
	}

	// interleaved messages, and the same seq in another boot
	b1, b2, b3 := randomBody(rnd, 3*chunkSize), randomBody(rnd, 2*chunkSize+1), randomBody(rnd, 3*chunkSize-5)
	d1, d2, d3 := frags(t, 1, 2, b1), frags(t, 1, 3, b2), frags(t, 2, 2, b3)
	var all []datagram
	for i := 0; i < 3; i++ {
		all = append(all, d1[i], d3[i])
		if i < len(d2) {
			all = append(all, d2[i])
		}
	}
	rnd.Shuffle(len(all), func(i, j int) { all[i], all[j] = all[j], all[i] })
	got := make(map[msgID][]byte)
	for _, d := range all {
		b, complete, _ := r.add(d)
		if complete {
			id := msgID{d.boot, d.seq}
			if got[id] != nil {
				t.Fatalf("%v completed twice", id)
			}
			got[id] = b
			r.remember(1, id, false)
		}
	}
	if !bytes.Equal(got[msgID{1, 2}], b1) || !bytes.Equal(got[msgID{1, 3}], b2) || !bytes.Equal(got[msgID{2, 2}], b3) {
		t.Fatal("interleaved messages mixed or incomplete")
	}

	// a missing fragment: never complete, evicted once maxPending messages start after it
	lost := frags(t, 3, 1, randomBody(rnd, 3*chunkSize))
	r.add(lost[0])
	r.add(lost[2])
	before := stats.Snapshot()[StUDPReassembliesEvicted]
	for k := uint64(0); k < maxPending; k++ {
		ds := frags(t, 3, 100+k, randomBody(rnd, 2*chunkSize))
		r.add(ds[0])
	}
	if after := stats.Snapshot()[StUDPReassembliesEvicted]; after != before+1 {
		t.Fatalf("evictions %d, want %d", after, before+1)
	}
	// its last fragment now starts it anew, still incomplete
	if _, complete, _ := r.add(lost[1]); complete {
		t.Fatal("an evicted message completed")
	}
	if n := len(r.pending[1]); n > maxPending {
		t.Fatalf("%d messages pending", n)
	}

	// stale messages in progress are evicted by a later completion: one of an earlier boot, and
	// one more than staleLag sequence numbers behind (exactly staleLag behind is not stale)
	r.pending[1] = nil
	old := frags(t, 6, 1, randomBody(rnd, 2*chunkSize))
	behind := frags(t, 7, 2, randomBody(rnd, 2*chunkSize))
	recent := frags(t, 7, 2+staleLag, randomBody(rnd, 2*chunkSize))
	r.add(old[0])
	r.add(behind[0])
	r.add(recent[0])
	before = stats.Snapshot()[StUDPReassembliesEvicted]
	r.remember(1, msgID{7, 2 + staleLag}, false)
	if n := stats.Snapshot()[StUDPReassembliesEvicted] - before; n != 1 || len(r.pending[1]) != 2 {
		t.Fatalf("evicted %d, %d left; want 1, 2", n, len(r.pending[1]))
	}
	r.remember(1, msgID{7, 3 + staleLag}, false)
	r.remember(1, msgID{8, 0}, false)
	if n := stats.Snapshot()[StUDPReassembliesEvicted] - before; n != 3 || len(r.pending[1]) != 0 {
		t.Fatalf("evicted %d, %d left; want 3, 0", n, len(r.pending[1]))
	}

	// a snapshot completed: its first fragment again asks for an ack, its others do not
	snap := frags(t, 4, 1, randomBody(rnd, 2*chunkSize))
	r.add(snap[1])
	if _, complete, _ := r.add(snap[0]); !complete {
		t.Fatal("snapshot incomplete")
	}
	r.remember(1, msgID{4, 1}, true)
	if _, complete, reack := r.add(snap[0]); complete || !reack {
		t.Fatal("a duplicate snapshot's first fragment: no re-ack")
	}
	if _, _, reack := r.add(snap[1]); reack {
		t.Fatal("a duplicate snapshot's second fragment: re-ack")
	}

	// the completed set stays bounded
	for k := uint64(0); k < 3*maxDone; k++ {
		d := frags(t, 5, k, []byte{1})[0]
		if _, complete, _ := r.add(d); !complete {
			t.Fatal("a one-fragment message incomplete")
		}
		r.remember(1, msgID{5, k}, false)
	}
	if len(r.done[1]) > maxDone {
		t.Fatalf("%d completed messages remembered", len(r.done[1]))
	}
	// messages completed out of their order are counted
	r.remember(1, msgID{5, 0}, false)
	if stats.Snapshot()[StUDPMsgsReordered] == 0 {
		t.Fatal("a message completed after a later one not counted")
	}
}

// TestNextBoot checks that each process of a replica gets a boot number one more than the last's,
// from 1.
func TestNextBoot(t *testing.T) {
	dir := t.TempDir()
	for want := uint64(1); want <= 5; want++ {
		if b := nextBoot(dir, 3); b != want {
			t.Fatalf("boot %d, want %d", b, want)
		}
	}
	if b := nextBoot(dir, 4); b != 1 {
		t.Fatalf("another replica's first boot %d", b)
	}
}
