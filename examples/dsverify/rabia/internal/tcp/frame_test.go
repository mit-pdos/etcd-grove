package tcp

import (
	"bufio"
	"rabia/internal/message"
	"testing"
	"unsafe"
)

// countWriter counts the bytes written to it and keeps the first few.
type countWriter struct {
	n    uint64
	head []byte
}

func (w *countWriter) Write(p []byte) (int, error) {
	if len(w.head) < 8 {
		k := 8 - len(w.head)
		if k > len(p) {
			k = len(p)
		}
		w.head = append(w.head, p[:k]...)
	}
	w.n += uint64(len(p))
	return len(p), nil
}

// A frame's header is its length as a uint32 (BufWrite's own rule: "we first write the length of
// the byte array and then write the actual data", which BufRead reads back as a uint32). A byte
// array of 2^32 bytes or more has no such header: BufWrite must fail and write nothing, not write a
// wrapped length followed by the data (the reader would take the rest of the data as frames: a
// client's put value could carry forged requests). Issue N8.
func TestBufWriteRejectsFrameOver32Bits(t *testing.T) {
	if testing.Short() {
		t.Skip("allocates a 4 GiB slice (never touched)")
	}
	data := make([]byte, 1<<32+1)
	w := &countWriter{}
	bw := bufio.NewWriter(w)
	err := message.BufWrite(bw, data)
	bw.Flush()
	if err == nil {
		t.Fatalf("BufWrite of %d bytes returned nil; wrote %d bytes, header %v", len(data), w.n, w.head)
	}
	if w.n != 0 {
		t.Fatalf("BufWrite failed but wrote %d bytes", w.n)
	}
}

// A command whose encoding is longer than a uint32 length is not written (N8); Command's
// MarshalWriteFlush then returns Flush's error (nil here), as before the workaround G12 (which
// skips the encoding of such a command: the same bytes written, the same result).
func TestCommandMarshalWriteFlushTooLong(t *testing.T) {
	if testing.Short() {
		t.Skip("a 4 GiB string")
	}
	big := make([]byte, 1<<32)
	cmd := &message.Command{CliId: 1, CliSeq: 2, Commands: []string{unsafe.String(&big[0], len(big))}}
	w := &countWriter{}
	bw := bufio.NewWriter(w)
	bw.Write([]byte("abc"))
	err := cmd.MarshalWriteFlush(bw)
	if err != nil || w.n != 3 {
		t.Fatalf("MarshalWriteFlush of a too long command: err %v, wrote %d bytes (want nil, 3)", err, w.n)
	}
}
