package json

import "io"

// minFree: the free space a Decoder's buffer has beyond twice its length before each read.
const minFree = 8192

// An Encoder writes JSON values to a writer. After a write error it returns that error and
// writes nothing more (Go's).
type Encoder struct {
	w   io.Writer
	err error
}

// NewEncoder returns an encoder that writes to w.
func NewEncoder(w io.Writer) *Encoder {
	return &Encoder{w: w}
}

// Encode writes v's encoding and a newline, in one Write call (Go's).
func (enc *Encoder) Encode(v interface{}) error {
	if enc.err != nil {
		return enc.err
	}
	b, err := Marshal(v)
	if err != nil {
		return err
	}
	b2 := append(b, '\n')
	if _, err2 := enc.w.Write(b2); err2 != nil {
		enc.err = err2
		return err2
	}
	return nil
}

// A Decoder reads and decodes JSON values from a reader, with a buffer of its own: like Go's, it
// may read from the reader beyond the values it decodes, and those bytes are lost with the
// decoder. Each read asks for at least as many bytes as Go's decoder may ask for at that point:
// Go's buffer starts at 64 bytes, grows to at most 4 KiB by throughput and otherwise doubles only
// when a value fills three quarters of it, and never shrinks; the model's never shrinks either,
// and before each read its free space is at least twice the buffered length plus 8 KiB. So every
// amount Go's may read ahead, the model's may (the reader decides how much it returns). Once a
// read error or a syntax error is returned, every later Decode returns it.
type Decoder struct {
	r     io.Reader
	buf   []byte
	scanp int
	rerr  error // a read error not yet reported (it ends the stream after the buffer)
	err   error // the sticky error
}

// NewDecoder returns a decoder that reads from r.
func NewDecoder(r io.Reader) *Decoder {
	return &Decoder{r: r}
}

// refill reads more into the buffer: the unread bytes move to the front, the buffer grows to
// have at least twice its length plus 8 KiB of free space, and one Read fills some of the free
// space; a read error is kept for after the buffer has been scanned.
func (dec *Decoder) refill() {
	n := copy(dec.buf, dec.buf[dec.scanp:])
	dec.buf = dec.buf[:n]
	dec.scanp = 0
	if cap(dec.buf)-len(dec.buf) < 2*len(dec.buf)+minFree {
		nb := make([]byte, len(dec.buf), 3*len(dec.buf)+minFree)
		copy(nb, dec.buf)
		dec.buf = nb
	}
	m, err := dec.r.Read(dec.buf[len(dec.buf):cap(dec.buf)])
	dec.buf = dec.buf[:len(dec.buf)+m]
	dec.rerr = err
}

// Decode reads the next JSON value from the stream and decodes it into v (Go's: io.EOF at the
// end of the stream with only whitespace left, io.ErrUnexpectedEOF in the middle of a value, the
// reader's error otherwise; a syntax error; else the value is consumed and decoded, and a
// decoding error is returned but does not stop the stream).
func (dec *Decoder) Decode(v interface{}) error {
	if dec.err != nil {
		return dec.err
	}
	c := getCodec()
	for {
		rest := dec.buf[dec.scanp:]
		// at the end of the stream (io.EOF) a number at the end of the buffer is complete
		st, n := c.Scan(rest, dec.rerr == io.EOF)
		if st == scanDone {
			data := rest[:n]
			dec.scanp = dec.scanp + int(n)
			return c.Unmarshal(data, v)
		}
		if st != scanMore {
			dec.err = &SyntaxError{msg: "json: invalid JSON input"}
			return dec.err
		}
		if dec.rerr != nil {
			if dec.rerr == io.EOF {
				if allSpace(rest) {
					dec.err = io.EOF
				} else {
					dec.err = io.ErrUnexpectedEOF
				}
			} else {
				dec.err = dec.rerr
			}
			return dec.err
		}
		dec.refill()
	}
}
