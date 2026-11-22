// Package remote runs a test's clients on machines of their own (dsverify-lab's design,
// notes/clients-separate-nodes.md there; this port: notes/remote-port-plan.md). The orchestrator
// (node 0) runs lintest.s driver: client c's operations are calls to client node c (Do), which runs
// them with its own client of the system under test (ServeClient) and answers. The history is
// recorded and checked by porcupine on node 0 (Run, Check). No client shares a process with
// another, so no proof can rely on one observer of several clients' steps.
//
// Calls behave as an etcd client's: a write gets one attempt, and if it gets no answer its outcome
// is unknown (it may have taken effect, may take effect later, or never), reported as the model's
// unknown output (Codec.Unknown), which the model treats as a pending write; a read may be retried
// (ReadTries attempts). A node that serves calls (Serve) runs each request it reads whole once, to
// completion, and answers on the connection that carried it; a cut connection loses the answer,
// never repeats the operation.
//
// The wire: one TCP connection per attempt, carrying one request and at most one reply, each a
// frame: an 8-byte little-endian length, then the body (kvnet's format). The request's body is
// the input's encoding, the reply's the output's (Codec).
package remote

import (
	"net"
	"time"

	"github.com/anishathalye/porcupine"
	"github.com/goose-lang/primitive"
	"github.com/mit-pdos/etcd-grove/examples/lib/lintest"
	"github.com/mit-pdos/etcd-grove/examples/lib/lintest/perclient"
)

// Codec is a model's inputs and outputs as bytes (Dec* is false on bytes that are not an
// encoding), which inputs are reads (a read may be retried; a write may not), the model's
// unknown output for an input (the output of an operation whose outcome is unknown: e.g.
// txnlin's Output{Err: true}), and which outputs are unknown ones.
type Codec struct {
	EncIn     func(any) []byte
	DecIn     func([]byte) (any, bool)
	EncOut    func(any) []byte
	DecOut    func([]byte) (any, bool)
	IsRead    func(any) bool
	Unknown   func(any) any
	IsUnknown func(any) bool
}

// MaxLen bounds a frame's body: a reader drops a connection that announces a longer one, and
// Do never sends a longer request (it waits forever instead).
const MaxLen uint64 = 1 << 20

// ReadTries is how many attempts a read gets.
const ReadTries = 3

// RetryMs is how long Serve waits before it retries a failed Listen.
const RetryMs = 100

func putU64(b []byte, x uint64) {
	for i := uint64(0); i < 8; i++ {
		b[i] = byte(x >> (8 * i))
	}
}

func getU64(b []byte) uint64 {
	x := uint64(0)
	for i := uint64(0); i < 8; i++ {
		x = x | (uint64(b[i]) << (8 * i))
	}
	return x
}

// writeAll writes all of b to c; false on an error.
func writeAll(c net.Conn, b []byte) bool {
	for len(b) != 0 {
		n, err := c.Write(b)
		if err != nil {
			return false
		}
		b = b[n:]
	}
	return true
}

// readFull reads exactly len(buf) bytes from c into buf (io.ReadFull's loop); false on any error
// before buf is full, the connection's end included.
func readFull(c net.Conn, buf []byte) bool {
	n := 0
	for n < len(buf) {
		k, err := c.Read(buf[n:])
		n += k
		if err != nil {
			return n == len(buf)
		}
	}
	return true
}

// writeFrame writes body to c as one frame.
func writeFrame(c net.Conn, body []byte) bool {
	b := make([]byte, 8+len(body))
	putU64(b, uint64(len(body)))
	copy(b[8:], body)
	return writeAll(c, b)
}

// readFrame reads one frame from c and returns its body; false on an error, the connection's
// end, or a length past MaxLen.
func readFrame(c net.Conn) ([]byte, bool) {
	hdr := make([]byte, 8)
	if !readFull(c, hdr) {
		return nil, false
	}
	n := getU64(hdr)
	if n > MaxLen {
		return nil, false
	}
	b := make([]byte, n)
	if !readFull(c, b) {
		return nil, false
	}
	return b, true
}

// hang never returns.
func hang() {
	for {
	}
}

// deadline is d from now.
func deadline(d time.Duration) time.Time {
	return time.Now().Add(d)
}

// attempt is one try of a call: it dials addr, sends the request req and reads the reply, all
// within d; false on any failure.
func attempt(addr string, req []byte, d time.Duration) ([]byte, bool) {
	c, err := net.DialTimeout("tcp", addr, d)
	if err != nil {
		return nil, false
	}
	c.SetDeadline(deadline(d))
	var rep []byte
	ok := writeFrame(c, req)
	if ok {
		rep, ok = readFrame(c)
	}
	c.Close()
	return rep, ok
}

// Do runs one operation, with input in, at the node listening at addr (Serve), each attempt
// within d. A write gets one attempt, a read ReadTries (codec.IsRead). It returns the output the
// node answered, or codec.Unknown(in) if no attempt got an answer that decodes. A request longer
// than MaxLen is never sent: Do then never returns.
//
// The prophecies do nothing in Go; the proof of the caller's linearizability needs them. p says
// which attempt answered with a known output (tries: none, or the answer was the unknown output):
// the commit of an operation whose outcome will be unknown is made before the operation is sent,
// and the commit of one that will be answered by the far side's. q says the bytes of that answer
// (their count, then each byte): the far side may fire a read's update several times, at
// different states, and the read commits at the first firing whose output encodes to those bytes
// (notes/specs-only/ledger.md, 2026-11-22, "remote.opMaybe's read form").
func Do(addr string, in any, codec Codec, d time.Duration) any {
	req := codec.EncIn(in)
	if uint64(len(req)) > MaxLen {
		hang()
	}
	tries := 1
	if codec.IsRead(in) {
		tries = ReadTries
	}
	p := primitive.NewProph()
	q := primitive.NewProph()
	for k := 0; k < tries; k++ {
		rep, ok := attempt(addr, req, d)
		if ok {
			out, good := codec.DecOut(rep)
			if good {
				if codec.IsUnknown(out) {
					p.ResolveU64(uint64(tries))
				} else {
					p.ResolveU64(uint64(k))
					q.ResolveU64(uint64(len(rep)))
					for j := 0; j < len(rep); j++ {
						q.ResolveU64(uint64(rep[j]))
					}
				}
				return out
			}
		}
	}
	p.ResolveU64(uint64(tries))
	return codec.Unknown(in)
}

// Report runs one operation with input in at the node listening at addr (Serve), in one attempt
// within d, and returns the output the node answered and true; false if the attempt got no answer
// that decodes (the operation may then have run, may still be running, or never run). It is for
// an operation whose output is a report the caller checks itself, not a model's output: a client's
// loop run on its own machine and what it saw (a writer's log of its successful Puts). No model, no
// prophecy, no retry (the loop writes). codec.IsRead, Unknown and IsUnknown are not used. A request
// longer than MaxLen is never sent: Report then never returns.
func Report(addr string, in any, codec Codec, d time.Duration) (any, bool) {
	req := codec.EncIn(in)
	if uint64(len(req)) > MaxLen {
		hang()
	}
	rep, ok := attempt(addr, req, d)
	if !ok {
		return nil, false
	}
	return codec.DecOut(rep)
}

// listen listens at addr, retrying a failed Listen.
func listen(addr string) net.Listener {
	l, err := net.Listen("tcp", addr)
	for err != nil {
		time.Sleep(time.Duration(RetryMs) * time.Millisecond)
		l, err = net.Listen("tcp", addr)
	}
	return l
}

// serveConn serves one connection: it reads a request whole (within d), runs op on it once and
// writes the reply (within d of op's end), then closes. A request that does not arrive whole, or
// does not decode, is not run; an output whose encoding is longer than MaxLen is not sent.
func serveConn(c net.Conn, sys any, op func(any, any) any, codec Codec, d time.Duration) {
	c.SetDeadline(deadline(d))
	req, ok := readFrame(c)
	if ok {
		in, good := codec.DecIn(req)
		if good {
			out := op(sys, in)
			rep := codec.EncOut(out)
			if uint64(len(rep)) <= MaxLen {
				c.SetDeadline(deadline(d))
				writeFrame(c, rep)
			}
		}
	}
	c.Close()
}

// Serve is a node that serves calls: it listens at addr (retrying a failed Listen) and serves the
// connections one at a time, each request with op(sys, in) (serveConn). It never returns.
func Serve(addr string, sys any, op func(any, any) any, codec Codec, d time.Duration) {
	l := listen(addr)
	for {
		c, err := l.Accept()
		if err == nil {
			serveConn(c, sys, op, codec, d)
		}
	}
}

// ServeClient is client node c's program: sys := newClient(c) (its own client of the system),
// then Serve at addr with op.
func ServeClient(c int, addr string, newClient func(int) any, op func(any, any) any, codec Codec,
	d time.Duration) {
	sys := newClient(c)
	Serve(addr, sys, op, codec, d)
}

// Run is the orchestrator: lintest's driver (perclient.Run) with len(addrs) clients of ops
// operations each, inputs from gen, client c's operations made at client node c (addrs[c]) by
// Do, the history traced with a counter clock and checked by porcupine against model within
// timeout (none if timeout <= 0).
func Run(model porcupine.Model, addrs []string, codec Codec, gen func(int) any, ops int,
	d time.Duration, timeout time.Duration) porcupine.CheckResult {
	apply := func(c int, in any) any {
		return Do(addrs[c], in, codec, d)
	}
	return perclient.Run(model, apply, gen, lintest.CounterClock(), len(addrs), ops, timeout)
}

// Check is Run with no timeout: it panics unless porcupine accepts the history (the theorem:
// it never panics).
func Check(model porcupine.Model, addrs []string, codec Codec, gen func(int) any, ops int,
	d time.Duration) {
	if Run(model, addrs, codec, gen, ops, d, 0) != porcupine.Ok {
		panic("remote: porcupine rejected the history")
	}
}
