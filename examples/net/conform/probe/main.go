// Command probe drives, over real TCP on 127.0.0.1, the patterns of Go's net that stress the
// TCP semantics (GooseLang/Ext/Tcp/Impl.lean), for the conformance traces
// (examples/net/conform/README.md, "The probe"). Each mode is one pattern, repeated:
//
//   - writeclose: a large Write to a slow reader while another goroutine Closes the writer's
//     end (the Write may return k > 0 with net.ErrClosed, the peer reading those bytes);
//   - writeclosewrite: the same with CloseWrite (k > 0 with EPIPE);
//   - resetwrite: the reader Closes with unread input (a reset) during a 1 MiB Write;
//   - killwrite: a child process (this program re-executed) writes 1 MiB Writes to a slow
//     reader and is killed (SIGKILL) inside one; the reader reads on to EOF or an error;
//   - deadlinewrite: a Write past its write deadline (k < len with a timeout), the deadline
//     cleared, the rest written; a Read past a read deadline;
//   - emptywrite: empty Writes on a live end, past a deadline, after CloseWrite, after a reset,
//     after Close; empty Reads; the addresses;
//   - dialthenlisten: a Dial with no listener, then Listen, Dial, Accept, a second Listen of
//     the address, the listener's Close, Accept and Dial after it;
//   - dialtimeout: DialTimeout with tiny timeouts, again and again, while the listener accepts
//     and reads each connection to its end (a connection whose DialTimeout failed may be
//     accepted: abandoned dials).
//
// Each mode listens at its own address, 127.0.0.1:7191-7198 by default (outside the ephemeral
// range, and outside the examples' 71xx: examples/net/README.md). It prints what it saw on
// stdout (counts of outcomes, and any byte a reader read that the writer did not write at
// that position) and exits 0: the conformance checker judges the trace, not the probe. It
// exits 1 only if its own setup fails (a Listen the pattern needs).
package main

import (
	"errors"
	"flag"
	"fmt"
	"io"
	"math/rand"
	"net"
	"os"
	"os/exec"
	"sort"
	"strings"
	"sync"
	"syscall"
	"time"

	"github.com/mit-pdos/etcd-grove/examples/net/conform/events"
)

var modes = []string{"writeclose", "writeclosewrite", "resetwrite", "killwrite", "deadlinewrite",
	"emptywrite", "dialthenlisten", "dialtimeout"}

var (
	mode  = flag.String("mode", "", "the pattern: "+strings.Join(modes, ", "))
	addr  = flag.String("addr", "", "the address to listen at (default: the mode's, 127.0.0.1:7191-7198)")
	iters = flag.Int("iters", 0, "how many times to repeat the pattern (default: the mode's)")
	size  = flag.Int("size", 1<<20, "bytes per large Write")
	dials = flag.Int("dials", 2000, "dialtimeout: how many DialTimeouts")
	iter  = flag.Int("iter", 0, "killwrite-child: the iteration (the stream's pattern)")
)

func main() {
	flag.Parse()
	if *mode == "killwrite-child" {
		killwriteChild()
		return
	}
	idx := -1
	for i, m := range modes {
		if m == *mode {
			idx = i
		}
	}
	if idx < 0 {
		fmt.Fprintf(os.Stderr, "probe: -mode must be one of %s\n", strings.Join(modes, ", "))
		os.Exit(2)
	}
	if *addr == "" {
		*addr = fmt.Sprintf("127.0.0.1:%d", 7191+idx)
	}
	defIters := map[string]int{"writeclose": 6, "writeclosewrite": 6, "resetwrite": 6, "killwrite": 4,
		"deadlinewrite": 4, "emptywrite": 4, "dialthenlisten": 4, "dialtimeout": 1}
	if *iters == 0 {
		*iters = defIters[*mode]
	}
	st := &stats{m: map[string]int{}}
	switch *mode {
	case "writeclose":
		raceWrite(st, false)
	case "writeclosewrite":
		raceWrite(st, true)
	case "resetwrite":
		resetWrite(st)
	case "killwrite":
		killWrite(st)
	case "deadlinewrite":
		deadlineWrite(st)
	case "emptywrite":
		emptyWrite(st)
	case "dialthenlisten":
		dialThenListen(st)
	case "dialtimeout":
		dialTimeout(st)
	}
	st.print(*mode)
}

/* ---- helpers ---- */

type stats struct {
	mu    sync.Mutex
	m     map[string]int
	notes []string
}

func (s *stats) add(k string) {
	s.mu.Lock()
	s.m[k]++
	s.mu.Unlock()
}

func (s *stats) note(format string, args ...any) {
	s.mu.Lock()
	s.notes = append(s.notes, fmt.Sprintf(format, args...))
	s.mu.Unlock()
}

func (s *stats) print(mode string) {
	keys := make([]string, 0, len(s.m))
	for k := range s.m {
		keys = append(keys, k)
	}
	sort.Strings(keys)
	fmt.Printf("%s:\n", mode)
	for _, k := range keys {
		fmt.Printf("  %-48s %d\n", k, s.m[k])
	}
	for _, n := range s.notes {
		fmt.Printf("  note: %s\n", n)
	}
}

func fatal(format string, args ...any) {
	fmt.Fprintf(os.Stderr, "probe: "+format+"\n", args...)
	os.Exit(1)
}

// errClass names err as the stats count it.
func errClass(err error) string {
	var errno syscall.Errno
	switch {
	case err == nil:
		return "nil"
	case err == io.EOF:
		return "EOF"
	case errors.Is(err, net.ErrClosed):
		return "ErrClosed"
	case errors.Is(err, os.ErrDeadlineExceeded):
		return "timeout"
	case errors.As(err, &errno):
		return "errno " + errnoName(errno)
	default:
		return "other: " + err.Error()
	}
}

func errnoName(e syscall.Errno) string {
	switch e {
	case syscall.ECONNRESET:
		return "ECONNRESET"
	case syscall.EPIPE:
		return "EPIPE"
	case syscall.ECONNREFUSED:
		return "ECONNREFUSED"
	case syscall.EADDRINUSE:
		return "EADDRINUSE"
	case syscall.ENOTCONN:
		return "ENOTCONN"
	case syscall.ETIMEDOUT:
		return "ETIMEDOUT"
	}
	return fmt.Sprintf("%d", int(e))
}

// writeClass names a Write's outcome: complete, or partial/none with its error.
func writeClass(k, n int, err error) string {
	switch {
	case err == nil && k == n:
		return "complete"
	case err == nil:
		return fmt.Sprintf("short with no error (%d of %d)", k, n)
	case k > 0:
		return "partial, " + errClass(err)
	default:
		return "none, " + errClass(err)
	}
}

// streamByte is byte off of iteration it's stream: a pattern of period 251 (prime, so no
// shift of one chunk equals another's), different per iteration.
func streamByte(it, off int) byte { return byte((off + 17*it) % 251) }

func pattern(it, off, n int) []byte {
	b := make([]byte, n)
	for i := range b {
		b[i] = streamByte(it, off+i)
	}
	return b
}

// checker checks that what a reader reads is a prefix of the iteration's stream.
type checker struct {
	it, got int
	bad     bool
}

func (c *checker) feed(st *stats, b []byte) {
	for i, x := range b {
		if !c.bad && x != streamByte(c.it, c.got+i) {
			c.bad = true
			st.note("iteration %d: byte %d read is %d, written %d", c.it, c.got+i, x, streamByte(c.it, c.got+i))
		}
	}
	c.got += len(b)
}

// slowRead reads c until an error, in chunks of 64 KiB with a pause after each, after an
// initial pause, checking the bytes; it returns the count and the error that ended it.
func slowRead(st *stats, c net.Conn, it int, first, pause time.Duration) (int, error) {
	time.Sleep(first)
	ck := &checker{it: it}
	buf := make([]byte, 64<<10)
	for {
		n, err := c.Read(buf)
		ck.feed(st, buf[:n])
		if err != nil {
			return ck.got, err
		}
		time.Sleep(pause)
	}
}

func listen(a string) net.Listener {
	l, err := net.Listen("tcp", a)
	if err != nil {
		fatal("listen %s: %v", a, err)
	}
	return l
}

// pair dials l's address and accepts the connection.
func pair(l net.Listener, a string) (cli, srv net.Conn, ok bool) {
	type res struct {
		c   net.Conn
		err error
	}
	ch := make(chan res, 1)
	go func() {
		c, err := l.Accept()
		ch <- res{c, err}
	}()
	cli, err := net.Dial("tcp", a)
	if err != nil {
		l.Close() // wakes the Accept (the probe's run is then over)
		<-ch
		return nil, nil, false
	}
	r := <-ch
	if r.err != nil {
		cli.Close()
		return nil, nil, false
	}
	return cli, r.c, true
}

/* ---- filling the buffers ---- */

// fill writes the iteration's stream to cli in 256 KiB Writes, each under a 20 ms write
// deadline (well past the tracer's cost of recording the Write), until one times out: the socket buffers are then full (the reader is not reading),
// so the next large Write blocks at once. It returns the stream's length so far.
func fill(st *stats, cli net.Conn, it int) int {
	off := 0
	for i := 0; ; i++ {
		chunk := pattern(it, off, 256<<10)
		cli.SetWriteDeadline(time.Now().Add(20 * time.Millisecond))
		k, err := cli.Write(chunk)
		off += k
		if err != nil {
			if !errors.Is(err, os.ErrDeadlineExceeded) {
				st.add("fill ended by " + errClass(err))
			}
			break
		}
		if i > 400 {
			st.add("fill: the buffers never filled")
			break
		}
	}
	cli.SetWriteDeadline(time.Time{})
	return off
}

// gatedRead waits for gate, then reads c slowly until an error (slowRead).
func gatedRead(st *stats, c net.Conn, it int, gate chan struct{}, pause time.Duration, got *int, rerr *error) {
	<-gate
	*got, *rerr = slowRead(st, c, it, 0, pause)
}

/* ---- writeclose, writeclosewrite ---- */

func raceWrite(st *stats, closeWrite bool) {
	l := listen(*addr)
	defer l.Close()
	what := "Close"
	if closeWrite {
		what = "CloseWrite"
	}
	for it := 0; it < *iters; it++ {
		cli, srv, ok := pair(l, *addr)
		if !ok {
			st.add("pair failed")
			return
		}
		gate := make(chan struct{})
		var wg sync.WaitGroup
		var got int
		var rerr error
		wg.Add(2)
		go func() {
			defer wg.Done()
			gatedRead(st, srv, it, gate, 2*time.Millisecond, &got, &rerr)
		}()
		off := fill(st, cli, it)
		buf := pattern(it, off, *size)
		go func() {
			defer wg.Done()
			<-gate
			time.Sleep(time.Duration(2+rand.Intn(30)) * time.Millisecond)
			if closeWrite {
				cli.(*net.TCPConn).CloseWrite()
			} else {
				cli.Close()
			}
		}()
		close(gate)
		k, err := cli.Write(buf)
		wg.Wait()
		cli.Close()
		srv.Close()
		st.add("Write racing " + what + ": " + writeClass(k, *size, err))
		st.add("reader ended by " + errClass(rerr))
		switch {
		case got > off+k:
			st.note("iteration %d: the reader read %d bytes of the racing Write, which returned %d (%s)", it, got-off, k, errClass(err))
			st.add("reader read more than the Write's count")
		case err != nil && k > 0 && got == off+k:
			st.add("reader read exactly the failed Write's count")
		case err != nil && k > 0:
			st.add("reader read less than the failed Write's count")
		}
	}
}

/* ---- resetwrite ---- */

func resetWrite(st *stats) {
	l := listen(*addr)
	defer l.Close()
	for it := 0; it < *iters; it++ {
		cli, srv, ok := pair(l, *addr)
		if !ok {
			st.add("pair failed")
			return
		}
		off := fill(st, cli, it)
		buf := pattern(it, off, *size)
		done := make(chan int)
		go func() {
			// Read slowly for a while, then Close with unread input: Linux sends a reset.
			ck := &checker{it: it}
			rb := make([]byte, 64<<10)
			stop := time.Now().Add(time.Duration(2+rand.Intn(20)) * time.Millisecond)
			for time.Now().Before(stop) {
				n, err := srv.Read(rb)
				ck.feed(st, rb[:n])
				if err != nil {
					break
				}
				time.Sleep(time.Millisecond)
			}
			srv.Close()
			done <- ck.got
		}()
		k, err := cli.Write(buf)
		got := <-done
		st.add("1 MiB Write under a reset: " + writeClass(k, *size, err))
		if got > off+k {
			st.add("reader read more than the Write's count")
		}
		k2, err2 := cli.Write([]byte("after"))
		st.add("next Write: " + writeClass(k2, 5, err2))
		rb := make([]byte, 16)
		n, rerr := cli.Read(rb)
		st.add(fmt.Sprintf("writer's Read: n=%d %s", n, errClass(rerr)))
		n, rerr = cli.Read(rb)
		st.add(fmt.Sprintf("writer's second Read: n=%d %s", n, errClass(rerr)))
		cli.Close()
	}
}

/* ---- killwrite ---- */

func killWrite(st *stats) {
	l := listen(*addr)
	defer l.Close()
	var log *events.Log
	node := os.Getenv("NETTCP_NODE")
	if node == "" {
		node = "probe"
	}
	child := node + ".writer"
	if dir := os.Getenv("NETTCP_TRACE_DIR"); dir != "" {
		var err error
		if log, err = events.Open(dir, node); err != nil {
			fatal("events: %v", err)
		}
		defer log.Close()
	}
	self, err := os.Executable()
	if err != nil {
		fatal("%v", err)
	}
	for it := 0; it < *iters; it++ {
		cmd := exec.Command(self, "-mode", "killwrite-child", "-addr", *addr, "-size", fmt.Sprint(*size), "-iter", fmt.Sprint(it))
		cmd.Env = append(os.Environ(), "NETTCP_NODE="+child)
		cmd.Stderr = os.Stderr
		if err := cmd.Start(); err != nil {
			fatal("start the writer: %v", err)
		}
		log.Start(child, cmd.Process, self)
		waited := make(chan struct{})
		go func() {
			cmd.Wait()
			log.Exit(child, cmd.Process.Pid, cmd.ProcessState)
			close(waited)
		}()
		type res struct {
			c   net.Conn
			err error
		}
		ch := make(chan res, 1)
		go func() { c, err := l.Accept(); ch <- res{c, err} }()
		var srv net.Conn
		select {
		case r := <-ch:
			if r.err != nil {
				fatal("accept: %v", r.err)
			}
			srv = r.c
		case <-waited:
			st.add("writer exited before its connection was accepted")
			continue
		}
		// Let the writer fill the buffers and block inside a Write, read some slowly, kill it.
		time.Sleep(100 * time.Millisecond)
		ck := &checker{it: it}
		buf := make([]byte, 64<<10)
		for ck.got < 256<<10 {
			n, err := srv.Read(buf)
			ck.feed(st, buf[:n])
			if err != nil {
				st.add("reader ended before the kill: " + errClass(err))
				break
			}
			time.Sleep(2 * time.Millisecond)
		}
		select {
		case <-waited:
		default:
			log.Kill(child, cmd.Process.Pid)
			cmd.Process.Kill()
		}
		<-waited
		var rerr error
		for {
			n, err := srv.Read(buf)
			ck.feed(st, buf[:n])
			if err != nil {
				rerr = err
				break
			}
		}
		srv.Close()
		st.add("reader after the kill ended by " + errClass(rerr))
		if cmd.ProcessState != nil {
			if ws, ok := cmd.ProcessState.Sys().(syscall.WaitStatus); ok && ws.Signaled() {
				st.add("writer killed")
			} else {
				st.add(fmt.Sprintf("writer exited %d", cmd.ProcessState.ExitCode()))
			}
		}
		if ck.got%*size != 0 {
			st.add("reader read part of a Write")
		}
	}
}

// killwriteChild dials and writes the iteration's stream in Writes of -size bytes until a
// Write fails (or the process is killed).
func killwriteChild() {
	c, err := net.Dial("tcp", *addr)
	if err != nil {
		os.Exit(0)
	}
	for j := 0; ; j++ {
		if _, err := c.Write(pattern(*iter, j**size, *size)); err != nil {
			os.Exit(0)
		}
	}
}

/* ---- deadlinewrite ---- */

func deadlineWrite(st *stats) {
	l := listen(*addr)
	defer l.Close()
	for it := 0; it < *iters; it++ {
		cli, srv, ok := pair(l, *addr)
		if !ok {
			st.add("pair failed")
			return
		}
		gate := make(chan struct{})
		var wg sync.WaitGroup
		var got int
		var rerr error
		wg.Add(1)
		go func() {
			defer wg.Done()
			gatedRead(st, srv, it, gate, time.Millisecond, &got, &rerr)
		}()
		off := fill(st, cli, it)
		buf := pattern(it, off, *size)
		close(gate)
		cli.SetWriteDeadline(time.Now().Add(time.Duration(10+rand.Intn(10)) * time.Millisecond))
		k, err := cli.Write(buf)
		st.add("Write past its deadline: " + writeClass(k, *size, err))
		cli.SetWriteDeadline(time.Time{})
		k2, err2 := cli.Write(buf[k:])
		st.add("the rest, deadline cleared: " + writeClass(k2, *size-k, err2))
		cli.SetReadDeadline(time.Now().Add(3 * time.Millisecond))
		n, err3 := cli.Read(make([]byte, 8))
		st.add(fmt.Sprintf("Read past its deadline: n=%d %s", n, errClass(err3)))
		cli.SetDeadline(time.Time{})
		cli.(*net.TCPConn).CloseWrite()
		wg.Wait()
		st.add("reader ended by " + errClass(rerr))
		if got == off+*size {
			st.add("reader read the whole stream")
		} else {
			st.note("iteration %d: the reader read %d of %d", it, got, off+*size)
		}
		srv.Close()
		cli.Close()
	}
}

/* ---- emptywrite ---- */

func emptyWrite(st *stats) {
	l := listen(*addr)
	defer l.Close()
	try := func(what string, c net.Conn) {
		k, err := c.Write(nil)
		st.add(fmt.Sprintf("%s: (%d, %s)", what, k, errClass(err)))
	}
	for it := 0; it < *iters; it++ {
		l.Addr()
		cli, srv, ok := pair(l, *addr)
		if !ok {
			st.add("pair failed")
			return
		}
		cli.LocalAddr()
		cli.RemoteAddr()
		srv.LocalAddr()
		srv.RemoteAddr()
		try("empty Write, live", cli)
		try("empty Write, live, acceptor's end", srv)
		n, err := srv.Read(nil)
		st.add(fmt.Sprintf("empty Read, live: (%d, %s)", n, errClass(err)))
		cli.SetWriteDeadline(time.Now().Add(-time.Second))
		try("empty Write, expired deadline", cli)
		cli.SetWriteDeadline(time.Time{})
		cli.(*net.TCPConn).CloseWrite()
		try("empty Write, after CloseWrite", cli)
		n, err = srv.Read(make([]byte, 4))
		st.add(fmt.Sprintf("peer's Read after CloseWrite: (%d, %s)", n, errClass(err)))
		cli.Close()
		try("empty Write, after Close", cli)
		n, err = cli.Read(nil)
		st.add(fmt.Sprintf("empty Read, after Close: (%d, %s)", n, errClass(err)))
		cli.LocalAddr()
		srv.Close()

		// A reset: the peer Closes with unread input.
		cli, srv, ok = pair(l, *addr)
		if !ok {
			st.add("pair failed")
			return
		}
		cli.Write([]byte("unread"))
		time.Sleep(5 * time.Millisecond)
		srv.Close()
		time.Sleep(5 * time.Millisecond)
		try("empty Write, after a reset", cli)
		try("empty Write, after a reset, again", cli)
		k, err := cli.Write([]byte("x"))
		st.add(fmt.Sprintf("Write after a reset: (%d, %s)", k, errClass(err)))
		cli.Close()
	}
}

/* ---- dialthenlisten ---- */

func dialThenListen(st *stats) {
	for it := 0; it < *iters; it++ {
		c, err := net.Dial("tcp", *addr)
		st.add("Dial, no listener: " + errClass(err))
		if c != nil {
			c.Close()
		}
		c, err = net.DialTimeout("tcp", *addr, time.Second)
		st.add("DialTimeout, no listener: " + errClass(err))
		if c != nil {
			c.Close()
		}
		l := listen(*addr)
		l2, err := net.Listen("tcp", *addr)
		st.add("second Listen: " + errClass(err))
		if l2 != nil {
			l2.Close()
		}
		cli, srv, ok := pair(l, *addr)
		if !ok {
			st.add("pair failed")
			l.Close()
			continue
		}
		cli.Write([]byte("hi"))
		buf := make([]byte, 8)
		n, err := srv.Read(buf)
		st.add(fmt.Sprintf("Read: n=%d %s", n, errClass(err)))
		cli.Close()
		n, err = srv.Read(buf)
		st.add(fmt.Sprintf("Read after the peer's Close: n=%d %s", n, errClass(err)))
		srv.Close()
		// A connection left pending at the listener's Close.
		pend, err := net.Dial("tcp", *addr)
		st.add("Dial, never accepted: " + errClass(err))
		st.add("listener Close: " + errClass(l.Close()))
		if pend != nil {
			n, err = pend.Read(buf)
			st.add(fmt.Sprintf("Read of a connection pending at the listener's Close: n=%d %s", n, errClass(err)))
			pend.Close()
		}
		_, err = l.Accept()
		st.add("Accept after Close: " + errClass(err))
		st.add("listener Close again: " + errClass(l.Close()))
		c, err = net.Dial("tcp", *addr)
		st.add("Dial after the listener's Close: " + errClass(err))
		if c != nil {
			c.Close()
		}
	}
}

/* ---- dialtimeout ---- */

func dialTimeout(st *stats) {
	l := listen(*addr)
	var wg sync.WaitGroup
	wg.Add(1)
	go func() {
		defer wg.Done()
		for {
			c, err := l.Accept()
			if err != nil {
				return
			}
			st.add("accepted")
			wg.Add(1)
			go func() {
				defer wg.Done()
				defer c.Close()
				buf := make([]byte, 16)
				first := true
				for {
					n, err := c.Read(buf)
					if first {
						first = false
						switch {
						case n > 0:
							st.add("accepted, first Read: data")
						default:
							st.add("accepted, first Read: " + errClass(err))
						}
					}
					if err != nil {
						return
					}
				}
			}()
		}
	}()
	for it := 0; it < *iters; it++ {
		for i := 0; i < *dials; i++ {
			to := time.Duration(1+rand.Intn(300)) * time.Microsecond
			c, err := net.DialTimeout("tcp", *addr, to)
			if err != nil {
				st.add("DialTimeout failed: " + errClass(err))
				continue
			}
			st.add("DialTimeout succeeded")
			c.Write([]byte{'D'})
			c.Close()
		}
	}
	time.Sleep(200 * time.Millisecond)
	l.Close()
	wg.Wait()
}
