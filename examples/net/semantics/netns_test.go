//go:build linux && amd64

package semantics

import (
	"bytes"
	"fmt"
	"io"
	"math/rand/v2"
	"net"
	"strings"
	"sync"
	"sync/atomic"
	"syscall"
	"testing"
	"time"
)

// Network faults, between two network namespaces joined through a router
// namespace (netns_helpers_test.go: the topology, the faults as iptables
// rules in the router's FORWARD chain, the gate NET_NETNS=1 and the
// re-execution as root by sudo -n). Run them with
//
//	cd examples && NET_NETNS=1 go test ./net/semantics/ -count=3 \
//	    -run 'TestTimeoutOnBreak|TestResetInNetwork|TestPartitionHealed|TestAcceptOrder'
//
// Each test logs one EVIDENCE line per case: the decisions, the outcome
// observed, and whether the model (GooseLang/Ext/Net/Impl.lean, v2.1, with
// notes/net-tcp-v3-plan.md's E1 error kinds) allows it.

// breakCase is one way of making the client's kernel give up on a
// partitioned connection.
type breakCase struct {
	name  string
	setup func(t *testing.T, d *net.TCPConn)
	// first is the client's call that is blocked when the kernel gives up
	first string // "read" (after a small Write left unacknowledged) or "write" (a large Write)
}

// TestTimeoutOnBreak (D1, D2, E1; E9). The client's kernel gives up on an
// established connection that a partition (every packet dropped in the
// router, both ways) cut off, three ways:
//
//   - TCP_USER_TIMEOUT 2000 ms, a 14-byte Write left unacknowledged, the
//     client blocked in a Read with no deadline;
//   - TCP_USER_TIMEOUT 2000 ms, the client blocked in a 16 MiB Write;
//   - keepalive (idle 1 s, interval 1 s, count 2), nothing in flight, the
//     client blocked in a Read with no deadline.
//
// Measured (each case): the blocked call returns syscall.ETIMEDOUT as an
// *net.OpError wrapping an *os.SyscallError ("read" or "write"), Timeout()
// true and Temporary() true, errors.Is(err, os.ErrDeadlineExceeded) false
// (tcp_write_err: sk_err ETIMEDOUT, the socket done). The blocked Read returns
// after 2.4-2.5 s (user timeout: the first retransmission after 2 s) or 3.1 s
// (keepalive: idle + 2 probes); the blocked Write returns (110048, ETIMEDOUT)
// after 2.2 s, every run (tcp_sendmsg returns the bytes copied; Go's write
// loop's next write(2) gets the error). The Write before the Read case's break returned (14, nil): those
// bytes never arrive. After the error, every Read returns EOF and every Write
// (0, EPIPE): the error is taken once (sock_error), the socket is shut both
// ways. The peer saw nothing during the partition (its Read with a 200 ms
// deadline: timeout); once it is healed, the peer's Write returns nil (its
// segment draws a RST from the client's kernel, which has no socket for it
// any more), then its Read returns ECONNRESET and then EOF, and its next
// Write (0, EPIPE).
//
// Model: allowed. The client's Read: D1's break at a read (the direction
// towards the client cut, keeping the empty prefix) answering an error; its
// Write: D2's "a prefix, shorter, appended and the connection broken, with an
// error"; the later EOF: D1 on a cut empty direction; the later EPIPE: D2's
// break (the client's own direction, still open in the model) and then D2's
// "into a cut direction: discarded, success or an error". The peer's timeout:
// D1/D5 (a read deadline set); its Write's nil: D2 into a cut direction
// (discarded) or into an open one (appended, the read side later truncates by
// D1's break); its ECONNRESET then EOF: D1's break keeping the empty prefix
// (the 14 bytes the client's Write "sent" are lost). E1: ETIMEDOUT is of kind
// sys (*os.SyscallError), with Timeout() true: "arbitrary" for sys is needed,
// "Timeout() true only for deadlines" would be refuted.
func TestTimeoutOnBreak(t *testing.T) {
	netnsTest(t, func(t *testing.T, n *netnsTopo) {
		userTO := func(t *testing.T, d *net.TCPConn) { setUserTimeout(t, d, 2000) }
		cases := []breakCase{
			{"TCP_USER_TIMEOUT 2s, Read blocked, 14 bytes unacknowledged", userTO, "read"},
			{"TCP_USER_TIMEOUT 2s, Write of 16 MiB blocked", userTO, "write"},
			{"keepalive idle 1s interval 1s count 2, Read blocked, nothing in flight",
				func(t *testing.T, d *net.TCPConn) {
					if err := d.SetKeepAliveConfig(net.KeepAliveConfig{Enable: true,
						Idle: time.Second, Interval: time.Second, Count: 2}); err != nil {
						t.Fatal(err)
					}
				}, "read"},
		}
		for _, c := range cases {
			timeoutOnBreak(t, n, c)
		}
	})
}

func timeoutOnBreak(t *testing.T, n *netnsTopo, c breakCase) {
	d, a := n.pair(t)
	c.setup(t, d)
	heal := n.partition(t)
	start := time.Now()
	var pre string
	type res struct {
		k   int
		err error
	}
	done := make(chan res, 1)
	const big = 16 << 20
	switch c.first {
	case "read":
		if strings.Contains(c.name, "unacknowledged") {
			pre = "Write(14 bytes) " + writeRes(d, "unacknowledged") + "; "
		}
		go func() { k, err := d.Read(make([]byte, 64)); done <- res{k, err} }()
	case "write":
		go func() { k, err := d.Write(make([]byte, big)); done <- res{k, err} }()
	}
	var r res
	select {
	case r = <-done:
	case <-time.After(20 * time.Second):
		t.Fatalf("%s: the blocked %s did not return within 20 s", c.name, c.first)
	}
	took := time.Since(start)
	// what the client sees after the error
	var later []string
	for i := 0; i < 2; i++ {
		later = append(later, "Read "+reads(d, guard, 1))
	}
	for i := 0; i < 2; i++ {
		later = append(later, "Write "+writeRes(d, "more"))
	}
	// the peer, during the partition and after it is healed
	peerDuring := reads(a, 200*time.Millisecond, 3)
	heal()
	peerW := writeRes(a, "reply")
	waitFor(t, "the peer's socket to be reset", func() bool { return tcpState(t, a) == tcpClose })
	peerAfter := reads(a, guard, 4)
	peerW2 := writeRes(a, "reply2")

	outcome := fmt.Sprintf("%s%s blocked: returned after %.1fs (%d, %s) [%s]; then %s; peer: during the partition reads %q; healed: Write %s, reads %q, Write %s",
		pre, c.first, took.Seconds(), r.k, short(r.err), chain(r.err), strings.Join(later, ", "),
		peerDuring, peerW, peerAfter, peerW2)
	evidence(t, "D1,D2,E1 ("+c.name+")", outcome,
		"allowed (client: D1/D2 break with an error, then EOF on the cut direction and EPIPE as D2's break; peer: D5 timeout, D2 write discarded, D1 break: ECONNRESET then EOF; E1: sys, Timeout() arbitrary)")

	// What the model's soundness rests on (E1): the error is of kind sys, and
	// not a deadline's, although Timeout() is true.
	if e, ok := sysErrno(r.err); !ok || e != syscall.ETIMEDOUT {
		t.Errorf("%s: the blocked %s returned %s; want ETIMEDOUT in *net.OpError > *os.SyscallError", c.name, c.first, chain(r.err))
	}
	if !r.err.(net.Error).Timeout() {
		t.Errorf("%s: ETIMEDOUT's Timeout() is false (measured true before)", c.name)
	}
	if short(r.err) == "timeout" {
		t.Errorf("%s: ETIMEDOUT is os.ErrDeadlineExceeded", c.name)
	}
	switch c.first {
	case "read":
		if r.k != 0 {
			t.Errorf("%s: the Read returned %d bytes", c.name, r.k)
		}
	case "write":
		if r.k <= 0 || r.k >= big {
			t.Errorf("%s: the Write returned %d bytes; want 0 < n < %d", c.name, r.k, big)
		}
	}
	if got := strings.Join(later, ", "); got != "Read EOF, Read EOF, Write (0, sys:EPIPE), Write (0, sys:EPIPE)" {
		t.Errorf("%s: after the error: %s", c.name, got)
	}
	if peerDuring != "timeout" || peerW != "(5, nil)" || peerAfter != "sys:ECONNRESET EOF" || peerW2 != "(0, sys:EPIPE)" {
		t.Errorf("%s: the peer: during %q; healed: Write %s, reads %q, Write %s", c.name, peerDuring, peerW, peerAfter, peerW2)
	}
}

// TestResetInNetwork (D1, D2, E1; E9). A reset made by the network: on an
// established connection where each end has received bytes it has not read
// ("s2c-unread" at the client, "c2s-unread" at the server), the router rejects
// the client's packets to the server with a TCP reset (iptables REJECT
// --reject-with tcp-reset in FORWARD: a RST to the client, spoofed from the
// server, in window: its seq is the client segment's ack). The client's next
// Write ("trigger") returns (7, nil) and its segment draws the RST; the server
// receives nothing. Two cases: the client then Reads first, or Writes first.
//
// Measured. Client, Read first: "s2c-unread" (bytes received before the RST
// survive: tcp_reset purges the write queue, not the receive queue), then
// ECONNRESET, then EOF; then Writes (0, EPIPE). Client, Write first: (0,
// ECONNRESET) then (0, EPIPE); then the Reads: "s2c-unread", then EOF, no
// error (the error went to the Write). The bytes "trigger" are lost. The server
// (the rule lifted): its Read returns "c2s-unread" then, with a 200 ms deadline,
// a timeout (it knows nothing yet); its Write returns (5, nil), and draws a RST
// from the client's kernel; then its Reads return ECONNRESET, EOF, and its
// next Write (0, EPIPE). Every error is of kind sys (*net.OpError >
// *os.SyscallError > Errno).
//
// Model: allowed: the client's direction (towards it) cut at the Read or the
// Write keeping its whole unread prefix (D1: bytes, an error, then EOF; or D2's
// break at the Write and then D1's EOF on the cut direction); the "trigger"
// Write's success: D2 appended, later truncated by the server's D1 break; the
// server's ECONNRESET then EOF: D1's break keeping the empty prefix.
func TestResetInNetwork(t *testing.T) {
	netnsTest(t, func(t *testing.T, n *netnsTopo) {
		for _, first := range []string{"read", "write"} {
			d, a := n.pair(t)
			mustWrite(t, a, "s2c-unread")
			waitInq(t, d, 10)
			mustWrite(t, d, "c2s-unread")
			waitInq(t, a, 10)
			port := fmt.Sprint(a.LocalAddr().(*net.TCPAddr).Port)
			undo := n.rule(t, "FORWARD", "-p", "tcp", "-s", nsCliIP, "-d", nsSrvIP, "--dport", port,
				"-j", "REJECT", "--reject-with", "tcp-reset")
			trig := writeRes(d, "trigger")
			waitFor(t, "the client's socket to be reset", func() bool { return tcpState(t, d) == tcpClose })
			var cli string
			if first == "read" {
				rs := reads(d, guard, 4)
				cli = fmt.Sprintf("Reads %q, Writes %s %s", rs, writeRes(d, "more"), writeRes(d, "more"))
			} else {
				w1, w2 := writeRes(d, "more"), writeRes(d, "more")
				cli = fmt.Sprintf("Writes %s %s, Reads %q", w1, w2, reads(d, guard, 4))
			}
			undo()
			srvBefore := reads(a, 200*time.Millisecond, 3)
			srvW := writeRes(a, "reply")
			waitFor(t, "the server's socket to be reset", func() bool { return tcpState(t, a) == tcpClose })
			srvAfter := reads(a, guard, 4)
			srvW2 := writeRes(a, "reply2")
			outcome := fmt.Sprintf("client (%s first): Write(trigger) %s; %s; server: reads %q, Write %s, reads %q, Write %s",
				first, trig, cli, srvBefore, srvW, srvAfter, srvW2)
			evidence(t, "D1,D2,E1 (reset by the network, client "+first+"s first)", outcome,
				"allowed (D1 break keeping the whole unread prefix, or D2 break then D1 EOF; the server: D1 break keeping the empty prefix; E1 sys)")
			want := map[string]string{
				"read":  `Reads "data:s2c-unread sys:ECONNRESET EOF", Writes (0, sys:EPIPE) (0, sys:EPIPE)`,
				"write": `Writes (0, sys:ECONNRESET) (0, sys:EPIPE), Reads "data:s2c-unread EOF"`,
			}[first]
			if trig != "(7, nil)" || cli != want {
				t.Errorf("client (%s first): Write(trigger) %s; %s; want (7, nil); %s", first, trig, cli, want)
			}
			if srvBefore != "data:c2s-unread timeout" || srvW != "(5, nil)" || srvAfter != "sys:ECONNRESET EOF" || srvW2 != "(0, sys:EPIPE)" {
				t.Errorf("server: reads %q, Write %s, reads %q, Write %s", srvBefore, srvW, srvAfter, srvW2)
			}
		}
	})
}

// TestPartitionHealed (D1, D2; E9). Both ends stream to each other (1 KiB
// Writes every 2 ms, pseudo-random bytes), the router drops every packet both
// ways for 2 s (shorter than every timeout: no TCP_USER_TIMEOUT, Linux's
// default tcp_retries2 = 15, Go's default keepalive idle 15 s), then the
// partition is healed; each writer stops 500 ms later and CloseWrites. Measured:
// data flows again 1.1 s after the heal (the next retransmission's backoff),
// every Write returns (len, nil) (the longest blocked 2.9 s: those issued
// during the partition return into the send buffer until it fills), no Read
// returns an error before EOF, and each side reads exactly the bytes the other
// wrote, in order, once, then EOF. Model: allowed (D2: appended; D1: the
// first k unread bytes, then EOF after fin); it is also the only outcome the
// model gives without a break, and the semantics needs no more (a partition
// is not a modeled event: until a timeout, it only delays).
func TestPartitionHealed(t *testing.T) {
	netnsTest(t, func(t *testing.T, n *netnsTopo) {
		d, a := n.pair(t)
		var stop atomic.Bool
		var recvd atomic.Int64 // bytes the server has read
		type side struct {
			sent, got []byte
			werr      error
			rerr      error
			maxStall  time.Duration // the longest single Write
		}
		var sides [2]side // [0] client to server, [1] server to client
		var wg sync.WaitGroup
		writer := func(s *side, c *net.TCPConn, seed uint64) {
			defer wg.Done()
			rng := rand.New(rand.NewPCG(seed, 7))
			buf := make([]byte, 1024)
			for !stop.Load() {
				for i := range buf {
					buf[i] = byte(rng.Uint32())
				}
				t0 := time.Now()
				k, err := c.Write(buf)
				if dt := time.Since(t0); dt > s.maxStall {
					s.maxStall = dt
				}
				s.sent = append(s.sent, buf[:k]...)
				if err != nil || k != len(buf) {
					s.werr = fmt.Errorf("Write = %d, %v", k, err)
					return
				}
				time.Sleep(2 * time.Millisecond)
			}
			if err := c.CloseWrite(); err != nil {
				s.werr = fmt.Errorf("CloseWrite: %v", err)
			}
		}
		reader := func(s *side, c *net.TCPConn, count *atomic.Int64) {
			defer wg.Done()
			buf := make([]byte, 4096)
			for {
				k, err := c.Read(buf)
				s.got = append(s.got, buf[:k]...)
				if count != nil {
					count.Add(int64(k))
				}
				if err == io.EOF {
					return
				}
				if err != nil {
					s.rerr = err
					return
				}
			}
		}
		wg.Add(4)
		go writer(&sides[0], d, 1)
		go writer(&sides[1], a, 2)
		go reader(&sides[0], a, &recvd)
		go reader(&sides[1], d, nil)
		waitFor(t, "64 KiB to arrive before the partition", func() bool { return recvd.Load() >= 64<<10 })
		heal := n.partition(t)
		atPart := recvd.Load()
		time.Sleep(2 * time.Second) // the fault's duration, not a wait for an event
		base := recvd.Load()
		duringPart := base - atPart
		heal()
		healed := time.Now()
		waitFor(t, "data to flow again after the heal", func() bool { return recvd.Load() > base })
		resumed := time.Since(healed)
		time.Sleep(500 * time.Millisecond)
		stop.Store(true)
		ch := make(chan struct{})
		go func() { wg.Wait(); close(ch) }()
		select {
		case <-ch:
		case <-time.After(30 * time.Second):
			t.Fatal("the streams did not finish within 30 s of the heal")
		}
		var res []string
		ok := true
		for i, s := range sides {
			same := bytes.Equal(s.sent, s.got)
			ok = ok && same && s.werr == nil && s.rerr == nil
			res = append(res, fmt.Sprintf("%s: wrote %d bytes (longest Write %.2fs, error %v), read %d then EOF (error %v), identical %v",
				[]string{"client to server", "server to client"}[i], len(s.sent), s.maxStall.Seconds(), s.werr,
				len(s.got), s.rerr, same))
		}
		outcome := fmt.Sprintf("partition 2.0s (%d bytes arrived during it), data flowing again %.2fs after the heal; %s",
			duringPart, resumed.Seconds(), strings.Join(res, "; "))
		evidence(t, "D1,D2 (a partition shorter than every timeout, healed)", outcome,
			"allowed (D2 every Write appended, D1 reads the bytes in order then EOF after fin)")
		if !ok {
			t.Errorf("a byte was lost, duplicated or reordered, or an error occurred: %s", outcome)
		}
	})
}

// TestAcceptOrder (D7; E9). Whether pending connections are accepted in the
// order of their Dials. Per trial, 8 connections are dialed to one listener
// before any Accept, each writing its index (the order in which its Dial
// returned) as its first byte; then the server accepts the 8 and reads the
// indices. Two modes, 50 trials each: back to back (one goroutine, each Dial
// after the previous returned) and concurrent (8 goroutines, each on its own
// thread in the client's namespace, released together). Measured: back to
// back, every trial in Dial order (0 of 50 out of order, every run: Linux's
// accept queue is FIFO, a connection entering it when the handshake's last ACK
// arrives); concurrent, 47 to 50 of 50 trials out of Dial-return order (a Dial
// returns when the SYN-ACK arrives, the server queues it when the ACK does, and
// the index is taken after the Dial returns: the orders differ).
// Model: allowed either way (D7: Accept returns any pending connection to the
// address); nothing here is a reason to give the model an order.
func TestAcceptOrder(t *testing.T) {
	netnsTest(t, func(t *testing.T, n *netnsTopo) {
		const k, trials = 8, 50
		l := n.listen(t)
		addr := l.Addr().String()
		workers := make([]nsWorker, k)
		for i := range workers {
			w, err := newNSWorker(t, n.cliNS)
			if err != nil {
				t.Fatal(err)
			}
			workers[i] = w
		}
		// the first Dial waits (bounded) for the links
		waitFor(t, "the links to come up", func() bool {
			c, err := n.dial(nil, addr)
			if err != nil {
				return false
			}
			c.Close()
			ac, err := l.Accept()
			if err == nil {
				ac.Close()
			}
			return err == nil
		})
		trial := func(concurrent bool) (inOrder bool) {
			var ret atomic.Int32
			conns := make([]*net.TCPConn, k)
			dial := func(i int, w nsWorker) {
				c, err := n.dial(w, addr)
				if err != nil {
					t.Errorf("Dial: %v", err)
					return
				}
				conns[i] = c
				if _, err := c.Write([]byte{byte(ret.Add(1))}); err != nil {
					t.Errorf("writing the index: %v", err)
				}
			}
			if concurrent {
				var wg sync.WaitGroup
				start := make(chan struct{})
				for i := 0; i < k; i++ {
					wg.Add(1)
					go func() { defer wg.Done(); <-start; dial(i, workers[i]) }()
				}
				close(start)
				wg.Wait()
			} else {
				for i := 0; i < k; i++ {
					dial(i, n.cli)
				}
			}
			defer func() {
				for _, c := range conns {
					if c != nil {
						c.Close()
					}
				}
			}()
			inOrder = true
			l.SetDeadline(time.Now().Add(waitLimit))
			for i := 0; i < k; i++ {
				ac, err := l.Accept()
				if err != nil {
					t.Fatalf("Accept: %v", err)
				}
				ac.SetReadDeadline(time.Now().Add(waitLimit))
				b := make([]byte, 1)
				_, err = io.ReadFull(ac, b)
				ac.Close()
				if err != nil {
					t.Fatalf("reading the index: %v", err)
				}
				if int(b[0]) != i+1 {
					inOrder = false
				}
			}
			return inOrder
		}
		var res []string
		outOf := map[bool]int{}
		for _, conc := range []bool{false, true} {
			for i := 0; i < trials; i++ {
				if !trial(conc) {
					outOf[conc]++
				}
			}
			res = append(res, fmt.Sprintf("%s: %d of %d trials accepted out of Dial-return order",
				map[bool]string{false: "back to back", true: "concurrent"}[conc], outOf[conc], trials))
		}
		evidence(t, "D7 (accept order, 8 pending connections)", strings.Join(res, "; "),
			"allowed (D7 accepts any pending connection; any order)")
		if outOf[false] != 0 {
			t.Errorf("back-to-back Dials accepted out of order in %d trials (measured 0 before; the model allows it)", outOf[false])
		}
	})
}
