//go:build linux && amd64

package semantics

import (
	"fmt"
	"net"
	"strings"
	"testing"
	"time"
)

// TestStickyTimedOut (D1, D14; the proposed sticky rule: notes/net-sticky-read.md).
// The client's kernel gives up on a connection with bytes received and unread:
// the server wrote "s2c-unread", which arrived (SIOCINQ 10), the client set
// TCP_USER_TIMEOUT 2000 ms and wrote 14 bytes the server never acknowledges,
// because the router, in two cases:
//
//   - drops every packet both ways (a partition): the kernel's error is ETIMEDOUT
//     (tcp_write_err: sk_err = sk_err_soft ?: ETIMEDOUT);
//   - rejects the client's packets to the server with an ICMP host-unreachable
//     (iptables REJECT --reject-with icmp-host-unreachable): on an established
//     socket the ICMP error is only soft (tcp_v4_err: sk_err_soft, no IP_RECVERR),
//     and the timeout's error is that soft error, EHOSTUNREACH.
//
// Nobody reads until the socket is closed (TCP_INFO state CLOSE, tcp_done); then
// the client Reads. Measured, both cases: "s2c-unread" first (the received bytes
// survive), then the error with nothing unread (SIOCINQ 0), of kind sys, then EOF
// on every later Read; Writes (0, EPIPE). So a read error other than a deadline's
// comes only once nothing is unread, and no byte follows it; the sys errors a
// Read can return on configuration C are ECONNRESET (TestStickyReset,
// TestStickyKilledPeer, TestResetInNetwork), ETIMEDOUT and EHOSTUNREACH (here).
func TestStickyTimedOut(t *testing.T) {
	netnsTest(t, func(t *testing.T, n *netnsTopo) {
		cases := []struct {
			name, want string
			fault      func(t *testing.T, port string) (undo func())
		}{
			{"partition", "sys:ETIMEDOUT", func(t *testing.T, port string) func() { return n.partition(t) }},
			{"icmp host-unreachable", "sys:EHOSTUNREACH", func(t *testing.T, port string) func() {
				return n.rule(t, "FORWARD", "-p", "tcp", "-s", nsCliIP, "-d", nsSrvIP, "--dport", port,
					"-j", "REJECT", "--reject-with", "icmp-host-unreachable")
			}},
		}
		for _, c := range cases {
			d, a := n.pair(t)
			mustWrite(t, a, "s2c-unread")
			waitInq(t, d, 10)
			setUserTimeout(t, d, 2000)
			undo := c.fault(t, fmt.Sprint(a.LocalAddr().(*net.TCPAddr).Port))
			w := writeRes(d, "unacknowledged")
			end := time.Now().Add(20 * time.Second)
			for tcpState(t, d) != tcpClose {
				if time.Now().After(end) {
					t.Fatalf("%s: the client's socket not closed after 20 s", c.name)
				}
				time.Sleep(10 * time.Millisecond)
			}
			var out []string
			atErr := -1
			for i := 0; i < 8 && atErr < 0; i++ {
				d.SetReadDeadline(time.Now().Add(guard))
				buf := make([]byte, 64)
				k, err := d.Read(buf)
				if k > 0 {
					out = append(out, "data:"+string(buf[:k]))
				}
				if err != nil {
					out = append(out, short(err))
					atErr = inq(t, d)
				}
			}
			after := reads(d, guard, 1) + " " + reads(d, guard, 1) + " " + reads(d, guard, 1)
			ws := writeRes(d, "more") + " " + writeRes(d, "more")
			undo()
			got := strings.Join(out, " ")
			evidence(t, "D1,D14 (sticky read error: "+c.name+")",
				fmt.Sprintf("Write %s; reads %q (%d unread at the error), then %s; Writes %s", w, got, atErr, after, ws),
				"allowed by D1 today and by the sticky rule (sys only with nothing unread; then EOF on the cut, empty direction)")
			if w != "(14, nil)" || got != "data:s2c-unread "+c.want || atErr != 0 ||
				after != "EOF EOF EOF" || ws != "(0, sys:EPIPE) (0, sys:EPIPE)" {
				t.Errorf("%s: Write %s; reads %q (%d unread at the error), then %q; Writes %s; want (14, nil); data:s2c-unread %s, 0; EOF x3; EPIPE x2",
					c.name, w, got, atErr, after, ws, c.want)
			}
		}
	})
}
