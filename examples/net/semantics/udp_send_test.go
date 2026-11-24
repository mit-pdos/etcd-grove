//go:build linux

package semantics

import (
	"bytes"
	"errors"
	"fmt"
	"net"
	"os"
	"syscall"
	"testing"
	"time"
)

// TestUDPSendDelivered (U2, U3; Lean: SendStep, Intact, RecvStep). On an open
// socket, WriteToUDP(b, a) returns (len(b), nil) (poll.FD.WriteToInet4 returns
// len(p) after a sendto(2) without error: internal/poll/fd_unix.go), and the
// socket bound to a receives b byte for byte, with the sender's address as
// the *UDPAddr ReadFromUDP returns. Sizes 1, 100, 1472 (intactMax).
//
// Model: agrees (SendStep's success adds d with Intact b d, d = b for
// |b| <= 1472; RecvStep returns it).
func TestUDPSendDelivered(t *testing.T) {
	t.Parallel()
	s, r := udpListen(t, "127.0.0.1"), udpListen(t, "127.0.0.1")
	for _, n := range []int{1, 100, 1472} {
		b := bytes.Repeat([]byte{byte(n)}, n)
		b[0] = 'x'
		k, err := s.WriteToUDP(b, laddr(r))
		if k != n || err != nil {
			t.Fatalf("WriteToUDP(%d bytes) = %d, %v", n, k, err)
		}
		got, from, err := udpRecv(r, 2048, guard)
		if err != nil || !bytes.Equal(got, b) {
			t.Fatalf("ReadFromUDP after a %d-byte send: %d bytes, %v", n, len(got), err)
		}
		if from == nil || from.String() != laddr(s).String() {
			t.Fatalf("source address %v, want %v", from, laddr(s))
		}
	}
	evidence(t, "U2,U3", "WriteToUDP = (len, nil); the datagram received intact, source = sender", "allowed (SendStep, Intact, RecvStep)")
}

// TestUDPSendToUnbound (U2; Lean: SendStep). A WriteToUDP to an address no
// socket is bound to returns (len(b), nil), and so do nine more; between them
// the sender's own ReadFromUDP (bounded by a deadline of the harness) times
// out every time and never returns ECONNREFUSED. Why: the receiving kernel
// answers with an ICMP port unreachable (__udp4_lib_rcv: no socket,
// icmp_send(ICMP_PORT_UNREACH)), and the sender's __udp4_lib_err reports
// an ICMP error to an unconnected socket only with IP_RECVERR set (else
// "if (!inet->recverr) { if (!harderr || sk->sk_state != TCP_ESTABLISHED)
// goto out; }": net/ipv4/udp.c). The control shows the ICMP is sent: a
// connected socket (DialUDP, state ESTABLISHED) to the same address gets
// ECONNREFUSED on its next Read or Write.
//
// Model: agrees (SendStep's success; a refusal would be a sys failure, also
// allowed). The control's DialUDP is not modeled (U12).
func TestUDPSendToUnbound(t *testing.T) {
	t.Parallel()
	s := udpListen(t, "127.0.0.1")
	dst := udpFreeAddr(t, "127.0.0.1")
	var res []string
	for i := 0; i < 10; i++ {
		k, err := s.WriteToUDP([]byte("nobody"), dst)
		if k != 6 || err != nil {
			t.Fatalf("send %d to unbound %v: %d, %s", i, dst, k, udpShape(err))
		}
		_, _, err = udpRecv(s, 64, 50*time.Millisecond)
		if errors.Is(err, syscall.ECONNREFUSED) || !errors.Is(err, os.ErrDeadlineExceeded) {
			t.Fatalf("read on the unconnected sender after send %d: %s", i, udpShape(err))
		}
		res = append(res, "timeout")
	}
	// Control: a connected socket learns of the ICMP.
	dc, err := net.DialUDP("udp4", nil, dst)
	if err != nil {
		t.Fatalf("DialUDP: %v", err)
	}
	defer dc.Close()
	if _, err := dc.Write([]byte("x")); err != nil {
		t.Fatalf("first connected Write: %v", err)
	}
	dc.SetReadDeadline(time.Now().Add(guard))
	_, err = dc.Read(make([]byte, 8))
	if !errors.Is(err, syscall.ECONNREFUSED) {
		t.Fatalf("connected control: %s, want ECONNREFUSED", udpShape(err))
	}
	evidence(t, "U2", fmt.Sprintf("10 sends to unbound %v: (6, nil); sender reads: %d timeouts, no ECONNREFUSED (control, connected: %s)",
		dst, len(res), udpShape(err)), "allowed (SendStep success)")
}

// TestUDPSendSizeLimit (U2, U3; Lean: SendStep's sys failure, Intact). On
// loopback (MTU 65536) a payload of 65507 bytes (65535 - 20 - 8) is sent
// and received whole (it is fragmented, so U3 lets the model deliver any
// bytes; Linux delivers them intact); 65508 bytes fail with EMSGSIZE
// (ip_append_data: an IPv4 datagram is at most 0xFFFF bytes), shaped
// *net.OpError{Op "write", Net "udp4", Source the socket's address, Addr the
// destination} > *os.SyscallError{Syscall "sendto"} > EMSGSIZE
// (WriteToUDP's OpError: net/udpsock.go; netFD.writeToInet4 wraps with
// writeToSyscallName "sendto": net/fd_posix.go, net/fd_unix.go), n = 0, and
// nothing arrives.
//
// Model: agrees (a sys failure, the datagram added or not).
func TestUDPSendSizeLimit(t *testing.T) {
	t.Parallel()
	s, r := udpListen(t, "127.0.0.1"), udpListen(t, "127.0.0.1")
	if err := r.SetReadBuffer(1 << 20); err != nil {
		t.Fatal(err)
	}
	big := bytes.Repeat([]byte("0123456789abcdef"), 65507/16+1)[:65507]
	udpSend(t, s, big, laddr(r))
	got, _, err := udpRecv(r, 70000, guard)
	if err != nil || !bytes.Equal(got, big) {
		t.Fatalf("65507-byte datagram: %d bytes, %v", len(got), err)
	}
	k, err := s.WriteToUDP(append(big, 'x'), laddr(r))
	shape := udpShape(err)
	var oe *net.OpError
	var se *syscallErr
	if k != 0 || !errors.As(err, &oe) || oe.Op != "write" || oe.Net != "udp4" || oe.Source == nil || oe.Addr == nil ||
		!errors.As(err, &se) || se.Syscall != "sendto" || !errors.Is(err, syscall.EMSGSIZE) {
		t.Fatalf("65508 bytes: %d, %s", k, shape)
	}
	if _, _, err := udpRecv(r, 70000, udpShort); !errors.Is(err, os.ErrDeadlineExceeded) {
		t.Fatalf("something arrived after the refused send: %v", err)
	}
	evidence(t, "U2,U3", "65507 bytes delivered whole; 65508: (0, "+shape+"), nothing arrives", "allowed (SendStep sys)")
}

// TestUDPZeroLength (U2, U4; Lean: SendStep, RecvStep). A zero-length
// WriteToUDP returns (0, nil) and sends a datagram with an empty payload; the
// receiver's ReadFromUDP returns n = 0, err = nil and the sender's address
// (not io.EOF: poll.FD.eofError returns EOF only when ZeroReadIsEOF, false for
// SOCK_DGRAM: net/fd_unix.go newFD). A datagram sent after it is the next
// read's.
//
// Model: agrees (Intact [] d gives d = []; RecvStep returns [] and success).
func TestUDPZeroLength(t *testing.T) {
	t.Parallel()
	s, r := udpListen(t, "127.0.0.1"), udpListen(t, "127.0.0.1")
	k, err := s.WriteToUDP(nil, laddr(r))
	if k != 0 || err != nil {
		t.Fatalf("WriteToUDP(empty) = %d, %v", k, err)
	}
	got, from, err := udpRecv(r, 64, guard)
	if len(got) != 0 || err != nil || from == nil || from.String() != laddr(s).String() {
		t.Fatalf("ReadFromUDP of an empty datagram: %d, %v, %s", len(got), from, udpShape(err))
	}
	udpSend(t, s, []byte("next"), laddr(r))
	if got, _, err := udpRecv(r, 64, guard); err != nil || string(got) != "next" {
		t.Fatalf("after the empty one: %q, %v", got, err)
	}
	evidence(t, "U2,U4", "empty datagram: WriteToUDP (0, nil); ReadFromUDP (0, sender, nil)", "allowed")
}
