//go:build linux && amd64

package semantics

import (
	"bytes"
	"crypto/sha256"
	"encoding/binary"
	"errors"
	"fmt"
	"math/rand/v2"
	"net"
	"os"
	"os/exec"
	"regexp"
	"strings"
	"syscall"
	"testing"
	"time"
)

// UDP between network namespaces (netns_helpers_test.go: the client, router
// and server namespaces joined by veth pairs, default MTU 1500; the gate
// NET_NETNS=1 and the re-execution as root by sudo -n). Run them with
//
//	cd examples && NET_NETNS=1 go test ./net/semantics/ -run UDPNetns -count=1 -v
//
// Each logs EVIDENCE lines (the decisions, the outcome, the model's verdict).

const (
	ipMtuDiscover = 10 // IP_MTU_DISCOVER, linux/in.h
	soRcvbufForce = 33 // SO_RCVBUFFORCE, asm-generic/socket.h
)

// udpNsListen binds a "udp4" socket at ip:port in the namespace of worker w.
func udpNsListen(t *testing.T, w nsWorker, ip string, port int) *net.UDPConn {
	t.Helper()
	var c *net.UDPConn
	var err error
	w.do(func() { c, err = net.ListenUDP("udp4", &net.UDPAddr{IP: net.ParseIP(ip).To4(), Port: port}) })
	if err != nil {
		t.Fatalf("ListenUDP %s:%d: %s", ip, port, udpShape(err))
	}
	t.Cleanup(func() { c.Close() })
	return c
}

// udpWarm sends small datagrams from s to r until one arrives (bounded): the
// links are up and the neighbours resolved. It drains what arrived.
func udpWarm(t *testing.T, s, r *net.UDPConn) {
	t.Helper()
	end := time.Now().Add(waitLimit)
	for {
		udpSend(t, s, []byte("warm"), laddr(r))
		if b, _, err := udpRecv(r, 64, 100*time.Millisecond); err == nil && string(b) == "warm" {
			break
		}
		if time.Now().After(end) {
			t.Fatal("no datagram crossed the router")
		}
	}
	for {
		if _, _, err := udpRecv(r, 64, 100*time.Millisecond); err != nil {
			return
		}
	}
}

var mtuRe = regexp.MustCompile(`\bmtu (\d+)\b`)

// linkMTU is the MTU of interface dev in namespace ns.
func linkMTU(t *testing.T, ns, dev string) string {
	t.Helper()
	out, err := exec.Command("ip", "-n", ns, "-o", "link", "show", "dev", dev).CombinedOutput()
	if err != nil {
		t.Fatalf("ip -n %s link show %s: %v %s", ns, dev, err, out)
	}
	m := mtuRe.FindStringSubmatch(string(out))
	if m == nil {
		t.Fatalf("no mtu in %q", out)
	}
	return m[1]
}

// TestUDPNetnsFragmentation (U2, U3; Lean: intactMax, Intact, SendStep). Over
// the topology's veth pairs (MTU 1500, the default of a veth: every
// interface the tests and examples/lib/robust create, measured here: the
// ends' eth0, the router's c0 and s0, and a bridge as robust's bridge variant
// makes, br0 with a veth port, all 1500; lo 65536), from the client to the
// server through the router:
//
//   - a 1472-byte payload (1500 - 20 - 8) leaves the client as ONE IP packet:
//     the client namespace's /proc/net/snmp Ip.OutRequests +1, Ip.FragCreates
//     +0, Ip.FragOKs +0; the server's Ip.ReasmReqds +0; it arrives byte for
//     byte;
//   - a 1473-byte payload is accepted by WriteToUDP (1473, nil) and fragmented
//     by the client's kernel: FragOKs +1, FragCreates +2; the server
//     reassembles it (ReasmOKs +1) and receives it byte for byte. Why not
//     EMSGSIZE: a UDP socket's IP_MTU_DISCOVER is IP_PMTUDISC_WANT (measured,
//     getsockopt: 1) since net.ipv4.ip_no_pmtu_disc is 0 (measured), and
//     with WANT ip_append_data/ip_fragment fragment locally a datagram larger
//     than the path MTU; only IP_PMTUDISC_DO or PROBE (which Go never sets)
//     make it EMSGSIZE.
//
// Model: agrees. With no ICMP lowering the path MTU, 1472 bytes is the most
// that goes as one packet over an interface MTU of 1500; intactMax is 524
// (TestUDPNetnsPmtuFloor: the path MTU's floor), so both sizes here are ones
// the model lets deliver any bytes (here intact: over-approximation).
func TestUDPNetnsFragmentation(t *testing.T) {
	netnsTest(t, func(t *testing.T, n *netnsTopo) {
		mtus := []string{
			"client eth0 " + linkMTU(t, n.cliNS, "eth0"),
			"client lo " + linkMTU(t, n.cliNS, "lo"),
			"router c0 " + linkMTU(t, n.rtrNS, "c0"),
			"router s0 " + linkMTU(t, n.rtrNS, "s0"),
			"server eth0 " + linkMTU(t, n.srvNS, "eth0"),
		}
		// robust's bridge variant: br0 in the router, the machines' veth ends its ports.
		mustNsCmd(t, "ip", "-n", n.rtrNS, "link", "add", "brt", "type", "bridge")
		mustNsCmd(t, "ip", "-n", n.rtrNS, "link", "add", "bp0", "type", "veth", "peer", "name", "bp1")
		mustNsCmd(t, "ip", "-n", n.rtrNS, "link", "set", "bp0", "master", "brt")
		mtus = append(mtus, "bridge (with a veth port) "+linkMTU(t, n.rtrNS, "brt"))
		for _, m := range mtus {
			if f := strings.Fields(m); f[len(f)-1] != "1500" && !strings.Contains(m, " lo ") {
				t.Errorf("MTU not 1500: %s", m)
			}
		}
		t.Logf("MTUs: %s", strings.Join(mtus, "; "))
		pmtu, err := exec.Command("ip", "netns", "exec", n.cliNS, "sysctl", "-n", "net.ipv4.ip_no_pmtu_disc").Output()
		if err != nil {
			t.Fatal(err)
		}
		s := udpNsListen(t, n.cli, nsCliIP, 20001)
		r := udpNsListen(t, n.srv, nsSrvIP, 20002)
		disc := udpSockopt(t, s, syscall.IPPROTO_IP, ipMtuDiscover)
		t.Logf("client: net.ipv4.ip_no_pmtu_disc = %s, the socket's IP_MTU_DISCOVER = %d (1: IP_PMTUDISC_WANT)",
			strings.TrimSpace(string(pmtu)), disc)
		udpWarm(t, s, r)
		names := []string{"Ip.OutRequests", "Ip.FragOKs", "Ip.FragCreates", "Ip.FragFails"}
		rnames := []string{"Ip.ReasmReqds", "Ip.ReasmOKs", "Udp.InDatagrams"}
		for _, size := range []int{1472, 1473} {
			b := make([]byte, size)
			for i := range b {
				b[i] = byte(rand.IntN(256))
			}
			cb, sb := udpCounters(t, n.cliNS), udpCounters(t, n.srvNS)
			k, err := s.WriteToUDP(b, laddr(r))
			if err != nil {
				if size > ifaceMax && errors.Is(err, syscall.EMSGSIZE) {
					evidence(t, "U2,U3", fmt.Sprintf("%d bytes: EMSGSIZE %s", size, udpShape(err)), "allowed (SendStep sys)")
					continue
				}
				t.Fatalf("WriteToUDP(%d bytes): %d, %s", size, k, udpShape(err))
			}
			got, _, err := udpRecv(r, 2048, guard)
			if err != nil {
				t.Fatalf("%d bytes: not received: %s", size, udpShape(err))
			}
			cd := counterDelta(cb, udpCounters(t, n.cliNS), names...)
			sd := counterDelta(sb, udpCounters(t, n.srvNS), rnames...)
			intact := bytes.Equal(got, b)
			obs := fmt.Sprintf("%d-byte payload: WriteToUDP (%d, nil); client %v; server %v; received %d bytes, intact %v",
				size, k, cd, sd, len(got), intact)
			if size <= ifaceMax {
				if cd["Ip.FragCreates"] != 0 || cd["Ip.FragOKs"] != 0 || sd["Ip.ReasmReqds"] != 0 || !intact {
					t.Errorf("not one packet at the interface MTU: %s", obs)
				}
				evidence(t, "U2,U3", obs, "allowed (above intactMax = 524: any bytes; here one packet, intact)")
			} else {
				evidence(t, "U2,U3", obs, "allowed (fragmented; Intact allows any bytes, here intact)")
			}
		}
	})
}

// intactMaxGo is Impl.lean's intactMax (552 - 20 - 8: the path MTU's floor,
// TestUDPNetnsPmtuFloor); ifaceMax is the most one packet carries at the
// interface MTU of 1500 when no ICMP lowered the path MTU.
const (
	intactMaxGo = 524
	ifaceMax    = 1472
)

// TestUDPNetnsFaults (U3, U5; Lean: Intact, RecvStep over UdpGlobal.sent).
// netem on the router's interface towards the server (loss 20%, duplicate
// 20%, delay 5ms jitter 5ms, reorder 25%, limit 100000), the server's socket
// with an 8 MiB receive buffer (SO_RCVBUFFORCE), the client sends 2000
// distinct datagrams, 48 to 1472 bytes each, every one an 8-byte sequence
// number, random bytes, and the SHA-256 of what precedes it; the server reads
// until 1 s passes with nothing. Measured (the counts in the EVIDENCE line):
// (a) every datagram received is byte-identical to the one sent with its
// sequence number (and its checksum matches); (b) some are never received;
// (c) some are received more than once; (d) some arrive after one with a
// higher sequence number. The faults are the network's: the server's
// Udp.RcvbufErrors stays 0.
//
// Model: agrees: these are exactly the faults of U5's one rule (a receive
// returns any datagram sent to the address and leaves it there), and U3's
// integrity holds for payloads of at most 524 bytes (intactMax). A received
// datagram of at most 524 bytes that differs from every one sent would
// CONTRADICT U3; the larger ones (up to 1472) the model lets be any bytes,
// and Linux delivered them intact too (over-approximation).
func TestUDPNetnsFaults(t *testing.T) {
	netnsTest(t, func(t *testing.T, n *netnsTopo) {
		const N = 2000
		s := udpNsListen(t, n.cli, nsCliIP, 20001)
		r := udpNsListen(t, n.srv, nsSrvIP, 20002)
		var serr error
		rawFd(t, r, func(fd uintptr) { serr = syscall.SetsockoptInt(int(fd), syscall.SOL_SOCKET, soRcvbufForce, 8<<20) })
		if serr != nil {
			t.Fatalf("SO_RCVBUFFORCE: %v", serr)
		}
		udpWarm(t, s, r)
		mustNsCmd(t, "ip", "netns", "exec", n.rtrNS, "tc", "qdisc", "add", "dev", "s0", "root", "netem",
			"limit", "100000", "delay", "5ms", "5ms", "reorder", "25%", "loss", "20%", "duplicate", "20%")
		sb := udpCounters(t, n.srvNS)
		sent := make([][]byte, N)
		for i := range sent {
			size := 48 + rand.IntN(ifaceMax-48+1)
			b := make([]byte, size)
			binary.BigEndian.PutUint64(b, uint64(i))
			for j := 8; j < size-32; j++ {
				b[j] = byte(rand.IntN(256))
			}
			sum := sha256.Sum256(b[:size-32])
			copy(b[size-32:], sum[:])
			sent[i] = b
		}
		type got struct {
			b   []byte
			err error
		}
		done := make(chan []got, 1)
		go func() {
			var gs []got
			for {
				b, _, err := udpRecv(r, 2048, time.Second)
				if errors.Is(err, os.ErrDeadlineExceeded) {
					break
				}
				gs = append(gs, got{b, err})
				if err != nil {
					break
				}
			}
			done <- gs
		}()
		for _, b := range sent {
			udpSend(t, s, b, laddr(r))
		}
		gs := <-done
		count := make([]int, N)
		total, ooo, maxSeq, corrupt := 0, 0, -1, 0
		for _, g := range gs {
			if g.err != nil {
				t.Fatalf("receive: %s", udpShape(g.err))
			}
			total++
			b := g.b
			ok := len(b) >= 40
			var seq int
			if ok {
				seq = int(binary.BigEndian.Uint64(b))
				sum := sha256.Sum256(b[:len(b)-32])
				ok = seq < N && bytes.Equal(sum[:], b[len(b)-32:]) && bytes.Equal(b, sent[seq])
			}
			if !ok {
				corrupt++
				continue
			}
			if count[seq] == 0 && seq < maxSeq {
				ooo++
			}
			count[seq]++
			if seq > maxSeq {
				maxSeq = seq
			}
		}
		distinct, dups := 0, 0
		for _, c := range count {
			if c > 0 {
				distinct++
				dups += c - 1
			}
		}
		sd := counterDelta(sb, udpCounters(t, n.srvNS), "Udp.InDatagrams", "Udp.RcvbufErrors", "Udp.InErrors", "Udp.InCsumErrors")
		qd, _ := exec.Command("ip", "netns", "exec", n.rtrNS, "tc", "-s", "qdisc", "show", "dev", "s0").CombinedOutput()
		t.Logf("netem: %s", strings.Join(strings.Fields(string(qd)), " "))
		obs := fmt.Sprintf("%d sent; %d received (%d distinct): lost %d, duplicate receptions %d, out of order %d, not identical to the one sent %d; server %v",
			N, total, distinct, N-distinct, dups, ooo, corrupt, sd)
		if corrupt != 0 {
			t.Errorf("a received datagram differs from the one sent (CONTRADICTS U3 if at most 524 bytes; Linux has never shown it): %s", obs)
		}
		if N-distinct == 0 || dups == 0 || ooo == 0 {
			t.Errorf("a fault was not shown: %s", obs)
		}
		evidence(t, "U3,U5", obs, "allowed (U5: loss, duplication, reordering; U3: intact)")
	})
}

// TestUDPNetnsSentBeforeBind (U5; Lean: UdpGlobal.sent, RecvStep). The client
// sends a datagram to the server's address before any socket there is bound;
// the server's kernel drops it (its namespace's Udp.NoPorts +1, measured, and
// waited for), then the server binds the address: its ReadFromUDP (bounded by
// the harness's deadline) gets nothing; a datagram sent after the bind is
// received, and only it.
//
// Model: over-approximates: the early datagram stays in UdpGlobal.sent, so
// the model lets the socket bound afterwards receive it, which Linux never
// does (__udp4_lib_rcv: no socket, the skb is freed). Sound (more behaviours).
func TestUDPNetnsSentBeforeBind(t *testing.T) {
	netnsTest(t, func(t *testing.T, n *netnsTopo) {
		s := udpNsListen(t, n.cli, nsCliIP, 20001)
		// The links up and the neighbours resolved, through another server port.
		w := udpNsListen(t, n.srv, nsSrvIP, 20004)
		udpWarm(t, s, w)
		dst := &net.UDPAddr{IP: net.ParseIP(nsSrvIP).To4(), Port: 20003}
		before := udpCounters(t, n.srvNS)["Udp.NoPorts"]
		udpSend(t, s, []byte("early"), dst)
		waitFor(t, "the server's kernel to drop the early datagram (Udp.NoPorts)", func() bool {
			return udpCounters(t, n.srvNS)["Udp.NoPorts"] > before
		})
		r := udpNsListen(t, n.srv, nsSrvIP, 20003)
		_, _, err := udpRecv(r, 64, udpShort)
		if !errors.Is(err, os.ErrDeadlineExceeded) {
			t.Fatalf("the socket bound after the early datagram: %s (want nothing)", udpShape(err))
		}
		udpSend(t, s, []byte("late"), dst)
		b, _, err := udpRecv(r, 64, guard)
		if err != nil || string(b) != "late" {
			t.Fatalf("after the bind: %q, %v", b, err)
		}
		if _, _, err := udpRecv(r, 64, udpShort); !errors.Is(err, os.ErrDeadlineExceeded) {
			t.Fatalf("a second datagram after the bind: %s", udpShape(err))
		}
		evidence(t, "U5", "a datagram sent before the bind: dropped (Udp.NoPorts +1), never received; one sent after: received",
			"over-approximates (the model allows receiving the early one)")
	})
}

// inetCsum is the Internet checksum (RFC 1071) of b.
func inetCsum(b []byte) uint16 {
	var s uint32
	for i := 0; i+1 < len(b); i += 2 {
		s += uint32(b[i])<<8 | uint32(b[i+1])
	}
	if len(b)%2 == 1 {
		s += uint32(b[len(b)-1]) << 8
	}
	for s>>16 != 0 {
		s = s>>16 + s&0xffff
	}
	return ^uint16(s)
}

// forgeFragNeeded sends, from worker w's namespace through a raw ICMP socket,
// an ICMP destination-unreachable "fragmentation needed" (type 3, code 4)
// with next-hop MTU mtu to src, quoting the header of a UDP datagram
// src:sport -> dst:dport (DF set) as the one that did not fit.
func forgeFragNeeded(t *testing.T, w nsWorker, src, dst string, sport, dport, mtu int) {
	t.Helper()
	inner := make([]byte, 20)
	inner[0], inner[8], inner[9] = 0x45, 64, syscall.IPPROTO_UDP
	binary.BigEndian.PutUint16(inner[2:], 1500)
	binary.BigEndian.PutUint16(inner[4:], 0x1234)
	binary.BigEndian.PutUint16(inner[6:], 0x4000) // DF
	copy(inner[12:], net.ParseIP(src).To4())
	copy(inner[16:], net.ParseIP(dst).To4())
	binary.BigEndian.PutUint16(inner[10:], inetCsum(inner))
	udp := make([]byte, 8)
	binary.BigEndian.PutUint16(udp[0:], uint16(sport))
	binary.BigEndian.PutUint16(udp[2:], uint16(dport))
	binary.BigEndian.PutUint16(udp[4:], 1480)
	body := append([]byte{3, 4, 0, 0, 0, 0, byte(mtu >> 8), byte(mtu)}, append(inner, udp...)...)
	binary.BigEndian.PutUint16(body[2:], inetCsum(body))
	var err error
	w.do(func() {
		var fd int
		fd, err = syscall.Socket(syscall.AF_INET, syscall.SOCK_RAW, syscall.IPPROTO_ICMP)
		if err != nil {
			return
		}
		defer syscall.Close(fd)
		to := &syscall.SockaddrInet4{}
		copy(to.Addr[:], net.ParseIP(src).To4())
		err = syscall.Sendto(fd, body, 0, to)
	})
	if err != nil {
		t.Fatalf("forging ICMP frag-needed (mtu %d): %v", mtu, err)
	}
}

var routeMtuRe = regexp.MustCompile(`\bmtu (lock )?(\d+)\b`)

// routeMTU is the path MTU the route from ns to dst carries (ip route get:
// "mtu lock 552"), "" when it has none.
func routeMTU(t *testing.T, ns, dst string) string {
	t.Helper()
	out, err := exec.Command("ip", "-n", ns, "route", "get", dst).CombinedOutput()
	if err != nil {
		t.Fatalf("ip route get: %v %s", err, out)
	}
	m := routeMtuRe.FindStringSubmatch(string(out))
	if m == nil {
		return ""
	}
	return m[0]
}

// TestUDPNetnsPmtuFloor (U3; Lean: intactMax = 524, Intact). What decides
// fragmentation is the path MTU, which an ICMP "fragmentation needed" message
// lowers, from any sender (forged here from the server's namespace with a raw
// socket, quoting a datagram of the client's socket: __udp4_lib_err finds the
// socket and calls ipv4_sk_update_pmtu, which records a route exception
// towards the server). Linux never lowers it below net.ipv4.route.min_pmtu
// (measured 552, the default): a smaller MTU is clamped to it and locked
// (__ip_rt_update_pmtu; ip route get: "mtu lock 552"). Measured, with
// /proc/net/snmp's Ip.FragCreates in the client's namespace:
//
//   - forged MTU 68: the route shows "mtu lock 552"; a 524-byte payload
//     (552 - 20 - 8) is one packet (FragCreates +0), a 525-byte one is
//     fragmented; both arrive intact (WriteToUDP returns (len, nil): the
//     socket's IP_PMTUDISC_WANT fragments locally rather than refusing);
//   - the route's exception flushed (1472 bytes one packet again), forged MTU
//     552 (route "mtu 552"): a 1472-byte payload is fragmented, so the
//     interface MTU alone (the earlier intactMax of 1472) bounds nothing.
//
// Model: agrees with intactMax = 524 (at most 524 bytes is one packet
// whatever ICMP arrives); the earlier 1472 is refuted (a 1472-byte datagram
// is fragmented, and fragments of distinct datagrams may be misassembled).
func TestUDPNetnsPmtuFloor(t *testing.T) {
	netnsTest(t, func(t *testing.T, n *netnsTopo) {
		out, err := exec.Command("ip", "netns", "exec", n.cliNS, "sysctl", "-n", "net.ipv4.route.min_pmtu").Output()
		if err != nil {
			t.Fatal(err)
		}
		if v := strings.TrimSpace(string(out)); v != "552" {
			t.Fatalf("net.ipv4.route.min_pmtu = %s, want 552", v)
		}
		s := udpNsListen(t, n.cli, nsCliIP, 20001)
		r := udpNsListen(t, n.srv, nsSrvIP, 20002)
		udpWarm(t, s, r)
		if m := routeMTU(t, n.cliNS, nsSrvIP); m != "" {
			t.Fatalf("route has a path MTU before any ICMP: %q", m)
		}
		names := []string{"Ip.OutRequests", "Ip.FragOKs", "Ip.FragCreates"}
		send := func(size int) map[string]int64 {
			t.Helper()
			b := make([]byte, size)
			for i := range b {
				b[i] = byte(rand.IntN(256))
			}
			cb := udpCounters(t, n.cliNS)
			if k, err := s.WriteToUDP(b, laddr(r)); k != size || err != nil {
				t.Fatalf("WriteToUDP(%d bytes): %d, %s", size, k, udpShape(err))
			}
			got, _, err := udpRecv(r, 2048, guard)
			if err != nil || !bytes.Equal(got, b) {
				t.Fatalf("%d bytes: received %d bytes, %s", size, len(got), udpShape(err))
			}
			return counterDelta(cb, udpCounters(t, n.cliNS), names...)
		}
		forge := func(mtu int, want string) {
			t.Helper()
			forgeFragNeeded(t, n.srv, nsCliIP, nsSrvIP, 20001, 20002, mtu)
			waitFor(t, "the route's path MTU "+want, func() bool { return routeMTU(t, n.cliNS, nsSrvIP) == want })
		}
		forge(68, "mtu lock 552")
		d524, d525 := send(524), send(525)
		obs := fmt.Sprintf("min_pmtu 552; forged MTU 68 -> route %q; 524 bytes %v, 525 bytes %v (both intact)",
			"mtu lock 552", d524, d525)
		if d524["Ip.FragCreates"] != 0 || d524["Ip.FragOKs"] != 0 {
			t.Errorf("CONTRADICTS U3 (intactMax 524): %s", obs)
		}
		if d525["Ip.FragCreates"] == 0 {
			t.Errorf("525 bytes not fragmented at path MTU 552: %s", obs)
		}
		evidence(t, "U3", obs, "allowed (intactMax = 524: one packet at the floor)")
		// (c) from a fresh route: the exception flushed, then MTU 552 alone.
		mustNsCmd(t, "ip", "-n", n.cliNS, "route", "flush", "cache")
		if m := routeMTU(t, n.cliNS, nsSrvIP); m != "" {
			t.Fatalf("route still has a path MTU after the flush: %q", m)
		}
		if d := send(1472); d["Ip.FragCreates"] != 0 {
			t.Fatalf("1472 bytes fragmented after the flush: %v", d)
		}
		forge(552, "mtu 552")
		d1472 := send(1472)
		obs2 := fmt.Sprintf("route cache flushed (1472 bytes one packet again); forged MTU 552 -> route %q; 1472 bytes %v (intact here)", "mtu 552", d1472)
		if d1472["Ip.FragCreates"] == 0 {
			t.Errorf("1472 bytes not fragmented at path MTU 552: %s", obs2)
		}
		evidence(t, "U3", obs2, "refutes the earlier intactMax = 1472; allowed by 524")
	})
}
