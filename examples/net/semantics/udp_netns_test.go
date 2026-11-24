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
// Model: agrees. U3's integrity claim (at most 1472 bytes: one packet, never
// fragmented on an MTU of 1500) holds; a larger payload is fragmented, which
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
				if size > intactMaxGo && errors.Is(err, syscall.EMSGSIZE) {
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
			if size <= intactMaxGo {
				if cd["Ip.FragCreates"] != 0 || cd["Ip.FragOKs"] != 0 || sd["Ip.ReasmReqds"] != 0 || !intact {
					t.Errorf("CONTRADICTS U3 (intactMax): %s", obs)
				}
				evidence(t, "U2,U3", obs, "allowed (one packet, Intact: d = bs)")
			} else {
				evidence(t, "U2,U3", obs, "allowed (fragmented; Intact allows any bytes, here intact)")
			}
		}
	})
}

// intactMaxGo is Impl.lean's intactMax.
const intactMaxGo = 1472

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
// integrity holds for payloads of at most 1472 bytes. A received datagram
// that differs from every one sent would CONTRADICT U3.
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
			size := 48 + rand.IntN(intactMaxGo-48+1)
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
			t.Errorf("CONTRADICTS U3 (integrity): %s", obs)
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
