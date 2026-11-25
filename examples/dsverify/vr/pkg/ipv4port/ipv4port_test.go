package ipv4port

import (
	"encoding/binary"
	"fmt"
	"math/rand"
	"net"
	"strconv"
	"testing"
)

// goFromHostPort is FromHostPort as released (net.SplitHostPort, net.ParseIP, IP.To4,
// strconv.Atoi, fmt.Sprintf): the reference the plain-Go parser must agree with.
func goFromHostPort(hostport string) (net.IP, int, string, error) {
	ip, port, err := net.SplitHostPort(hostport)
	if err != nil {
		return nil, 0, "", err
	}
	parsedIP := net.ParseIP(ip)
	if parsedIP == nil || parsedIP.To4() == nil {
		return nil, 0, "", fmt.Errorf("invalid IP address: %s", ip)
	}
	parsedPort, err := strconv.Atoi(port)
	if err != nil {
		return nil, 0, "", err
	}
	return parsedIP, parsedPort, fmt.Sprintf("%s:%d", parsedIP.String(), parsedPort), nil
}

// goLess is Less as released.
func goLess(a, b IPv4Port) bool {
	if a.GetIP().Equal(b.GetIP()) {
		return a.GetPort() < b.GetPort()
	}
	return binary.BigEndian.Uint16(a.GetIP().To4()) < binary.BigEndian.Uint16(b.GetIP().To4())
}

// The plain-Go FromHostPort gives the released result on every dotted-quad address with a
// decimal port (the configured addresses' form), and rejects malformed ones.
func TestFromHostPortAsReleased(t *testing.T) {
	rng := rand.New(rand.NewSource(1))
	inputs := []string{"127.0.0.1:7000", "10.77.0.11:7000", "0.0.0.0:0", "255.255.255.255:65535",
		"1.2.3.4:007000", "10.77.0.1:1"}
	for i := 0; i < 5000; i++ {
		inputs = append(inputs, fmt.Sprintf("%d.%d.%d.%d:%d", rng.Intn(256), rng.Intn(256),
			rng.Intn(256), rng.Intn(256), rng.Intn(70000)))
	}
	for _, in := range inputs {
		var p IPv4Port
		err := p.FromHostPort(in)
		ip, port, str, gerr := goFromHostPort(in)
		if err != nil || gerr != nil {
			t.Fatalf("%q: err %v, released err %v", in, err, gerr)
		}
		if !p.First.Equal(ip) || len(p.First) != len(ip) || p.Second != port || p.String() != str {
			t.Fatalf("%q: got %v %d %q, released %v %d %q", in, p.First, p.Second, p.String(), ip, port, str)
		}
	}
	for _, in := range []string{"", "1.2.3:4", "1.2.3.4", "1.2.3.4:", "01.2.3.4:5", "256.1.1.1:5",
		"1.2.3.4:x", "1.2.3.4.5:6", "a.b.c.d:1", "1.2.3.4:5:6", "1.2.3.1000:5"} {
		var p IPv4Port
		if p.FromHostPort(in) == nil {
			t.Errorf("%q accepted", in)
		}
		if _, _, _, gerr := goFromHostPort(in); gerr == nil {
			t.Errorf("%q: released accepts it", in)
		}
	}
}

// Less gives the released result on every pair of parsed addresses.
func TestLessAsReleased(t *testing.T) {
	rng := rand.New(rand.NewSource(2))
	var ps []IPv4Port
	for i := 0; i < 300; i++ {
		var p IPv4Port
		s := fmt.Sprintf("%d.%d.%d.%d:%d", rng.Intn(3), rng.Intn(3), rng.Intn(3), rng.Intn(3), rng.Intn(4))
		if err := p.FromHostPort(s); err != nil {
			t.Fatal(err)
		}
		ps = append(ps, p)
	}
	for _, a := range ps {
		for _, b := range ps {
			if a.Less(b) != goLess(a, b) {
				t.Fatalf("Less(%v, %v) = %v, released %v", a, b, a.Less(b), goLess(a, b))
			}
		}
	}
}
