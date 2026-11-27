package ipv4port

import (
	"errors"
	"fmt"
	"net"
)

// IPv4Port is a pair of IPv4 address and port.
type IPv4Port struct {
	First  net.IP
	Second int

	str string
}

func (ipPort IPv4Port) GetIP() net.IP {
	return ipPort.First
}

func (ipPort IPv4Port) GetPort() int {
	return ipPort.Second
}

func (ipPort *IPv4Port) SetIP(ip net.IP) {
	ipPort.First = ip
	ipPort.str = fmt.Sprintf("%s:%d", ipPort.First.String(), ipPort.Second)
}

func (ipPort *IPv4Port) SetPort(port int) {
	ipPort.Second = port
	ipPort.str = fmt.Sprintf("%s:%d", ipPort.First.String(), ipPort.Second)
}

func (ipPort IPv4Port) String() string {
	return ipPort.str
}

// FromHostPort parses "a.b.c.d:port" (decimal octets 0..255 without leading zeros, a
// decimal port) in plain Go. On those strings (the configured addresses it is given) the result
// is the one net.SplitHostPort, net.ParseIP, IP.To4, strconv.Atoi and fmt.Sprintf gave: First
// is the 16-byte form ParseIP returns for an IPv4 address, Second the port, and String()
// "a.b.c.d:port" with the port in canonical decimal.
func (ipPort *IPv4Port) FromHostPort(hostport string) error {
	var octets [4]byte
	i := 0
	n := len(hostport)
	for k := 0; k < 4; k++ {
		start := i
		v := 0
		for i < n && hostport[i] >= '0' && hostport[i] <= '9' && i-start < 3 {
			v = v*10 + int(hostport[i]-'0')
			i++
		}
		digits := i - start
		if digits == 0 || v > 255 || (digits > 1 && hostport[start] == '0') {
			return errors.New("invalid IPv4 address: " + hostport)
		}
		octets[k] = byte(v)
		sep := byte('.')
		if k == 3 {
			sep = ':'
		}
		if i >= n || hostport[i] != sep {
			return errors.New("invalid IPv4 address and port: " + hostport)
		}
		i++
	}

	pstart := i
	port := 0
	for i < n && hostport[i] >= '0' && hostport[i] <= '9' {
		if port > (1<<31)/10 {
			return errors.New("invalid port: " + hostport)
		}
		port = port*10 + int(hostport[i]-'0')
		i++
	}
	if i == pstart || i != n {
		return errors.New("invalid port: " + hostport)
	}

	ipPort.First = net.IP{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0xff, 0xff, octets[0], octets[1], octets[2], octets[3]}
	ipPort.Second = port
	ipPort.str = decimal(int(octets[0])) + "." + decimal(int(octets[1])) + "." +
		decimal(int(octets[2])) + "." + decimal(int(octets[3])) + ":" + decimal(port)
	return nil
}

// FromAddrString returns an IPv4Port whose String() is s, as is (an accepted connection's
// remote address, read once). Its IP and port are not set: only String() is read.
func FromAddrString(s string) IPv4Port {
	return IPv4Port{str: s}
}

// decimal is n (n >= 0) in decimal, as fmt's %d.
func decimal(n int) string {
	if n == 0 {
		return "0"
	}
	var b []byte
	for n > 0 {
		b = append([]byte{byte('0' + n%10)}, b...)
		n /= 10
	}
	return string(b)
}

// ip4 is the IPv4 address of ip (its 4-byte or 16-byte form), as IP.To4.
func ip4(ip net.IP) []byte {
	if len(ip) == 16 {
		return ip[12:16]
	}
	return ip
}

// Less orders by IP and then port, as before over net.IP.Equal and IP.To4: equal addresses
// compare ports; otherwise the first two bytes of the addresses, as a big-endian uint16, are
// compared (nonissues/ipv4port-less-16bit.md).
func (ipPort IPv4Port) Less(other IPv4Port) bool {
	curr := ip4(ipPort.GetIP())
	otherIP := ip4(other.GetIP())
	if curr[0] == otherIP[0] && curr[1] == otherIP[1] && curr[2] == otherIP[2] && curr[3] == otherIP[3] {
		return ipPort.GetPort() < other.GetPort()
	}

	parsedCurr := uint16(curr[0])<<8 | uint16(curr[1])
	parsedOther := uint16(otherIP[0])<<8 | uint16(otherIP[1])

	return parsedCurr < parsedOther
}

// ByLess sorts IPv4Ports with Less (sort.Sort; same algorithm and comparisons as sort.Slice
// with Less).
type ByLess []IPv4Port

func (a ByLess) Len() int           { return len(a) }
func (a ByLess) Less(i, j int) bool { return a[i].Less(a[j]) }
func (a ByLess) Swap(i, j int)      { a[i], a[j] = a[j], a[i] }
