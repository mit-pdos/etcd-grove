package robust

import (
	"fmt"
	"math/rand/v2"
	"net"
	"os"
	"runtime"
	"strings"
	"sync"
	"syscall"
	"time"
)

// sysSetns is setns(2) on linux/amd64 (the syscall package has no SYS_SETNS).
const sysSetns = 308

// dialWorkers is how many OS threads of a machine's namespace dial for this process at once.
const dialWorkers = 8

// A Network joins machines. In the namespace mode (NewNetwork) every machine is a network
// namespace of its own with one interface, eth0, whose address is 10.77.k.1 for the machine's
// index k, and whose other end is the interface m<k> of a router namespace that forwards between
// them: the network. Every fault is made in the router (iptables in its FORWARD chain, tc netem
// on its interfaces), so that to the machines' kernels it is a fault of the network (packets lost,
// late, duplicated, reordered, a middlebox's reset) and never a local error (a DROP in a
// machine's own OUTPUT chain fails its sends with EPERM). Nothing is made in the host's namespace.
// It needs root (IsRoot): run this process as root (RerunAsRoot).
//
// The bridge variant of the namespace mode is for a host where the router cannot forward (a
// container whose /proc/sys is read-only, so ip_forward stays 0) or has no iptables: there the
// router's namespace holds a Linux bridge instead, every machine at 10.77.k.1 on one /16, and the
// faults are tc's in the bridge's namespace: a block is a flower filter on the ingress of the
// sender's port that drops the packets to the receiver (a Reset block drops too: tc cannot answer
// with a TCP reset, CanReset), and link faults are netem on the receiver's port, as in the router
// variant. NewNetwork picks it by itself. A process without CAP_NET_ADMIN (root in a container that
// lacks it) can still make one inside a user namespace of its own (RerunInUserns).
//
// In the local mode (LocalNetwork) the machines share the host's loopback interface, all at one
// random address 127.a.b.c, and the network has no faults: what runs where root is not available.
type Network struct {
	tag    string // the namespaces' prefix, unique on the host
	router string // the router's namespace ("" in the local mode)
	bridge bool   // the router's namespace is a bridge (the bridge variant: no forwarding, no iptables)
	ip     string // the local mode's address

	mu       sync.Mutex
	machines []*Machine
}

// A Machine is a host of the network: a network namespace with its address (in the local mode,
// the host itself), on which this process starts processes (Start) and dials (Dial).
type Machine struct {
	Name string
	IP   string // its address: a process listening on it is reachable at IP:port
	ns   string // its namespace ("" in the local mode)
	idx  int
	net  *Network
	dial chan func() // the dialing threads of its namespace (nil in the local mode)
}

// NetnsAvailable says whether network namespaces can be made: root with CAP_NET_ADMIN, and the
// ip and tc commands (iptables too for the router variant; without it, NewNetwork makes the
// bridge variant).
func NetnsAvailable() error {
	if !IsRoot() {
		return fmt.Errorf("network namespaces need root (RerunAsRoot)")
	}
	if !HasNetAdmin() {
		return fmt.Errorf("network namespaces need CAP_NET_ADMIN (RerunInUserns)")
	}
	for _, c := range []string{"ip", "tc"} {
		if _, err := run("which", c); err != nil {
			return err
		}
	}
	return nil
}

// HasNetAdmin says whether this process has CAP_NET_ADMIN (in its user namespace).
func HasNetAdmin() bool {
	b, err := os.ReadFile("/proc/self/status")
	if err != nil {
		return false
	}
	for _, l := range strings.Split(string(b), "\n") {
		if v, ok := strings.CutPrefix(l, "CapEff:"); ok {
			var caps uint64
			if _, err := fmt.Sscanf(strings.TrimSpace(v), "%x", &caps); err != nil {
				return false
			}
			return caps&(1<<12) != 0 // CAP_NET_ADMIN
		}
	}
	return false
}

// routerAvailable says whether the router variant can be made: iptables, and forwarding in the
// router's namespace (sysctl writes /proc/sys, which a container may mount read-only).
func (n *Network) routerAvailable() bool {
	if _, err := run("which", "iptables-restore"); err != nil {
		return false
	}
	_, err := run("ip", "netns", "exec", n.router, "sysctl", "-qw", "net.ipv4.ip_forward=1")
	return err == nil
}

// LocalNetwork is a network of the local mode: no namespaces, no faults.
func LocalNetwork() *Network {
	return &Network{ip: fmt.Sprintf("127.%d.%d.%d", 1+rand.IntN(254), rand.IntN(256), 1+rand.IntN(254))}
}

// NewNetwork makes the router's namespace of a network of the namespace mode; tag (short:
// interface names are not made from it) prefixes every namespace's name and must be unique on
// the host.
func NewNetwork(tag string) (*Network, error) {
	if err := NetnsAvailable(); err != nil {
		return nil, err
	}
	n := &Network{tag: tag, router: tag + "-net"}
	if _, err := run("ip", "netns", "add", n.router); err != nil {
		return nil, err
	}
	cmds := [][]string{
		{"ip", "-n", n.router, "link", "set", "lo", "up"},
		{"ip", "netns", "exec", n.router, "iptables", "-N", "ROBUST"},
		{"ip", "netns", "exec", n.router, "iptables", "-A", "FORWARD", "-j", "ROBUST"},
	}
	if !n.routerAvailable() {
		n.bridge = true
		cmds = [][]string{
			{"ip", "-n", n.router, "link", "set", "lo", "up"},
			{"ip", "-n", n.router, "link", "add", "br0", "type", "bridge"},
			{"ip", "-n", n.router, "link", "set", "br0", "up"},
		}
	}
	for _, c := range cmds {
		if _, err := run(c...); err != nil {
			n.Close()
			return nil, err
		}
	}
	return n, nil
}

// Namespaces says whether the network is of the namespace mode (and can have faults).
func (n *Network) Namespaces() bool { return n.router != "" }

// CanReset says whether a Reset block refuses connections with a TCP reset (the router variant);
// in the bridge variant it drops, as a plain block.
func (n *Network) CanReset() bool { return n.Namespaces() && !n.bridge }

// AddMachine adds a machine named name (for the logs).
func (n *Network) AddMachine(name string) (*Machine, error) {
	n.mu.Lock()
	idx := len(n.machines) + 1
	m := &Machine{Name: name, idx: idx, net: n}
	n.machines = append(n.machines, m)
	n.mu.Unlock()
	if !n.Namespaces() {
		m.IP = n.ip
		return m, nil
	}
	if idx > 250 {
		return nil, fmt.Errorf("robust: at most 250 machines")
	}
	m.ns = fmt.Sprintf("%s-%d", n.tag, idx)
	m.IP = fmt.Sprintf("10.77.%d.1", idx)
	gw := fmt.Sprintf("10.77.%d.254", idx)
	r := m.routerIf()
	if n.bridge {
		for _, c := range [][]string{
			{"ip", "netns", "add", m.ns},
			{"ip", "-n", m.ns, "link", "set", "lo", "up"},
			{"ip", "-n", m.ns, "link", "add", "eth0", "type", "veth", "peer", "name", r, "netns", n.router},
			{"ip", "-n", m.ns, "addr", "add", m.IP + "/16", "dev", "eth0"},
			{"ip", "-n", m.ns, "link", "set", "eth0", "up"},
			{"ip", "-n", n.router, "link", "set", r, "master", "br0"},
			{"ip", "-n", n.router, "link", "set", r, "up"},
			{"ip", "netns", "exec", n.router, "tc", "qdisc", "add", "dev", r, "clsact"},
		} {
			if _, err := run(c...); err != nil {
				return nil, err
			}
		}
		return m, m.startDialers()
	}
	for _, c := range [][]string{
		{"ip", "netns", "add", m.ns},
		{"ip", "-n", m.ns, "link", "set", "lo", "up"},
		{"ip", "-n", m.ns, "link", "add", "eth0", "type", "veth", "peer", "name", r, "netns", n.router},
		{"ip", "-n", m.ns, "addr", "add", m.IP + "/24", "dev", "eth0"},
		{"ip", "-n", n.router, "addr", "add", gw + "/24", "dev", r},
		{"ip", "-n", m.ns, "link", "set", "eth0", "up"},
		{"ip", "-n", n.router, "link", "set", r, "up"},
		{"ip", "-n", m.ns, "route", "add", "default", "via", gw},
	} {
		if _, err := run(c...); err != nil {
			return nil, err
		}
	}
	return m, m.startDialers()
}

// routerIf is the router's interface towards m.
func (m *Machine) routerIf() string { return fmt.Sprintf("m%d", m.idx) }

// Machines are the network's machines, in the order they were added.
func (n *Network) Machines() []*Machine {
	n.mu.Lock()
	defer n.mu.Unlock()
	return append([]*Machine(nil), n.machines...)
}

// Close removes the namespaces (and with them their interfaces, rules and queues), and stops the
// machines' dialing threads. The processes must have exited.
func (n *Network) Close() {
	for _, m := range n.Machines() {
		if m.dial != nil {
			close(m.dial)
			m.dial = nil
		}
		if m.ns != "" {
			run("ip", "netns", "del", m.ns)
		}
	}
	if n.router != "" {
		run("ip", "netns", "del", n.router)
	}
}

// startDialers starts the threads that dial from m's namespace: each joins it (setns(2)) and
// stays locked to its goroutine, so it exits with it instead of returning to Go's pool. A socket
// belongs to the namespace of the thread that made it, and is then usable from any goroutine.
func (m *Machine) startDialers() error {
	m.dial = make(chan func())
	errs := make(chan error, dialWorkers)
	for i := 0; i < dialWorkers; i++ {
		go func() {
			runtime.LockOSThread()
			f, err := os.Open("/run/netns/" + m.ns)
			if err != nil {
				errs <- err
				return
			}
			_, _, e := syscall.RawSyscall(sysSetns, f.Fd(), syscall.CLONE_NEWNET, 0)
			f.Close()
			if e != 0 {
				errs <- fmt.Errorf("setns %s: %v", m.ns, e)
				return
			}
			errs <- nil
			for fn := range m.dial {
				fn()
			}
		}()
	}
	for i := 0; i < dialWorkers; i++ {
		if err := <-errs; err != nil {
			return err
		}
	}
	return nil
}

// Dial connects to addr (TCP) from m, within timeout: what a client running on m does.
func (m *Machine) Dial(addr string, timeout time.Duration) (net.Conn, error) {
	if m.dial == nil {
		return net.DialTimeout("tcp", addr, timeout)
	}
	type res struct {
		c   net.Conn
		err error
	}
	done := make(chan res, 1)
	m.dial <- func() {
		c, err := net.DialTimeout("tcp", addr, timeout)
		done <- res{c, err}
	}
	r := <-done
	return r.c, r.err
}

// A Block is a fault of the network on the packets from one machine to another: dropped
// (DROP: the connections stall, then time out), or, if Reset, refused with a TCP reset (a
// middlebox's: the connections break at once).
type Block struct {
	From, To *Machine
	Reset    bool
}

// SetBlocks replaces the network's blocks by bs (none: healed). Connections already made are
// subject to them too: a block cuts the packets, not the connections.
func (n *Network) SetBlocks(bs []Block) error {
	if !n.Namespaces() {
		if len(bs) == 0 {
			return nil
		}
		return fmt.Errorf("robust: a local network has no faults")
	}
	if n.bridge {
		return n.setBridgeBlocks(bs)
	}
	var b strings.Builder
	b.WriteString("*filter\n-F ROBUST\n")
	for _, x := range bs {
		if x.Reset {
			fmt.Fprintf(&b, "-A ROBUST -s %s -d %s -p tcp -j REJECT --reject-with tcp-reset\n", x.From.IP, x.To.IP)
		}
		fmt.Fprintf(&b, "-A ROBUST -s %s -d %s -j DROP\n", x.From.IP, x.To.IP)
	}
	b.WriteString("COMMIT\n")
	_, err := runIn(b.String(), "ip", "netns", "exec", n.router, "iptables-restore", "--noflush")
	return err
}

// setBridgeBlocks is SetBlocks in the bridge variant: every port's ingress filters removed, then a
// filter on the sender's port for each block, dropping its IP packets to the receiver.
func (n *Network) setBridgeBlocks(bs []Block) error {
	for _, m := range n.Machines() {
		if _, err := run("ip", "netns", "exec", n.router, "tc", "filter", "del", "dev", m.routerIf(), "ingress"); err != nil {
			return err
		}
	}
	if len(bs) == 0 {
		return nil
	}
	var b strings.Builder
	for _, x := range bs {
		fmt.Fprintf(&b, "filter add dev %s ingress protocol ip prio 1 flower dst_ip %s action drop\n",
			x.From.routerIf(), x.To.IP)
	}
	_, err := runIn(b.String(), "ip", "netns", "exec", n.router, "tc", "-batch", "-")
	return err
}

// Partition blocks every packet between machines of different groups (both ways); a machine in
// no group is not blocked.
func Partition(groups [][]*Machine, reset bool) []Block {
	var bs []Block
	for i, g := range groups {
		for j, h := range groups {
			if i == j {
				continue
			}
			for _, a := range g {
				for _, b := range h {
					bs = append(bs, Block{From: a, To: b, Reset: reset})
				}
			}
		}
	}
	return bs
}

// Heal removes every block.
func (n *Network) Heal() error { return n.SetBlocks(nil) }

// LinkFaults are the faults of the packets the network delivers to one machine (tc netem on the
// router's interface towards it): each delayed by Delay plus or minus Jitter, lost with
// probability Loss (percent), duplicated with probability Duplicate, and, with a delay, sent at
// once (ahead of the delayed ones: reordered) with probability Reorder. TCP turns them into
// retransmissions, stalls and reordered arrivals across connections, never into a stream's
// bytes out of order.
type LinkFaults struct {
	Delay, Jitter            time.Duration
	Loss, Duplicate, Reorder float64
}

// None says whether f has no fault.
func (f LinkFaults) None() bool { return f == LinkFaults{} }

// String is f as netem's parameters.
func (f LinkFaults) String() string {
	args := []string{}
	if f.Delay != 0 {
		args = append(args, "delay", fmt.Sprintf("%dus", f.Delay.Microseconds()))
		if f.Jitter != 0 {
			args = append(args, fmt.Sprintf("%dus", f.Jitter.Microseconds()))
		}
	}
	if f.Loss != 0 {
		args = append(args, "loss", fmt.Sprintf("%.2f%%", f.Loss))
	}
	if f.Duplicate != 0 {
		args = append(args, "duplicate", fmt.Sprintf("%.2f%%", f.Duplicate))
	}
	if f.Reorder != 0 && f.Delay != 0 {
		args = append(args, "reorder", fmt.Sprintf("%.2f%%", f.Reorder))
	}
	return strings.Join(args, " ")
}

// SetLink sets the faults of the packets delivered to m (none: a plain link).
func (n *Network) SetLink(m *Machine, f LinkFaults) error {
	if !n.Namespaces() {
		if f.None() {
			return nil
		}
		return fmt.Errorf("robust: a local network has no faults")
	}
	if f.None() || f.String() == "" {
		run("ip", "netns", "exec", n.router, "tc", "qdisc", "del", "dev", m.routerIf(), "root")
		return nil
	}
	_, err := run(append([]string{"ip", "netns", "exec", n.router, "tc", "qdisc", "replace", "dev",
		m.routerIf(), "root", "netem"}, strings.Fields(f.String())...)...)
	return err
}
