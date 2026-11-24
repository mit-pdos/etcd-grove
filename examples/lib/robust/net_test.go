package robust

import (
	"bytes"
	"fmt"
	"io"
	"net"
	"os"
	"strings"
	"testing"
	"time"
)

// TestMain runs an echo server instead of the tests when the test started this binary as one
// (ROBUST_ECHO set to the address to listen at).
func TestMain(m *testing.M) {
	if addr := os.Getenv("ROBUST_ECHO"); addr != "" {
		l, err := net.Listen("tcp", addr)
		if err != nil {
			fmt.Fprintln(os.Stderr, err)
			os.Exit(2)
		}
		for {
			c, err := l.Accept()
			if err != nil {
				continue
			}
			go func() {
				io.Copy(c, c)
				c.Close()
			}()
		}
	}
	os.Exit(m.Run())
}

// asRootTest runs the test t as root (in a child test binary run by sudo -n), unless it already
// runs as root; it says whether the caller is the root child, which runs the body.
func asRootTest(t *testing.T) bool {
	if os.Getenv("ROBUST_NETNS") == "" {
		t.Skip("a network-namespace test: set ROBUST_NETNS=1 (needs sudo -n)")
	}
	if IsRoot() && HasNetAdmin() {
		return true
	}
	var out bytes.Buffer
	args := []string{"-test.run=^" + t.Name() + "$", "-test.v", "-test.count=1"}
	var err error
	if IsRoot() {
		// a container's root without CAP_NET_ADMIN: a user namespace of its own (the bridge variant)
		err = RerunInUserns(args, []string{"ROBUST_NETNS=1"}, &out)
	} else {
		err = RerunAsRoot(args, []string{"ROBUST_NETNS=1"}, &out)
	}
	for _, l := range strings.Split(out.String(), "\n") {
		if strings.TrimSpace(l) != "" {
			t.Log(l)
		}
	}
	if err != nil {
		t.Fatalf("as root: %v", err)
	}
	return false
}

// echo dials addr from m, writes a line and reads it back, within timeout.
func echo(m *Machine, addr string, timeout time.Duration) error {
	c, err := m.Dial(addr, timeout)
	if err != nil {
		return err
	}
	defer c.Close()
	c.SetDeadline(time.Now().Add(timeout))
	if _, err := c.Write([]byte("ping\n")); err != nil {
		return err
	}
	b := make([]byte, 5)
	if _, err := io.ReadFull(c, b); err != nil {
		return err
	}
	if string(b) != "ping\n" {
		return fmt.Errorf("echoed %q", b)
	}
	return nil
}

// TestNetworkFaults checks the namespace network: two machines reach each other; a partition
// with drops stalls a dial until its timeout, one with resets refuses it at once; a one-way
// block cuts only its way; healing restores the link; a netem delay delays.
func TestNetworkFaults(t *testing.T) {
	if !asRootTest(t) {
		return
	}
	n, err := NewNetwork(fmt.Sprintf("rbt%d", os.Getpid()))
	if err != nil {
		t.Fatal(err)
	}
	defer n.Close()
	a, err := n.AddMachine("a")
	if err != nil {
		t.Fatal(err)
	}
	b, err := n.AddMachine("b")
	if err != nil {
		t.Fatal(err)
	}
	exe, _ := os.Executable()
	addr := b.IP + ":7000"
	p, err := b.Start(exe, nil, []string{"ROBUST_ECHO=" + addr}, os.Stderr, func(err error) {
		t.Errorf("the echo server exited: %v", err)
	})
	if err != nil {
		t.Fatal(err)
	}
	defer p.Kill()
	deadline := time.Now().Add(5 * time.Second)
	for echo(a, addr, time.Second) != nil {
		if time.Now().After(deadline) {
			t.Fatal("a cannot reach b's echo server")
		}
		time.Sleep(20 * time.Millisecond)
	}

	if err := n.SetBlocks(Partition([][]*Machine{{a}, {b}}, false)); err != nil {
		t.Fatal(err)
	}
	start := time.Now()
	if err := echo(a, addr, 300*time.Millisecond); err == nil {
		t.Error("an echo across a dropping partition succeeded")
	} else if time.Since(start) < 250*time.Millisecond {
		t.Errorf("a dropping partition failed the dial at once (%v): %v", time.Since(start), err)
	}

	if n.CanReset() {
		if err := n.SetBlocks(Partition([][]*Machine{{a}, {b}}, true)); err != nil {
			t.Fatal(err)
		}
		start = time.Now()
		if err := echo(a, addr, 2*time.Second); err == nil {
			t.Error("an echo across a resetting partition succeeded")
		} else if time.Since(start) > time.Second {
			t.Errorf("a resetting partition did not refuse at once (%v): %v", time.Since(start), err)
		}
	}

	// b's packets to a lost: the handshake's answer never arrives
	if err := n.SetBlocks([]Block{{From: b, To: a}}); err != nil {
		t.Fatal(err)
	}
	if err := echo(a, addr, 300*time.Millisecond); err == nil {
		t.Error("an echo with b's packets to a dropped succeeded")
	}

	if err := n.Heal(); err != nil {
		t.Fatal(err)
	}
	if err := echo(a, addr, time.Second); err != nil {
		t.Errorf("after healing: %v", err)
	}

	if err := n.SetLink(b, LinkFaults{Delay: 100 * time.Millisecond}); err != nil {
		t.Fatal(err)
	}
	start = time.Now()
	if err := echo(a, addr, 3*time.Second); err != nil {
		t.Errorf("with a delay: %v", err)
	} else if d := time.Since(start); d < 200*time.Millisecond {
		t.Errorf("a 100ms delay on the packets to b, an echo (two round trips) took %v", d)
	}
	if err := n.SetLink(b, LinkFaults{}); err != nil {
		t.Fatal(err)
	}
}
