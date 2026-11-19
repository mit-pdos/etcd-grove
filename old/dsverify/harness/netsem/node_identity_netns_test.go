package netsem

import (
	"fmt"
	"net"
	"os"
	"os/exec"
	"strings"
	"testing"
)

// TestNodeIdentity: a node's wildcard Listen, and its Listen on another node's IP, as the rig
// deploys a node (one network namespace, one IPv4 address, here 10.77.0.10 on a dummy link;
// run.sh runs this test under `sudo unshare -n`, so nothing outside the private namespace is
// touched). Skipped unless NETSEM_NETNS=1.
//
// WildcardListen: Listen on a wildcard host, ":p", "0.0.0.0:p" or "[::]:p" (Go listens on the
// unspecified address, all local interfaces: an IPv6 socket that also takes IPv4 when the
// kernel supports it), is reached by a Dial of the node's own configured address "ip:p", and it
// conflicts with a Listen on "ip:p" either way (EADDRINUSE), as two wildcard spellings conflict
// with each other: with one IP per node, the wildcard listener is the listener on "ip:p".
//
// Lean: Impl.lean, `listenAddr` (a wildcard host resolves to the node's IP, the extension's
// local state, spelled as the configured address "ip:p"), NetConnStep "Listen" (the resolved
// string, then as a Listen of it).
// Allowed: Dial("ip:p") to a node that listened on ":p" succeeds; Listen(":p") failing.
// Excluded: two open listeners on ":p" and "ip:p" (or ":p" and "0.0.0.0:p") at one node.
// Not modeled: Dial of 127.0.0.1:p (the wildcard listener takes it; a loopback address is never
// configured, so a Dial of it is stuck).
//
// ListenOtherIP: Listen on an address whose IP is not the node's fails with EADDRNOTAVAIL
// (ip_nonlocal_bind is 0, the default, and the rig's). The model keeps allowing success there
// (an over-approximation, sound for safety; the kits listen only on their own addresses), so the
// semantics does not depend on that sysctl.
//
// Lean: Impl.lean, NetConnStep "Listen" (a configured address of any node).
// Evidence: measured (below).
func TestNodeIdentity(t *testing.T) {
	if os.Getenv("NETSEM_NETNS") != "1" {
		t.Skip("needs a private network namespace (run.sh)")
	}
	run := func(args ...string) {
		if out, err := exec.Command(args[0], args[1:]...).CombinedOutput(); err != nil {
			t.Fatalf("%v: %v %s", args, err, out)
		}
	}
	run("ip", "link", "set", "lo", "up")
	run("ip", "link", "add", "d0", "type", "dummy")
	run("ip", "addr", "add", "10.77.0.10/24", "dev", "d0")
	run("ip", "link", "set", "d0", "up")
	out, err := nodeIdentity("10.77.0.10", "10.77.0.11")
	if err != nil {
		t.Fatal(err)
	}
	t.Logf("NodeIdentity: %s", out)
}

// nodeIdentity is the body of TestNodeIdentity: me is the node's IP, other another node's.
func nodeIdentity(me, other string) (string, error) {
	var res []string
	port := 7100
	for _, host := range []string{"", "0.0.0.0", "[::]"} {
		port++
		p := fmt.Sprint(port)
		// a wildcard listener, reached by a Dial of the node's own address
		l, err := net.Listen("tcp", host+":"+p)
		if err != nil {
			return "", fmt.Errorf("Listen %q: %v", host+":"+p, err)
		}
		ch := make(chan error, 1)
		go func() {
			c, err := l.Accept()
			if err == nil {
				c.Close()
			}
			ch <- err
		}()
		d, eDial := dial(me + ":" + p)
		if eDial == nil {
			d.Close()
		}
		eAcc := <-ch
		// the conflicts, both ways, at the same port
		_, eSpec := net.Listen("tcp", me+":"+p)
		var eOther []string
		for _, h2 := range []string{"", "0.0.0.0", "[::]"} {
			if h2 != host {
				_, e := net.Listen("tcp", h2+":"+p)
				eOther = append(eOther, fmt.Sprintf("%q %s", h2, describe(e)))
			}
		}
		l.Close()
		port++
		p2 := fmt.Sprint(port)
		ls, err := net.Listen("tcp", me+":"+p2)
		if err != nil {
			return "", err
		}
		_, eWild := net.Listen("tcp", host+":"+p2)
		ls.Close()
		res = append(res, fmt.Sprintf("Listen(%q) ok, Addr %s; Dial(%q) %s, Accept %s; then Listen(%q) %s, other wildcards %s; Listen(%q) after Listen(%q): %s",
			host+":"+p, l.Addr(), me+":"+p, describe(eDial), describe(eAcc), me+":"+p, describe(eSpec),
			strings.Join(eOther, ", "), host+":"+p2, me+":"+p2, describe(eWild)))
	}
	_, eNot := net.Listen("tcp", other+":7200")
	res = append(res, fmt.Sprintf("Listen(%q) (another node's IP): %s", other+":7200", describe(eNot)))
	return strings.Join(res, "\n\t"), nil
}
