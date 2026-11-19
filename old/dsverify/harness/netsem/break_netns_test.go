package netsem

import (
	"fmt"
	"net"
	"os"
	"os/exec"
	"testing"
	"time"
)

// TestBreakInNetwork is BreakSuffix with the reset made by the network, not by a process: in a
// private network namespace (run.sh runs this test under `sudo unshare -n`), after the dialer
// wrote 8 MiB that the acceptor has not read, iptables rejects the acceptor's packets with a TCP
// reset, and the acceptor's next packet (a 1-byte Write) draws it. The acceptor then reads a
// prefix of the bytes, then an error, then EOF; the dialer's later writes are lost and fail.
// Skipped unless NETSEM_NETNS=1. TestVeth runs the same over the rig's veth links.
func TestBreakInNetwork(t *testing.T) {
	if os.Getenv("NETSEM_NETNS") != "1" {
		t.Skip("needs a private network namespace (run.sh)")
	}
	run := func(args ...string) error {
		if out, err := exec.Command(args[0], args[1:]...).CombinedOutput(); err != nil {
			return fmt.Errorf("%v: %v %s", args, err, out)
		}
		return nil
	}
	if err := run("ip", "link", "set", "lo", "up"); err != nil {
		t.Fatal(err)
	}
	out, err := breakInNetwork(func(args ...string) error { return run(append([]string{"iptables"}, args...)...) })
	if err != nil {
		t.Fatal(err)
	}
	t.Logf("BreakInNetwork: %s", out)
}

// breakInNetwork is the body of TestBreakInNetwork; iptables runs iptables where the acceptor is.
func breakInNetwork(iptables func(args ...string) error) (string, error) {
	d, a, err := pair()
	if err != nil {
		return "", err
	}
	defer d.Close()
	defer a.Close()
	port := a.LocalAddr().(*net.TCPAddr).Port
	d.SetWriteDeadline(time.Now().Add(300 * time.Millisecond))
	k, _ := d.Write(fill(8<<20, 'z'))
	rule := []string{"OUTPUT", "-p", "tcp", "--sport", fmt.Sprint(port), "-j", "REJECT",
		"--reject-with", "tcp-reset"}
	if err := iptables(append([]string{"-A"}, rule...)...); err != nil {
		return "", err
	}
	defer iptables(append([]string{"-D"}, rule...)...)
	_, ew := a.Write([]byte("!"))
	time.Sleep(100 * time.Millisecond)
	got, errs := readAll(a, time.Second)
	d.SetWriteDeadline(time.Time{})
	var dErrs []string
	for i := 0; i < 3; i++ {
		_, e := d.Write([]byte("more"))
		dErrs = append(dErrs, describe(e))
		time.Sleep(50 * time.Millisecond)
	}
	return sprintf("dialer wrote %d bytes; acceptor's 1-byte Write: %s; acceptor read %d, then %v; dialer's next Writes: %v",
		k, describe(ew), got, errs, dErrs), nil
}
