package swiftnet

import (
	"bytes"
	"fmt"
	"io"
	"math/rand"
	"net"
	"os"
	"os/exec"
	"strconv"
	"strings"
	"testing"

	"github.com/anishathalye/porcupine"
)

// The kit's deployment on loopback (the lab's kit_test.go, ported): every node but the
// orchestrator is this test binary re-executed (SWIFTNET_NODE), one process per node (net/rpc's
// Register and HandleHTTP are per process): nodes 1..NC the client nodes (clientNode), the others
// the server nodes (serve). Node i's first address is 127.0.0.1:(base+i); its rpc port (a
// replica's) or request port (a client node's) is RPCOff above, its configuration port ConfOff
// above. The orchestrator is the test (orch). It takes about a minute (the start-up wait StartMs,
// the replicas' start-up, then each client's Connect). Run with the real net/rpc (go test).

func TestMain(m *testing.M) {
	if id := os.Getenv("SWIFTNET_NODE"); id != "" {
		n, err := strconv.ParseUint(id, 10, 64)
		if err != nil {
			panic(err)
		}
		addrs := strings.Split(os.Getenv("SWIFTNET_ADDRS"), ",")
		if n >= 1 && n <= NC {
			clientNode(addrs, at(addrs, n, RPCOff), n-1)
		}
		serve(n-NC, addrs)
		os.Exit(0)
	}
	os.Exit(m.Run())
}

// freeBase finds a port base b such that b+i, b+i+RPCOff and b+i+ConfOff (i < n) are free on
// loopback (below Linux's ephemeral ports).
func freeBase(t *testing.T, n int) uint64 {
	for b := 20000 + rand.Intn(10000); b < 32768-int(ConfOff)-n; b += 97 {
		ok := true
		var ls []net.Listener
		for i := 0; i < n && ok; i++ {
			for _, p := range []int{b + i, b + i + int(RPCOff), b + i + int(ConfOff)} {
				l, err := net.Listen("tcp", fmt.Sprintf("127.0.0.1:%d", p))
				if err != nil {
					ok = false
					break
				}
				ls = append(ls, l)
			}
		}
		for _, l := range ls {
			l.Close()
		}
		if ok {
			return uint64(b)
		}
	}
	t.Fatal("no free ports")
	return 0
}

// TestDeployment runs the kit's thirteen nodes on loopback, each but the orchestrator a process
// of its own; orch panics unless porcupine accepts the history.
func TestDeployment(t *testing.T) {
	if testing.Short() {
		t.Skip("a minute of start-up")
	}
	n := len(Addrs())
	base := freeBase(t, n)
	var addrs []string
	for i := 0; i < n; i++ {
		addrs = append(addrs, fmt.Sprintf("127.0.0.1:%d", base+uint64(i)))
	}
	exited := make(chan string, n)
	for id := 1; id < n; id++ {
		cmd := exec.Command(os.Args[0], "-test.run=^$")
		cmd.Env = append(os.Environ(), fmt.Sprintf("SWIFTNET_NODE=%d", id),
			"SWIFTNET_ADDRS="+strings.Join(addrs, ","))
		var out bytes.Buffer
		cmd.Stdout = &out
		cmd.Stderr = &out
		if testing.Verbose() {
			cmd.Stderr = io.MultiWriter(os.Stderr, &out)
			cmd.Stdout = cmd.Stderr
		}
		if err := cmd.Start(); err != nil {
			t.Fatal(err)
		}
		t.Cleanup(func() { cmd.Process.Kill() })
		go func(id int) {
			err := cmd.Wait()
			exited <- fmt.Sprintf("node %d ended (%v):\n%s", id, err, out.String())
		}(id)
	}
	var caddrs []string
	for c := uint64(0); c < NC; c++ {
		caddrs = append(caddrs, at(addrs, 1+c, RPCOff))
	}
	orch(addrs, caddrs)
	select {
	case e := <-exited:
		t.Fatal(e)
	default:
	}
}

func opH(put bool, k uint64, v string, out Out, call, ret int64) porcupine.Operation {
	return porcupine.Operation{Input: In{Put: put, K: k, V: v}, Output: out, Call: call, Return: ret}
}

// The model: a sequential history is accepted, a stale get rejected, a pending put may take
// effect late or never, a value read from a pending put stays.
func TestModel(t *testing.T) {
	m := Model()
	ok := []porcupine.Operation{
		opH(true, 0, "a", Out{}, 0, 1),
		opH(false, 0, "", Out{V: "a"}, 2, 3),
		opH(false, 1, "", Out{V: ""}, 4, 5),
	}
	if !porcupine.CheckOperations(m, ok) {
		t.Fatal("sequential history rejected")
	}
	stale := []porcupine.Operation{
		opH(true, 0, "a", Out{}, 0, 1),
		opH(true, 0, "b", Out{}, 2, 3),
		opH(false, 0, "", Out{V: "a"}, 4, 5),
	}
	if porcupine.CheckOperations(m, stale) {
		t.Fatal("stale get accepted")
	}
	pend := []porcupine.Operation{
		opH(true, 0, "a", Out{Unknown: true}, 0, 1),
		opH(false, 0, "", Out{V: ""}, 2, 3),
		opH(false, 0, "", Out{V: "a"}, 4, 5),
		opH(false, 0, "", Out{V: "a"}, 6, 7),
	}
	if !porcupine.CheckOperations(m, pend) {
		t.Fatal("late pending put rejected")
	}
	back := append(pend, opH(false, 0, "", Out{V: ""}, 8, 9))
	if porcupine.CheckOperations(m, back) {
		t.Fatal("value went back after a pending put took effect")
	}
}

// Gen's inputs decode as they encode, their keys are below NKeys and put values never empty.
func TestGenCodec(t *testing.T) {
	cd := Codec()
	for i := 0; i < 1000; i++ {
		in := Gen(i % int(NC)).(In)
		if in.K >= NKeys || (in.Put && in.V == "") {
			t.Fatalf("bad input %+v", in)
		}
		got, ok := cd.DecIn(cd.EncIn(in))
		if !ok || got.(In) != in {
			t.Fatalf("codec: %+v -> %+v", in, got)
		}
	}
}
