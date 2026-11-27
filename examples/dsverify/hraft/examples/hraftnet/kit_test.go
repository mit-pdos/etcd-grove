package hraftnet

import (
	"fmt"
	"net"
	"os"
	"os/exec"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"
	"testing"
	"time"

	"github.com/anishathalye/porcupine"
	"github.com/hashicorp/raft/examples/hraftnet/rpctransport"
	"github.com/hashicorp/raft/examples/hraftnet/service"
	"github.com/mit-pdos/etcd-grove/examples/lib/remote"
)

// The deployment's machines listen at 10.77.k.1 (kit_gen.go; examples/lib/robust's machine
// addresses). TestDeployment runs all twelve in this process, in a network namespace of its own
// whose loopback holds those addresses (a child of this test: unshare -rn, which needs user
// namespaces or root). Each run is a child of its own (the servers never stop, and hold their
// ports), so runs are independent and may run in parallel.
// (The multi-process deployment, one network namespace per machine with the network faults the
// kernel makes, is examples/dsverify/hraftrobust's, over the machines of ./covmachine.)

// The variables a child of TestDeployment reads.
const (
	childVar = "HRAFTNET_CHILD" // "1": this process is a run's child, in its namespace
	runsVar  = "HRAFTNET_RUNS"  // how many runs TestDeployment makes (default 4)
	parVar   = "HRAFTNET_PAR"   // how many runs at once (default 4)
	warmVar  = "HRAFTNET_WARM"  // how long (ms) a run's admin runs before the clients (default 3000)
	opsVar   = "HRAFTNET_OPS"   // the operations per client (default testOps)
)

// testOps is the tests' operations per client: one of the numbers Orch draws (1..MaxOps), small
// so that porcupine's check of the history, run to completion, ends quickly.
const testOps = 8

// machineIPs is every machine's address: servers 1..6, clients 0..4, the orchestrator.
func machineIPs() []string {
	var ips []string
	for k := 1; k <= 12; k++ {
		ips = append(ips, fmt.Sprintf("10.77.%d.1", k))
	}
	return ips
}

// inNamespace says whether the deployment's addresses can be listened on here.
func inNamespace() bool {
	l, err := net.Listen("tcp", "10.77.1.1:0")
	if err != nil {
		return false
	}
	l.Close()
	return true
}

// runChild runs TestDeploymentRun in a child in a network namespace of its own, with the
// deployment's addresses on its loopback; its output.
func runChild(t *testing.T) (string, error) {
	exe, err := os.Executable()
	if err != nil {
		t.Fatal(err)
	}
	script := "ip link set lo up"
	for _, ip := range machineIPs() {
		script += " && ip addr add " + ip + "/32 dev lo"
	}
	script += " && exec \"$0\" \"$@\""
	args := []string{"-rn", "sh", "-c", script, exe, "-test.run=^TestDeploymentRun$", "-test.v", "-test.count=1"}
	if d := os.Getenv("HRAFTNET_COVERPROFILE"); d != "" {
		f, err := os.CreateTemp(d, "cover-*.out")
		if err != nil {
			t.Fatal(err)
		}
		f.Close()
		args = append(args, "-test.coverprofile="+f.Name())
	}
	cmd := exec.Command("unshare", args...)
	cmd.Env = append(os.Environ(), childVar+"=1")
	out, err := cmd.CombinedOutput()
	return string(out), err
}

func envInt(name string, def int) int {
	if v, err := strconv.Atoi(os.Getenv(name)); err == nil && v > 0 {
		return v
	}
	return def
}

// TestDeployment (the non-vacuity test) makes HRAFTNET_RUNS runs of the deployment, each in a
// child (TestDeploymentRun): porcupine must accept every history, and over the runs every kind of
// operation must be answered and every kind of the admin's requests must succeed (the
// configuration chosen, n0 = 3 and 5, both reached).
func TestDeployment(t *testing.T) {
	if os.Getenv(childVar) != "" {
		t.Skip("a child runs TestDeploymentRun only")
	}
	if exec.Command("unshare", "-rn", "true").Run() != nil {
		t.Skip("no network namespaces (unshare -rn): run as root or with user namespaces")
	}
	runs, par := envInt(runsVar, 4), envInt(parVar, 4)
	totals := map[string]int{}
	var mu sync.Mutex
	sem := make(chan bool, par)
	var wg sync.WaitGroup
	for i := 0; i < runs; i++ {
		wg.Add(1)
		sem <- true
		go func(i int) {
			defer wg.Done()
			defer func() { <-sem }()
			out, err := runChild(t)
			mu.Lock()
			defer mu.Unlock()
			if err != nil {
				t.Errorf("run %d: %v\n%s", i, err, out)
				return
			}
			for _, l := range strings.Split(out, "\n") {
				if k := strings.Index(l, "hraftnet-count "); k >= 0 {
					f := strings.Fields(l[k:])
					if len(f) == 3 {
						n, _ := strconv.Atoi(f[2])
						totals[f[1]] += n
					}
				}
			}
		}(i)
	}
	wg.Wait()
	t.Logf("over %d runs: %v", runs, totals)
	for _, k := range []string{"put", "read-log", "read-barrier", "read-verify", "AddVoter", "AddNonvoter",
		"DemoteVoter", "RemoveServer", "LeadershipTransfer", "Snapshot"} {
		if totals[k] == 0 {
			t.Errorf("no %s answered (succeeded) over %d runs", k, runs)
		}
	}
}

// kind is an operation's kind, for the counts.
func kind(x In) string {
	if x.Put {
		return "put"
	}
	return []string{"read-log", "read-barrier", "read-verify"}[x.Way]
}

// TestDeploymentRun is one run of the deployment, in this process (in a child of TestDeployment):
// the six servers and five client machines (Server, Client, as their commands run them, but with
// a client's operations counted by kind), then the orchestrator's steps (Orch's, with the admin's
// successes counted and remote.Run in place of remote.Check, at HRAFTNET_OPS operations per client
// (default testOps: a small number Orch can draw),
// after the admin has run alone for HRAFTNET_WARM ms).
func TestDeploymentRun(t *testing.T) {
	if os.Getenv(childVar) == "" || !inNamespace() {
		t.Skip("run by TestDeployment, in a namespace of its own")
	}
	for id := uint64(1); id <= NS; id++ {
		go Server(id)
	}
	var counts sync.Map
	count := func(k string) {
		v, _ := counts.LoadOrStore(k, new(atomic.Int64))
		v.(*atomic.Int64).Add(1)
	}
	for c := uint64(0); c < NC; c++ {
		go func(c uint64) {
			Register()
			newClient := func(id int) any {
				return &Sys{c: c, conns: serverConns(), j: 1 + rnd(NS)}
			}
			opc := func(sys any, in any) any {
				x := in.(In)
				o := sys.(*Sys).op(x)
				if !o.Unknown {
					count(kind(x))
				}
				return o
			}
			remote.ServeClient(int(c), ClientAddrs()[c], newClient, opc, Codec(), attempt())
		}(c)
	}
	n0 := chooseN0()
	configure(n0)
	Register()
	stop := make(chan bool)
	go func() {
		conns := serverConns()
		ms := adminMethods()
		for {
			select {
			case <-stop:
				return
			default:
			}
			time.Sleep(time.Duration(rnd(AdminMs)) * time.Millisecond)
			j := adminTarget(conns)
			k := rnd(uint64(len(ms)))
			s := 1 + rnd(NS)
			args := &service.AdminArgs{ID: string(serverID(s)), Addr: string(serverAddr(s))}
			if k == 4 && rnd(2) == 0 {
				args = &service.AdminArgs{ID: "", Addr: ""}
			}
			reply := new(service.AdminReply)
			if conns[j-1].Call(ms[k], args, reply, apiTimeout()) == rpctransport.CallOK && reply.Ok {
				count(strings.TrimPrefix(ms[k], "API."))
			}
		}
	}()
	// the admin alone for a while first (the test's schedule: in the theorem, any)
	time.Sleep(time.Duration(envInt(warmVar, 3000)) * time.Millisecond)
	r := remote.Run(Model(), ClientAddrs(), Codec(), Gen, envInt(opsVar, testOps), attempt(), 0)
	close(stop)
	if r != porcupine.Ok {
		t.Fatalf("porcupine: %v (n0 = %d)", r, n0)
	}
	fmt.Printf("hraftnet-count n0=%d 1\n", n0)
	counts.Range(func(k, v any) bool {
		fmt.Printf("hraftnet-count %s %d\n", k, v.(*atomic.Int64).Load())
		return true
	})
}

// TestControlStale (the negative control): client machines whose reads return the first value
// they ever wrote, as a server that serves stale reads would, are caught (two operations a client:
// porcupine's search of a rejected history, with Model's Equal always false, grows fast with its
// length).
func TestControlStale(t *testing.T) {
	var addrs []string
	for c := uint64(0); c < NC; c++ {
		l, err := net.Listen("tcp", "127.0.0.1:0")
		if err != nil {
			t.Fatal(err)
		}
		addrs = append(addrs, l.Addr().String())
		l.Close()
	}
	var mu sync.Mutex
	var first string
	stale := func(sys any, in any) any {
		x := in.(In)
		mu.Lock()
		defer mu.Unlock()
		if x.Put {
			if first == "" {
				first = x.V
			}
			return Out{}
		}
		if first == "" {
			return Out{}
		}
		return Out{Found: true, V: first}
	}
	for c := range addrs {
		go remote.ServeClient(c, addrs[c], func(int) any { return nil }, stale, Codec(), attempt())
	}
	time.Sleep(200 * time.Millisecond)
	illegal := false
	for i := 0; i < 20 && !illegal; i++ {
		illegal = remote.Run(Model(), addrs, Codec(), Gen, 2, attempt(), 0) == porcupine.Illegal
	}
	if !illegal {
		t.Fatalf("porcupine accepted every stale history")
	}
}
