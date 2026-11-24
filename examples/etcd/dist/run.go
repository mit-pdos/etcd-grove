package dist

import (
	"encoding/json"
	"fmt"
	"math/rand/v2"
	"os"
	"path/filepath"
	"strconv"
	"strings"
	"time"

	"go.uber.org/zap"

	"github.com/mit-pdos/etcd-grove/examples/etcd/dist/client"
	"github.com/mit-pdos/etcd-grove/examples/etcd/dist/deployment"
	"github.com/mit-pdos/etcd-grove/examples/etcd/dist/server"
	"github.com/mit-pdos/etcd-grove/examples/lib/etcdstart"
	"github.com/mit-pdos/etcd-grove/examples/lib/robust"
)

// The processes' roles, the first argument of RunProcess.
const (
	RoleServer = "server" // a member: server.MainDeployment
	RoleClient = "client" // a workload's orchestrator: client.MainDeployment
	RoleNode   = "node"   // a workload's client machine: client.NodeDeployment
)

// ReadyFile is the file the orchestrator of workload j marks its set-up done with, beside the
// deployment's file.
func ReadyFile(file string, j int) string {
	return fmt.Sprintf("%s.client-%d.ready", file, j)
}

// RunProcess runs a test process: ROLE DEPLOYMENT.json INDEX, the whole deployment's JSON and the
// machine's index (among the members, the workloads, or the client machines in Deployment.Node's
// order). Role RoleServer runs server.MainDeployment (with DIST_LOG set, MainDeploymentLogger to
// standard error); RoleClient client.MainDeployment, its result printed, its set-up done marked by
// ReadyFile, for the test to hold its faults until then; RoleNode client.NodeDeployment, which never
// returns on a well-formed deployment. What cmd/server and cmd/client do, for a binary that is both
// (the test binary).
func RunProcess(args []string) error {
	if len(args) != 3 {
		return fmt.Errorf("usage: server|client|node DEPLOYMENT.json INDEX")
	}
	b, err := os.ReadFile(args[1])
	if err != nil {
		return err
	}
	var d Deployment
	if err := json.Unmarshal(b, &d); err != nil {
		return err
	}
	i, err := strconv.Atoi(args[2])
	if err != nil {
		return err
	}
	switch args[0] {
	case RoleServer:
		lg := zap.NewNop()
		if os.Getenv("DIST_LOG") != "" {
			if l, err := zap.NewDevelopment(); err == nil {
				lg = l
			}
		}
		server.MainDeploymentLogger(d, i, lg)
		return fmt.Errorf("server.MainDeployment returned")
	case RoleClient:
		ready := func() { os.WriteFile(ReadyFile(args[1], i), nil, 0o644) }
		r := client.MainDeployment(d, i, ready)
		if i >= 0 && i < len(d.Workloads) {
			fmt.Printf("%s: %v\n", d.Workloads[i].Kind, r)
		} else {
			fmt.Printf("%v\n", r)
		}
		return nil
	case RoleNode:
		client.NodeDeployment(d, i)
		return fmt.Errorf("client.NodeDeployment returned")
	}
	return fmt.Errorf("unknown role %q", args[0])
}

// NodePort is the port a workload's client machine serves the orchestrator's calls at, in the
// namespace mode (in the local mode, ports of the one loopback address from 31000).
const NodePort = 2390

// Cluster is a running deployment: its members, restartables of a run (examples/lib/robust's
// Run), its workloads' orchestrator machines and client machines, and the deployment's file.
type Cluster struct {
	d        Deployment
	file     string
	run      *robust.Run
	members  []*robust.Restartable
	clients  []*robust.Machine
	nodes    [][]*robust.Machine // nodes[j][c] is at d.Nodes[j][c]
	machines []*robust.Machine   // every machine of the deployment: the network faults'
}

// Result is a run's outcome: each workload's result line (in the workloads' order), and the first
// failure (a panic, a member exiting on its own, a client not done by the deadline), nil if none.
type Result struct {
	Lines []string
	Err   error
}

// Checked is how many workloads' checks ran.
func (r Result) Checked() int {
	n := 0
	for _, l := range r.Lines {
		if strings.HasSuffix(l, ": checked") {
			n++
		}
	}
	return n
}

// MemberAddrs gives member i's addresses on the machines ms of n: port 2380 (peer) and 2379
// (client) of its machine's address in the namespace mode; in the local mode, ports of the one
// loopback address, from base.
func MemberAddrs(n *robust.Network, ms []*robust.Machine, base int) func(int) (string, string) {
	return func(i int) (string, string) {
		if n.Namespaces() {
			return ms[i].IP + ":2380", ms[i].IP + ":2379"
		}
		return fmt.Sprintf("%s:%d", ms[i].IP, base+2*i), fmt.Sprintf("%s:%d", ms[i].IP, base+2*i+1)
	}
}

// MemberMachines adds k members' machines to n and returns them with their addresses
// (MemberAddrs).
func MemberMachines(n *robust.Network, k int, base int) ([]*robust.Machine, func(int) (string, string), error) {
	var ms []*robust.Machine
	for i := 0; i < k; i++ {
		m, err := n.AddMachine(fmt.Sprintf("member-%d", i))
		if err != nil {
			return nil, nil, err
		}
		ms = append(ms, m)
	}
	return ms, MemberAddrs(n, ms, base), nil
}

// NodeMachines adds the client machines of the workloads ws to n (deployment.NodeCount(ws[j]) for
// workload j) and returns them with their addresses (a Deployment's Nodes): port NodePort of the
// machine's address in the namespace mode; in the local mode, ports of the one loopback address,
// from a random base.
func NodeMachines(n *robust.Network, ws []Workload) ([][]*robust.Machine, [][]string, error) {
	localPort := 31000 + 20*rand.IntN(80)
	var nms [][]*robust.Machine
	var addrs [][]string
	for j, w := range ws {
		var ms []*robust.Machine
		as := []string{}
		for c := 0; c < deployment.NodeCount(w); c++ {
			m, err := n.AddMachine(fmt.Sprintf("client-%d-%s-node-%d", j, w.Kind, c))
			if err != nil {
				return nil, nil, err
			}
			ms = append(ms, m)
			if n.Namespaces() {
				as = append(as, m.IP+":"+strconv.Itoa(NodePort))
			} else {
				as = append(as, fmt.Sprintf("%s:%d", m.IP, localPort))
				localPort++
			}
		}
		nms = append(nms, ms)
		addrs = append(addrs, as)
	}
	return nms, addrs, nil
}

// Start starts the deployment d in the run r on the network n, whose first len(d.Members)
// machines ms are the members' and whose machines nodes are d's client machines (nodes[j][c] at
// d.Nodes[j][c]: NodeMachines): it writes d to the run's work directory (the file every machine's
// process reads); each member is a restartable of a group of its own (its directory, on a disk of
// its own in the power modes), linked from its data directory and WAL area
// (etcdstart.DataBase/<name>.etcd, etcdstart.WALBase/<name>.etcd, the paths server.Main uses), its
// process started with role RoleServer; then an orchestrator machine per workload. The clients are
// started by Run. On an error, it removes its links; the caller stops r.
func Start(d Deployment, r *robust.Run, n *robust.Network, ms []*robust.Machine, nodes [][]*robust.Machine) (_ *Cluster, err error) {
	c := &Cluster{d: d, run: r, nodes: nodes, file: filepath.Join(r.Work(), "deployment.json")}
	defer func() {
		if err != nil {
			c.Stop()
		}
	}()
	b, _ := json.MarshalIndent(d, "", "  ")
	if err := os.WriteFile(c.file, b, 0o644); err != nil {
		return nil, err
	}
	g := r.NewGroup()
	for i := range d.Members {
		mb, err := g.Add(d.Members[i].Name, ms[i])
		if err != nil {
			return nil, err
		}
		c.members = append(c.members, mb)
		for _, sub := range []string{"data", "wal"} {
			if err := os.MkdirAll(filepath.Join(mb.Dir, sub), 0o755); err != nil {
				return nil, err
			}
		}
		name := d.Members[i].Name + ".etcd"
		if err := robust.Symlink(filepath.Join(mb.Dir, "data"), filepath.Join(etcdstart.DataBase, name)); err != nil {
			return nil, err
		}
		if err := robust.Symlink(filepath.Join(mb.Dir, "wal"), filepath.Join(etcdstart.WALBase, name)); err != nil {
			return nil, err
		}
		if err := robust.SyncFS(mb.Dir); err != nil {
			return nil, err
		}
		mb.Args = []string{RoleServer, c.file, strconv.Itoa(i)}
	}
	if err := g.Start(); err != nil {
		return nil, err
	}
	c.machines = append(c.machines, ms...)
	for _, nms := range nodes {
		c.machines = append(c.machines, nms...)
	}
	for j, w := range d.Workloads {
		m, err := n.AddMachine(fmt.Sprintf("client-%d-%s", j, w.Kind))
		if err != nil {
			return nil, err
		}
		c.clients = append(c.clients, m)
		c.machines = append(c.machines, m)
	}
	return c, nil
}

// Run runs the deployment's clients (robust.Run.RunClients: every client machine's process, role
// RoleNode, in Deployment.Node's order, then every workload's orchestrator's, role RoleClient) while
// members crash and the network fails over every machine of the deployment; once they are done, it
// stops the faults. It returns the result; the caller stops the run and the cluster (Stop).
func (c *Cluster) Run() Result {
	var nodes, orchs []robust.Client
	k := 0
	for j, w := range c.d.Workloads {
		for i, nm := range c.nodes[j] {
			nodes = append(nodes, robust.Client{Name: fmt.Sprintf("client-%d-%s-node-%d", j, w.Kind, i),
				Machine: nm, Args: []string{RoleNode, c.file, strconv.Itoa(k)}})
			k++
		}
		orchs = append(orchs, robust.Client{Name: fmt.Sprintf("client-%d-%s", j, w.Kind), Machine: c.clients[j],
			Args: []string{RoleClient, c.file, strconv.Itoa(j)}, Ready: ReadyFile(c.file, j)})
	}
	lines := c.run.RunClientsAwait(nodes, orchs, c.machines, c.await)
	return Result{Lines: lines, Err: c.run.Err()}
}

// How long, and how often, the harness waits for an address to accept a connection (await).
const (
	awaitFor   = 3 * time.Minute
	awaitPause = 100 * time.Millisecond
)

// await is the harness's liveness wait before the orchestrators start (the programs do not retry,
// client.MainReady): from each workload's orchestrator machine, every member's client address
// (a member serves it only once it is ready, server.MainLogger) and the workload's client
// machines' addresses accept a TCP connection, each within awaitFor.
func (c *Cluster) await() error {
	for j := range c.d.Workloads {
		m := c.clients[j]
		addrs := append(c.d.Endpoints(), c.d.Nodes[j]...)
		for _, a := range addrs {
			deadline := time.Now().Add(awaitFor)
			for {
				conn, err := m.Dial(a, time.Second)
				if err == nil {
					conn.Close()
					break
				}
				if time.Now().After(deadline) {
					return fmt.Errorf("%s did not accept a connection from %s within %v", a, m.Name, awaitFor)
				}
				time.Sleep(awaitPause)
			}
		}
	}
	return nil
}

// Stop removes the members' links (the run's Stop kills the members and removes their disks).
func (c *Cluster) Stop() {
	for _, m := range c.d.Members {
		name := m.Name + ".etcd"
		os.Remove(filepath.Join(etcdstart.DataBase, name))
		os.Remove(filepath.Join(etcdstart.WALBase, name))
	}
}
