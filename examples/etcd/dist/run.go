package dist

import (
	"encoding/json"
	"fmt"
	"math/rand/v2"
	"os"
	"path/filepath"
	"strconv"
	"strings"

	"go.uber.org/zap"

	"github.com/mit-pdos/etcd-grove/examples/etcd/dist/client"
	"github.com/mit-pdos/etcd-grove/examples/etcd/dist/server"
	"github.com/mit-pdos/etcd-grove/examples/lib/etcdstart"
	"github.com/mit-pdos/etcd-grove/examples/lib/robust"
)

// The processes' roles, the first argument of RunProcess.
const (
	RoleServer = "server"
	RoleClient = "client"
)

// RunProcess runs a test process: role RoleServer with a server.Config's JSON file (server.Main;
// with DIST_LOG set, MainLogger to standard error), or RoleClient with a client.Args JSON file
// (client.MainReady, its result printed; its set-up done marked by the file FILE.json.ready, for
// the test to hold its faults until then; or, on a workload's client machine, client.NodeMain,
// which never returns). What cmd/server and cmd/client do, for a binary that is both
// (the test binary).
func RunProcess(args []string) error {
	if len(args) != 2 {
		return fmt.Errorf("usage: server|client FILE.json")
	}
	b, err := os.ReadFile(args[1])
	if err != nil {
		return err
	}
	switch args[0] {
	case RoleServer:
		var c server.Config
		if err := json.Unmarshal(b, &c); err != nil {
			return err
		}
		if os.Getenv("DIST_LOG") != "" {
			if lg, err := zap.NewDevelopment(); err == nil {
				server.MainLogger(c, lg)
				return fmt.Errorf("server.Main returned")
			}
		}
		server.Main(c)
		return fmt.Errorf("server.Main returned")
	case RoleClient:
		var a client.Args
		if err := json.Unmarshal(b, &a); err != nil {
			return err
		}
		if a.IsNode {
			if a.Node < 0 || a.Node >= len(a.Nodes) {
				return fmt.Errorf("no client machine %d", a.Node)
			}
			client.NodeMain(a.W, a.Node, a.Nodes[a.Node], a.Eps)
			return fmt.Errorf("client.NodeMain returned")
		}
		ready := func() { os.WriteFile(args[1]+".ready", nil, 0o644) }
		fmt.Printf("%s: %v\n", a.W.Kind, client.MainReady(a.W, a.Eps, a.Nodes, ready))
		return nil
	}
	return fmt.Errorf("unknown role %q", args[0])
}

// NodePort is the port a workload's client machine serves the orchestrator's calls at, in the
// namespace mode (in the local mode, ports of the one loopback address from 31000).
const NodePort = 2390

// Cluster is a running deployment: its members, restartables of a run (examples/lib/robust's
// Run), and its workloads' client machines.
type Cluster struct {
	d       Deployment
	run     *robust.Run
	members []*robust.Restartable
	clients []*robust.Machine
	// nodes[i] are workload i's client machines (client.NodeCount), at nodeAddrs[i]
	nodes     [][]*robust.Machine
	nodeAddrs [][]string
	machines  []*robust.Machine // every machine of the deployment: the network faults'
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

// Start starts the deployment d in the run r on the network n, whose first len(d.Members)
// machines ms are the members': each member a restartable of a group of its own (its directory,
// on a disk of its own in the power modes), linked from its data directory and WAL area
// (etcdstart.DataBase/<name>.etcd, etcdstart.WALBase/<name>.etcd, the paths server.Main uses), its
// process started with role RoleServer; then a machine per workload. The clients are started by
// Run. On an error, it removes its links; the caller stops r.
func Start(d Deployment, r *robust.Run, n *robust.Network, ms []*robust.Machine) (_ *Cluster, err error) {
	c := &Cluster{d: d, run: r}
	defer func() {
		if err != nil {
			c.Stop()
		}
	}()
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
		b, _ := json.MarshalIndent(d.ServerConfig(i), "", "  ")
		cfg := filepath.Join(r.Work(), d.Members[i].Name+".json")
		if err := os.WriteFile(cfg, b, 0o644); err != nil {
			return nil, err
		}
		mb.Args = []string{RoleServer, cfg}
	}
	if err := g.Start(); err != nil {
		return nil, err
	}
	localPort := 31000 + 20*rand.IntN(80)
	c.machines = append(c.machines, ms...)
	for i, w := range d.Workloads {
		m, err := n.AddMachine(fmt.Sprintf("client-%d-%s", i, w.Kind))
		if err != nil {
			return nil, err
		}
		c.clients = append(c.clients, m)
		c.machines = append(c.machines, m)
		var nms []*robust.Machine
		var addrs []string
		for j := 0; j < client.NodeCount(w); j++ {
			nm, err := n.AddMachine(fmt.Sprintf("client-%d-%s-node-%d", i, w.Kind, j))
			if err != nil {
				return nil, err
			}
			nms = append(nms, nm)
			c.machines = append(c.machines, nm)
			if n.Namespaces() {
				addrs = append(addrs, nm.IP+":"+strconv.Itoa(NodePort))
			} else {
				addrs = append(addrs, fmt.Sprintf("%s:%d", nm.IP, localPort))
				localPort++
			}
		}
		c.nodes = append(c.nodes, nms)
		c.nodeAddrs = append(c.nodeAddrs, addrs)
	}
	return c, nil
}

// Run runs the deployment's clients (robust.Run.RunClients: every workload's client machines'
// processes, client.NodeMain, then its orchestrator's, client.MainReady, each with role
// RoleClient and a client.Args file) while members crash and the network fails over every machine
// of the deployment; once they are done, it stops the faults. It returns the result; the caller
// stops the run and the cluster (Stop).
func (c *Cluster) Run() Result {
	eps := c.d.Endpoints()
	r := c.run
	var nodes, orchs []robust.Client
	write := func(name string, a client.Args) (string, error) {
		b, _ := json.Marshal(a)
		p := filepath.Join(r.Work(), name+".json")
		return p, os.WriteFile(p, b, 0o644)
	}
	for i, w := range c.d.Workloads {
		for j, nm := range c.nodes[i] {
			p, err := write(fmt.Sprintf("client-%d-node-%d", i, j),
				client.Args{W: w, Eps: eps, Nodes: c.nodeAddrs[i], IsNode: true, Node: j})
			if err != nil {
				return Result{Err: err}
			}
			nodes = append(nodes, robust.Client{Name: fmt.Sprintf("client-%d-%s-node-%d", i, w.Kind, j),
				Machine: nm, Args: []string{RoleClient, p}})
		}
		p, err := write(fmt.Sprintf("client-%d", i), client.Args{W: w, Eps: eps, Nodes: c.nodeAddrs[i]})
		if err != nil {
			return Result{Err: err}
		}
		orchs = append(orchs, robust.Client{Name: fmt.Sprintf("client-%d-%s", i, w.Kind), Machine: c.clients[i],
			Args: []string{RoleClient, p}, Ready: p + ".ready"})
	}
	lines := r.RunClients(nodes, orchs, c.machines)
	return Result{Lines: lines, Err: r.Err()}
}

// Stop removes the members' links (the run's Stop kills the members and removes their disks).
func (c *Cluster) Stop() {
	for _, m := range c.d.Members {
		name := m.Name + ".etcd"
		os.Remove(filepath.Join(etcdstart.DataBase, name))
		os.Remove(filepath.Join(etcdstart.WALBase, name))
	}
}
