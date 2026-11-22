package harness

import (
	"encoding/json"
	"fmt"
	"math/rand/v2"
	"os"
	"path/filepath"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"
	"time"

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

// RunProcess runs a harness process: role RoleServer with a server.Config's JSON file (server.Main;
// with DIST_LOG set, MainLogger to standard error), or RoleClient with a client.Args JSON file
// (client.MainReady, its result printed; its set-up done marked by the file FILE.json.ready, for
// the harness to hold its faults until then; or, on a workload's client machine, client.NodeMain,
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

// Crash modes (kvnet's driver's).
const (
	CrashKill  = "kill"  // SIGKILL, then syncfs of the member's filesystem, then restart
	CrashPower = "power" // SIGKILL, then a power loss of the member's disk, then restart
	CrashMixed = "mixed" // either, at random
)

// Config is a run's faults and limits.
type Config struct {
	Crash      string        // CrashKill, CrashPower or CrashMixed (the last two need disks)
	CrashPause time.Duration // between two crashes, on average (0: none)
	Downtime   time.Duration // a crashed member stays down a random time below it
	Netns      bool          // machines are network namespaces, with network faults
	NetPause   time.Duration // between two network faults, on average (0: none)
	NetHold    time.Duration // how long a network fault lasts, on average
	Deadline   time.Duration // the run fails if a client is not done by then
	// FaultsAtStart makes the faults from the start, through the workloads' set-ups (which then
	// often end a workload: auth's set-up cannot be redone after an unknown outcome); otherwise
	// they start once every workload's set-up is done or the workload ended, or after SetupWait.
	FaultsAtStart bool
	SetupWait     time.Duration
}

// Command says how to start the harness's processes: the program and the environment added; the
// program runs RunProcess on its arguments (role, file).
type Command struct {
	Path string
	Env  []string
}

// member is a member's machine, directory, disk (nil but in the power modes), process and
// incarnations.
type member struct {
	i     int
	m     *robust.Machine
	dir   string // its files: data/ (its data directory) and wal/ (its WAL area)
	disk  *robust.Disk
	cfg   string // its configuration's file
	p     *robust.Proc
	count int
}

// Stats counts the faults made.
type Stats struct {
	Kills, PowerLosses, Restarts atomic.Uint64
	// SetupsDone is how many workloads had marked their set-up done when the faults started (all,
	// unless the wait ran out or a workload ended first); FaultsAfter is when they started, from
	// the clients' start.
	SetupsDone  atomic.Int64
	FaultsAfter atomic.Int64
}

func (s *Stats) String() string {
	return fmt.Sprintf("kills %d, power losses %d; faults from %v, %d set-ups done then",
		s.Kills.Load(), s.PowerLosses.Load(), time.Duration(s.FaultsAfter.Load()).Round(100*time.Millisecond),
		s.SetupsDone.Load())
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

// Cluster is a running deployment.
type Cluster struct {
	d       Deployment
	cfg     Config
	cmd     Command
	work    string
	net     *robust.Network
	members []*member
	clients []*robust.Machine
	// nodes[i] are workload i's client machines (client.NodeCount), at nodeAddrs[i]
	nodes     [][]*robust.Machine
	nodeAddrs [][]string
	nemesis   *robust.NetNemesis
	Stats     Stats

	mu      sync.Mutex
	crashMu sync.Mutex

	failOnce sync.Once
	failed   chan struct{}
	failErr  error
}

// fail records the run's first failure.
func (c *Cluster) fail(err error) {
	c.failOnce.Do(func() {
		c.failErr = err
		close(c.failed)
	})
}

// Err is the run's first failure, or nil.
func (c *Cluster) Err() error {
	select {
	case <-c.failed:
		return c.failErr
	default:
		return nil
	}
}

// tail is the last n lines of the file path.
func tail(path string, n int) string {
	b, _ := os.ReadFile(path)
	lines := strings.Split(strings.TrimRight(string(b), "\n"), "\n")
	if len(lines) > n {
		lines = lines[len(lines)-n:]
	}
	return strings.Join(lines, "\n")
}

// NewNet makes the run's network: namespaces (netns) or the local mode.
func NewNet(netns bool) (*robust.Network, error) {
	if !netns {
		return robust.LocalNetwork(), nil
	}
	return robust.NewNetwork(fmt.Sprintf("ed%d", os.Getpid()%100000))
}

// MemberMachines adds k members' machines to n and returns them with the function that gives
// member i's addresses: port 2380 (peer) and 2379 (client) of its machine's address in the
// namespace mode; in the local mode, ports of the one loopback address, from base.
func MemberMachines(n *robust.Network, k int, base int) ([]*robust.Machine, func(int) (string, string), error) {
	var ms []*robust.Machine
	for i := 0; i < k; i++ {
		m, err := n.AddMachine(fmt.Sprintf("member-%d", i))
		if err != nil {
			return nil, nil, err
		}
		ms = append(ms, m)
	}
	addr := func(i int) (string, string) {
		if n.Namespaces() {
			return ms[i].IP + ":2380", ms[i].IP + ":2379"
		}
		return fmt.Sprintf("%s:%d", ms[i].IP, base+2*i), fmt.Sprintf("%s:%d", ms[i].IP, base+2*i+1)
	}
	return ms, addr, nil
}

// link makes path a symbolic link to target, replacing what is there.
func link(target, path string) error {
	os.Remove(path)
	if err := os.MkdirAll(filepath.Dir(path), 0o755); err != nil {
		return err
	}
	return os.Symlink(target, path)
}

// Start starts the deployment d on the network n, whose first len(d.Members) machines ms are the
// members': each member's directory (on a disk of its own in the power modes) under work, linked
// from its data directory and WAL area (etcdstart.DataBase/<name>.etcd, etcdstart.WALBase/<name>.etcd,
// the paths server.Main uses), and its process; then a machine per workload. The clients are
// started by Run.
func Start(d Deployment, cfg Config, cmd Command, work string, n *robust.Network, ms []*robust.Machine) (*Cluster, error) {
	if err := os.MkdirAll(filepath.Join(work, "logs"), 0o755); err != nil {
		return nil, err
	}
	c := &Cluster{d: d, cfg: cfg, cmd: cmd, work: work, net: n, failed: make(chan struct{})}
	for i := range d.Members {
		mb := &member{i: i, m: ms[i], dir: filepath.Join(work, d.Members[i].Name)}
		if cfg.Crash != CrashKill {
			dk, err := robust.NewDisk(work, d.Members[i].Name+"-disk")
			if err != nil {
				c.Stop()
				return nil, err
			}
			mb.disk, mb.dir = dk, dk.Mnt
		}
		c.members = append(c.members, mb)
		for _, sub := range []string{"data", "wal"} {
			if err := os.MkdirAll(filepath.Join(mb.dir, sub), 0o755); err != nil {
				c.Stop()
				return nil, err
			}
		}
		name := d.Members[i].Name + ".etcd"
		if err := link(filepath.Join(mb.dir, "data"), filepath.Join(etcdstart.DataBase, name)); err != nil {
			c.Stop()
			return nil, err
		}
		if err := link(filepath.Join(mb.dir, "wal"), filepath.Join(etcdstart.WALBase, name)); err != nil {
			c.Stop()
			return nil, err
		}
		if err := robust.SyncFS(mb.dir); err != nil {
			c.Stop()
			return nil, err
		}
		b, _ := json.MarshalIndent(d.ServerConfig(i), "", "  ")
		mb.cfg = filepath.Join(work, d.Members[i].Name+".json")
		if err := os.WriteFile(mb.cfg, b, 0o644); err != nil {
			c.Stop()
			return nil, err
		}
	}
	for _, mb := range c.members {
		if err := c.start(mb); err != nil {
			c.Stop()
			return nil, err
		}
	}
	localPort := 31000 + 20*rand.IntN(80)
	var all []*robust.Machine
	all = append(all, ms...)
	for i, w := range d.Workloads {
		m, err := n.AddMachine(fmt.Sprintf("client-%d-%s", i, w.Kind))
		if err != nil {
			c.Stop()
			return nil, err
		}
		c.clients = append(c.clients, m)
		all = append(all, m)
		var nms []*robust.Machine
		var addrs []string
		for j := 0; j < client.NodeCount(w); j++ {
			nm, err := n.AddMachine(fmt.Sprintf("client-%d-%s-node-%d", i, w.Kind, j))
			if err != nil {
				c.Stop()
				return nil, err
			}
			nms = append(nms, nm)
			all = append(all, nm)
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
	if cfg.Netns && cfg.NetPause != 0 {
		c.nemesis = &robust.NetNemesis{Net: n, Machines: all, Pause: cfg.NetPause, Hold: cfg.NetHold}
	}
	return c, nil
}

// start starts mb's next incarnation: a process that ends without the harness killing it fails
// the run.
func (c *Cluster) start(mb *member) error {
	c.mu.Lock()
	mb.count++
	count := mb.count
	c.mu.Unlock()
	name := c.d.Members[mb.i].Name
	logPath := filepath.Join(c.work, "logs", name+".log")
	lf, err := os.OpenFile(logPath, os.O_CREATE|os.O_APPEND|os.O_WRONLY, 0o644)
	if err != nil {
		return err
	}
	fmt.Fprintf(lf, "=== incarnation %d\n", count)
	p, err := mb.m.Start(c.cmd.Path, []string{RoleServer, mb.cfg}, c.cmd.Env, lf, func(err error) {
		c.fail(fmt.Errorf("member %s (incarnation %d) exited on its own (%v); its log %s:\n%s",
			name, count, err, logPath, tail(logPath, 40)))
	})
	if err != nil {
		lf.Close()
		return err
	}
	go func() {
		<-p.Exited()
		lf.Close()
	}()
	c.mu.Lock()
	mb.p = p
	c.mu.Unlock()
	return nil
}

// crash crashes member i (SIGKILL, then its files synced or its disk's power lost) and restarts it
// after a random downtime.
func (c *Cluster) crash(i int) {
	c.crashMu.Lock()
	defer c.crashMu.Unlock()
	mb := c.members[i]
	mb.p.Kill()
	power := c.cfg.Crash == CrashPower || (c.cfg.Crash == CrashMixed && rand.IntN(2) == 0)
	var err error
	if power {
		c.Stats.PowerLosses.Add(1)
		err = mb.disk.PowerLoss()
	} else {
		c.Stats.Kills.Add(1)
		err = robust.SyncFS(mb.dir)
	}
	if err != nil {
		c.fail(fmt.Errorf("crash of member %d: %v", i, err))
		return
	}
	time.Sleep(time.Duration(rand.Int64N(int64(c.cfg.Downtime) + 1)))
	if err := c.start(mb); err != nil {
		c.fail(fmt.Errorf("restart of member %d: %v", i, err))
	}
}

// crasher crashes a random member at once, then at random times until stop (the first at once,
// so that a short workload, done within seconds of the faults' start, meets one).
func (c *Cluster) crasher(stop <-chan struct{}) {
	c.crash(rand.IntN(len(c.members)))
	for {
		select {
		case <-stop:
			return
		case <-c.failed:
			return
		case <-time.After(time.Duration(rand.Int64N(2*int64(c.cfg.CrashPause) + 1))):
		}
		c.crash(rand.IntN(len(c.members)))
	}
}

// startNodes starts workload i's client machines' processes (client.NodeMain): one that ends
// before the harness kills it (a panic: a principal's failed check) fails the run.
func (c *Cluster) startNodes(i int, eps []string) ([]*robust.Proc, error) {
	w := c.d.Workloads[i]
	var procs []*robust.Proc
	for j, nm := range c.nodes[i] {
		b, _ := json.Marshal(client.Args{W: w, Eps: eps, Nodes: c.nodeAddrs[i], IsNode: true, Node: j})
		argPath := filepath.Join(c.work, fmt.Sprintf("client-%d-node-%d.json", i, j))
		logPath := filepath.Join(c.work, "logs", fmt.Sprintf("client-%d-%s-node-%d.log", i, w.Kind, j))
		if err := os.WriteFile(argPath, b, 0o644); err != nil {
			return procs, err
		}
		lf, err := os.Create(logPath)
		if err != nil {
			return procs, err
		}
		p, err := nm.Start(c.cmd.Path, []string{RoleClient, argPath}, c.cmd.Env, lf, func(err error) {
			c.fail(fmt.Errorf("client %d (%s)'s machine %d exited (%v); its log:\n%s", i, w.Kind, j, err,
				tail(logPath, 30)))
		})
		if err != nil {
			lf.Close()
			return procs, err
		}
		go func() {
			<-p.Exited()
			lf.Close()
		}()
		procs = append(procs, p)
	}
	return procs, nil
}

// runClients starts every workload's processes on their machines (its client machines', then its
// orchestrator's) and waits for every orchestrator to end, or for the deadline, or for the run to
// fail; then it kills the client machines' processes (which never end) and returns the
// orchestrators' result lines.
func (c *Cluster) runClients(started chan<- []string, exited []atomic.Bool) []string {
	eps := c.d.Endpoints()
	lines := make([]string, len(c.d.Workloads))
	done := make(chan int, len(c.d.Workloads))
	var procs, nodeProcs []*robust.Proc
	var argPaths []string
	defer func() { close(started) }()
	defer func() {
		for _, p := range nodeProcs {
			p.Kill()
		}
	}()
	for i := range c.d.Workloads {
		ps, err := c.startNodes(i, eps)
		nodeProcs = append(nodeProcs, ps...)
		if err != nil {
			c.fail(err)
			return lines
		}
	}
	for i, w := range c.d.Workloads {
		b, _ := json.Marshal(client.Args{W: w, Eps: eps, Nodes: c.nodeAddrs[i]})
		argPath := filepath.Join(c.work, fmt.Sprintf("client-%d.json", i))
		argPaths = append(argPaths, argPath)
		logPath := filepath.Join(c.work, "logs", fmt.Sprintf("client-%d-%s.log", i, w.Kind))
		if err := os.WriteFile(argPath, b, 0o644); err != nil {
			c.fail(err)
			return lines
		}
		lf, err := os.Create(logPath)
		if err != nil {
			c.fail(err)
			return lines
		}
		p, err := c.clients[i].Start(c.cmd.Path, []string{RoleClient, argPath}, c.cmd.Env, lf, func(err error) {
			lf.Close()
			if err != nil {
				c.fail(fmt.Errorf("client %d (%s) failed (%v); its log:\n%s", i, w.Kind, err, tail(logPath, 30)))
			}
			lines[i] = strings.TrimSpace(tail(logPath, 1))
			exited[i].Store(true)
			done <- i
		})
		if err != nil {
			c.fail(err)
			return lines
		}
		procs = append(procs, p)
	}
	started <- argPaths
	deadline := time.After(c.cfg.Deadline)
	for n := 0; n < len(procs); n++ {
		select {
		case <-done:
		case <-deadline:
			c.fail(fmt.Errorf("the clients were not done after %v", c.cfg.Deadline))
		case <-c.failed:
		}
		if c.Err() != nil {
			break
		}
	}
	for _, p := range procs {
		p.Kill()
	}
	return lines
}

// Run runs the deployment's clients while members crash and the network fails; once they are
// done, it stops the faults. It returns the result; the caller stops the cluster (Stop).
func (c *Cluster) Run() Result {
	stop := make(chan struct{})
	started := make(chan []string, 1)
	exited := make([]atomic.Bool, len(c.d.Workloads))
	var wg sync.WaitGroup
	wg.Add(1)
	go func() {
		defer wg.Done()
		t0 := time.Now()
		paths, ok := <-started
		if !ok {
			return
		}
		if !c.cfg.FaultsAtStart && !c.awaitSetUps(paths, exited, stop) {
			return
		}
		c.Stats.FaultsAfter.Store(int64(time.Since(t0)))
		if c.cfg.CrashPause != 0 {
			wg.Add(1)
			go func() { c.crasher(stop); wg.Done() }()
		}
		if c.nemesis != nil {
			wg.Add(1)
			go func() {
				if err := c.nemesis.Run(stop); err != nil {
					c.fail(fmt.Errorf("the network nemesis: %v", err))
				}
				wg.Done()
			}()
		}
	}()
	lines := c.runClients(started, exited)
	close(stop)
	wg.Wait()
	return Result{Lines: lines, Err: c.Err()}
}

// awaitSetUps waits until every client has marked its set-up done (its args file's .ready) or
// ended, or SetupWait has passed; it records how many set-ups were done, and reports false if the
// run stopped first.
func (c *Cluster) awaitSetUps(paths []string, exited []atomic.Bool, stop <-chan struct{}) bool {
	deadline := time.Now().Add(c.cfg.SetupWait)
	for {
		done, all := int64(0), true
		for i, p := range paths {
			if _, err := os.Stat(p + ".ready"); err == nil {
				done++
			} else if !exited[i].Load() {
				all = false
			}
		}
		if all || time.Now().After(deadline) {
			c.Stats.SetupsDone.Store(done)
			return true
		}
		select {
		case <-stop:
			return false
		case <-c.failed:
			return false
		case <-time.After(100 * time.Millisecond):
		}
	}
}

// NetStats describes the network faults made.
func (c *Cluster) NetStats() string {
	if c.nemesis == nil {
		return "no network faults"
	}
	return c.nemesis.Stats.String()
}

// Stop kills every member, then removes their disks and links (not the network: the caller's).
func (c *Cluster) Stop() {
	c.crashMu.Lock()
	defer c.crashMu.Unlock()
	c.failOnce.Do(func() { close(c.failed) }) // no failure recorded after this: the harness's kills
	for _, mb := range c.members {
		if mb.p != nil {
			mb.p.Kill()
		}
	}
	for i, mb := range c.members {
		name := c.d.Members[i].Name + ".etcd"
		os.Remove(filepath.Join(etcdstart.DataBase, name))
		os.Remove(filepath.Join(etcdstart.WALBase, name))
		if mb.disk != nil {
			mb.disk.Destroy()
		}
	}
}
