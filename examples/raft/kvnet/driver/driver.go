// Package driver runs kvnet's test over the robustness harness (examples/lib/robust), the way the
// top-level robustness theorem (notes/kvnet-robust-goal.md) runs it: every replica a process of
// kvnet.RunNode on a machine of its own (a network namespace, as root; one loopback address
// otherwise), all started at once, connected by TCP through the harness's network; and the
// checking client, a process of kvcheck.Check on a client machine, which runs the clients' random
// Puts, Gets and Reads, reconfigures the cluster and disrupts leadership, and panics unless
// porcupine accepts its history. Meanwhile the harness makes the environment's faults: the network
// fails (partitions both ways or one way, by drops or by resets; delay, loss, duplication,
// reordering of packets: robust.NetNemesis, in the namespace mode) and replicas crash for real --
// the process killed with SIGKILL, and either its filesystem synced before it restarts (the
// restart Linux file extension's semantics allows: notes/decisions.md, "One file semantics, fsExt;
// power loss only") or its machine's disk losing power (robust.Disk: every replica on a filesystem
// of its own, which loses what was not durable). Every fault is the environment's: the programs
// have none.
//
// The harness's own checks, after the client is done, are beyond the theorem (liveness, and the
// final crash): the members converge, and after a power loss of the whole cluster at once the
// store still holds everything it held.
package driver

import (
	"fmt"
	"math/rand"
	"net"
	"os"
	"path/filepath"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"
	"time"

	"github.com/anishathalye/porcupine"
	"github.com/goose-lang/primitive"
	"github.com/mit-pdos/etcd-grove/examples/lib/robust"
	"github.com/mit-pdos/etcd-grove/examples/raft/kvnet"
	"google.golang.org/protobuf/proto"
)

// oneIn is true with probability 1/n.
func oneIn(n uint64) bool { return primitive.RandomUint64()%n == 0 }

// below is a random number in [0, n) (0 if n is 0).
func below(n uint64) uint64 {
	if n == 0 {
		return 0
	}
	return primitive.RandomUint64() % n
}

// NumReplicas is how many replicas a cluster runs (all started at once; the checking client's
// configuration changes add and remove them), as kvdurable's.
const NumReplicas = 9

// opTimeout is how long the harness waits for a replica's answer.
const opTimeout = 300 * time.Millisecond

// replicaPort is the port a replica listens at on its machine (namespace mode): outside Linux's
// ephemeral range, as the net extension's addresses must be (kvnet.AddrOk).
const replicaPort = "7001"

// clientMachines is how many client machines the network has (namespace mode): the checking
// client runs on the first; the others take part in the network faults only.
const clientMachines = 4

// Crash modes.
const (
	CrashKill  = "kill"  // SIGKILL, then syncfs of the replica's filesystem, then restart
	CrashPower = "power" // SIGKILL, then a power loss of the replica's disk, then restart
	CrashMixed = "mixed" // either, at random
)

// Config is a test run's cluster and faults. The workload is the checking client's own
// (kvcheck).
type Config struct {
	kvnet.Options
	CrashPause time.Duration // between two crashes, on average (0: none)
	Downtime   time.Duration // a crashed replica stays down a random time below it
	Crash      string        // CrashKill, CrashPower or CrashMixed (the last two need root: disk)
	FinalCrash bool          // the whole cluster crashes at once at the end (in the crash mode)
	Netns      bool          // machines are network namespaces (needs root), with network faults
	NetPause   time.Duration // between two network faults, on average (0: none; needs Netns)
	NetHold    time.Duration // how long a network fault lasts, on average
	Deadline   time.Duration // the run fails if the client is not done by then (0: none)
	Transport  string        // the replicas' raft messages': TransportTCP (or "") or TransportUDP
}

// RandomConfig is a run of random options (kvnet.RandomOptions), crashes in the given mode,
// network faults if netns, and the final crash.
func RandomConfig(crash string, netns bool) Config {
	return Config{
		Options:    kvnet.RandomOptions(),
		CrashPause: 150 * time.Millisecond,
		Downtime:   50 * time.Millisecond,
		Crash:      crash,
		FinalCrash: true,
		Netns:      netns,
		NetPause:   100 * time.Millisecond,
		NetHold:    200 * time.Millisecond,
		Deadline:   5 * time.Minute,
	}
}

// Stats counts what the harness did; Node is the replicas' own counters, summed over the
// incarnations (each read just before its crash, and at the end).
type Stats struct {
	Kills       atomic.Uint64 // crashes with the filesystem synced
	PowerLosses atomic.Uint64 // crashes with the disk's power lost
	// StrandedLearners is how many learners the last convergence check let lag (Cluster.stranded)
	StrandedLearners atomic.Uint64
	mu               sync.Mutex
	Node             [kvnet.NumStats]uint64
}

func (s *Stats) addNode(v [kvnet.NumStats]uint64) {
	s.mu.Lock()
	for i := range v {
		s.Node[i] += v[i]
	}
	s.mu.Unlock()
}

func (s *Stats) String() string {
	s.mu.Lock()
	defer s.mu.Unlock()
	return fmt.Sprintf("kills %d, power losses %d, stranded learners %d\n  replicas: %s",
		s.Kills.Load(), s.PowerLosses.Load(), s.StrandedLearners.Load(), kvnet.FormatStats(s.Node))
}

// A Command says how to start the harness's processes: the program, the arguments before the
// process's own (NodeArgs, ClientArgs: its role first), and the environment added to the
// harness's. The program runs RunProcess on its arguments.
type Command struct {
	Path string
	Args []string
	Env  []string
}

// replica is a replica of the cluster: its id, its machine, its directory (a disk's mount, in the
// power modes), its disk (nil but in the power modes), its current incarnation's process and how
// many it had.
type replica struct {
	id    uint64
	m     *robust.Machine
	dir   string
	disk  *robust.Disk
	p     *robust.Proc
	count int
}

// clusters counts the clusters this process started (each round of a check is one).
var clusters atomic.Uint64

// Cluster is a running cluster of replica processes.
type Cluster struct {
	cfg    Config
	cmd    Command
	work   string
	serial uint64 // this process's count of clusters, in its disks' names
	addrs  string // the replicas' addresses, comma-separated (replica i at the i-th)
	Stats  Stats

	net      *robust.Network
	machines map[uint64]*robust.Machine // the replicas', by id
	clients  []*robust.Machine          // the checking client runs on the first
	control  *robust.Machine            // the harness's own status and read requests
	nemesis  *robust.NetNemesis         // nil without network faults

	// the harness's reads' sequence numbers: from 2^63, so as never to meet the client's
	nextRead atomic.Uint64

	mu       sync.Mutex
	replicas map[uint64]*replica

	// crashMu makes one crash, or the final crash, at a time
	crashMu sync.Mutex

	failOnce sync.Once
	failed   chan struct{}
	failErr  error
}

// freeAddrs are n addresses free now, all on the loopback address ip, 127.a.b.c other than
// 127.0.0.1, at random ports below Linux's ephemeral range (kvnet.AddrOk). Not on 127.0.0.1: a
// connection's source address is 127.0.0.1 (the loopback route's), so no connection's source port
// can take a replica's address while the replica is down, and its next incarnation always gets to
// listen there. (Another process could still listen on the same address and port: the replica
// then retries until it can.)
func freeAddrs(ip string, n int) ([]string, error) {
	var addrs []string
	var ls []net.Listener
	defer func() {
		for _, l := range ls {
			l.Close()
		}
	}()
	for tries := 0; len(addrs) < n; tries++ {
		if tries > 1000 {
			return nil, fmt.Errorf("no free port on %s", ip)
		}
		a := ip + ":" + strconv.Itoa(20000+rand.Intn(32768-20000))
		l, err := net.Listen("tcp", a)
		if err != nil {
			continue
		}
		ls = append(ls, l)
		addrs = append(addrs, a)
	}
	return addrs, nil
}

// Start starts a cluster of NumReplicas replicas (ids 1 to NumReplicas, the bootstrap
// configuration's voters 1 to cfg.Voters), each a process started by cmd on a machine of its own,
// with their files, logs and disks in the directory work (which must exist).
func Start(cfg Config, cmd Command, work string) (*Cluster, error) {
	if err := os.MkdirAll(filepath.Join(work, "logs"), 0o755); err != nil {
		return nil, err
	}
	c := &Cluster{cfg: cfg, cmd: cmd, work: work, machines: make(map[uint64]*robust.Machine),
		replicas: make(map[uint64]*replica), failed: make(chan struct{}), serial: clusters.Add(1)}
	c.nextRead.Store(1 << 63)
	if err := c.makeNetwork(); err != nil {
		if c.net != nil {
			c.net.Close()
		}
		return nil, err
	}
	for id := uint64(1); id <= NumReplicas; id++ {
		if err := c.add(id); err != nil {
			c.Stop()
			return nil, err
		}
	}
	return c, nil
}

// makeNetwork makes the machines: one per replica, the clients' and the control's; and the
// replicas' addresses (a port of their machine's address in the namespace mode, free ports of one
// loopback address otherwise).
func (c *Cluster) makeNetwork() error {
	if !c.cfg.Netns {
		c.net = robust.LocalNetwork()
	} else {
		n, err := robust.NewNetwork(fmt.Sprintf("kvn%d", os.Getpid()%100000))
		if err != nil {
			return err
		}
		c.net = n
	}
	for id := uint64(1); id <= NumReplicas; id++ {
		m, err := c.net.AddMachine(fmt.Sprintf("replica-%d", id))
		if err != nil {
			return err
		}
		c.machines[id] = m
	}
	var addrs []string
	if c.cfg.Netns {
		for id := uint64(1); id <= NumReplicas; id++ {
			addrs = append(addrs, c.machines[id].IP+":"+replicaPort)
		}
	} else {
		as, err := freeAddrs(c.machines[1].IP, NumReplicas)
		if err != nil {
			return err
		}
		addrs = as
	}
	for _, a := range addrs {
		if !kvnet.AddrOk(a) {
			return fmt.Errorf("address %q is not well formed (kvnet.AddrOk)", a)
		}
	}
	c.addrs = kvnet.JoinAddrs(addrs)
	nclients := 1
	if c.cfg.Netns {
		nclients = clientMachines
	}
	for i := 0; i < nclients; i++ {
		m, err := c.net.AddMachine(fmt.Sprintf("client-%d", i))
		if err != nil {
			return err
		}
		c.clients = append(c.clients, m)
	}
	m, err := c.net.AddMachine("control")
	if err != nil {
		return err
	}
	c.control = m
	if c.cfg.Netns && c.cfg.NetPause != 0 {
		var ms []*robust.Machine
		for id := uint64(1); id <= NumReplicas; id++ {
			ms = append(ms, c.machines[id])
		}
		c.nemesis = &robust.NetNemesis{Net: c.net, Machines: append(ms, c.clients...),
			Pause: c.cfg.NetPause, Hold: c.cfg.NetHold}
	}
	return nil
}

// request sends one request from the control machine to replica id (kvnet.RequestVia).
func (c *Cluster) request(id uint64, kind byte, timeout, total time.Duration, payload []byte) ([]byte, bool) {
	return kvnet.RequestVia(c.control.Dial, kvnet.SplitAddrs(c.addrs)[id-1], kind, timeout, total, payload)
}

// fail records the run's first failure and wakes everything that waits on the cluster.
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

// aborted says whether the run has failed.
func (c *Cluster) aborted() bool {
	return c.Err() != nil
}

// add makes replica id's directory (on a disk of its own in the power modes) and starts it.
func (c *Cluster) add(id uint64) error {
	r := &replica{id: id, m: c.machines[id], dir: filepath.Join(c.work, "replica-"+fmt.Sprint(id))}
	if c.cfg.Crash != CrashKill {
		d, err := robust.NewDisk(c.work, fmt.Sprintf("kvnet-%d-%d-%d", os.Getpid(), c.serial, id))
		if err != nil {
			return err
		}
		r.disk, r.dir = d, d.Mnt
	} else if err := os.MkdirAll(r.dir, 0o755); err != nil {
		return err
	}
	// started before it is listed, so that a crash (which picks among the listed replicas) never
	// meets one without a process
	if err := c.start(r); err != nil {
		if r.disk != nil {
			r.disk.Destroy()
		}
		return err
	}
	c.mu.Lock()
	c.replicas[id] = r
	c.mu.Unlock()
	return nil
}

// start starts r's next incarnation. A process that ends without the harness killing it (a panic:
// raft's, or the store's on a file it cannot read) fails the run.
func (c *Cluster) start(r *replica) error {
	c.mu.Lock()
	r.count++
	count := r.count
	c.mu.Unlock()
	logPath := filepath.Join(c.work, "logs", fmt.Sprintf("replica-%d.log", r.id))
	lf, err := os.OpenFile(logPath, os.O_CREATE|os.O_APPEND|os.O_WRONLY, 0o644)
	if err != nil {
		return err
	}
	fmt.Fprintf(lf, "=== incarnation %d\n", count)
	args := append(append([]string(nil), c.cmd.Args...), NodeArgs(r.id, c.addrs, r.dir, c.cfg.Options)...)
	if c.cfg.Transport != "" {
		args = append(args, "-transport", c.cfg.Transport)
	}
	p, err := r.m.Start(c.cmd.Path, args, c.cmd.Env, lf, func(err error) {
		c.fail(fmt.Errorf("replica %d (incarnation %d) exited on its own (%v); its log %s:\n%s",
			r.id, count, err, logPath, tail(logPath, 40)))
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
	r.p = p
	c.mu.Unlock()
	return nil
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

// status asks replica id for its status.
func (c *Cluster) status(id uint64, timeout time.Duration) (kvnet.Status, bool) {
	b, ok := c.request(id, kvnet.ReqStatus, timeout, timeout+500*time.Millisecond, nil)
	if !ok {
		return kvnet.Status{}, false
	}
	return kvnet.GetStatus(b)
}

// kill kills r's incarnation and waits for its process to end, after reading its counters (best
// effort: a replica that does not answer at once keeps them).
func (c *Cluster) kill(r *replica) {
	if b, ok := c.request(r.id, kvnet.ReqStatus, 20*time.Millisecond, 20*time.Millisecond, nil); ok {
		if s, ok := kvnet.GetStatus(b); ok {
			c.Stats.addNode(s.Stats)
		}
	}
	r.p.Kill()
}

// down takes r down after its kill: a power loss of its disk, or a sync of its filesystem, by
// the crash mode.
func (c *Cluster) down(r *replica) error {
	power := c.cfg.Crash == CrashPower || (c.cfg.Crash == CrashMixed && oneIn(2))
	if power {
		c.Stats.PowerLosses.Add(1)
		return r.disk.PowerLoss()
	}
	c.Stats.Kills.Add(1)
	return robust.SyncFS(r.dir)
}

// crash crashes replica id (kill, down) and restarts it after a random downtime.
func (c *Cluster) crash(id uint64) {
	c.crashMu.Lock()
	defer c.crashMu.Unlock()
	r := c.replica(id)
	c.kill(r)
	if err := c.down(r); err != nil {
		c.fail(fmt.Errorf("crash of replica %d: %v", id, err))
		return
	}
	time.Sleep(time.Duration(below(uint64(c.cfg.Downtime) + 1)))
	if err := c.start(r); err != nil {
		c.fail(fmt.Errorf("restart of replica %d: %v", id, err))
	}
}

// CrashAll crashes every replica at once (each killed, then each taken down), then restarts them
// all.
func (c *Cluster) CrashAll() error {
	c.crashMu.Lock()
	defer c.crashMu.Unlock()
	rs := c.all()
	for _, r := range rs {
		c.kill(r)
	}
	for _, r := range rs {
		if err := c.down(r); err != nil {
			return err
		}
	}
	for _, r := range rs {
		if err := c.start(r); err != nil {
			return err
		}
	}
	return nil
}

// replica is replica id, or nil.
func (c *Cluster) replica(id uint64) *replica {
	c.mu.Lock()
	defer c.mu.Unlock()
	return c.replicas[id]
}

// all is every replica, in no particular order.
func (c *Cluster) all() []*replica {
	c.mu.Lock()
	defer c.mu.Unlock()
	var rs []*replica
	for _, r := range c.replicas {
		rs = append(rs, r)
	}
	return rs
}

// sleep waits a random time below 2*pause, or until stop or a failure; it says whether to stop.
func (c *Cluster) sleep(pause time.Duration, stop <-chan struct{}) bool {
	select {
	case <-stop:
		return true
	case <-c.failed:
		return true
	case <-time.After(time.Duration(below(uint64(2 * pause)))):
		return false
	}
}

// Crash crashes a random replica at random times until stop, and restarts it: a member or not,
// a leader or not, at any point of its work.
func (c *Cluster) Crash(pause time.Duration, stop <-chan struct{}) {
	for !c.sleep(pause, stop) {
		c.crash(1 + below(NumReplicas))
	}
}

// Read returns key's value by a read index at a random replica, retried until one answers or the
// run fails (the harness's own read, for its final check: not the client's).
func (c *Cluster) Read(key string) string {
	for !c.aborted() {
		req := kvnet.EncodeRead(c.nextRead.Add(1), key)
		if v, ok := c.request(1+below(NumReplicas), kvnet.ReqRead, opTimeout, opTimeout+500*time.Millisecond, req); ok {
			return string(v)
		}
	}
	return ""
}

// stranded says whether s, the status of a learner of the configuration of top (the replica that
// has applied the most), may be stuck for good behind top: with PreVote and CheckQuorum both off, a
// learner that took a higher term (from a removed voter still campaigning in its old
// configuration) ignores the leader's messages without answering, and never campaigns itself
// (nonissues/raft-learner-stranded-higher-term.md). Raft's liveness, not the store's safety.
func (c *Cluster) stranded(top, s kvnet.Status, id uint64) bool {
	return !c.cfg.PreVote && !c.cfg.CheckQuorum && s.Term > top.Term && hasID(top.Conf.GetLearners(), id)
}

// hasID says whether id is in ids.
func hasID(ids []uint64, id uint64) bool {
	for _, x := range ids {
		if x == id {
			return true
		}
	}
	return false
}

// agree is Converged's check, once: the members of the configuration of the replica that has
// applied the most agree with it on the applied index, the configuration and the store contents,
// but for a learner stuck behind it in the way raft allows (stranded), which it counts in
// Stats.StrandedLearners. It returns that replica's status.
func (c *Cluster) agree() (kvnet.Status, error) {
	var top kvnet.Status
	var topID uint64
	got := make(map[uint64]kvnet.Status)
	for _, r := range c.all() {
		s, ok := c.status(r.id, opTimeout)
		if !ok {
			continue
		}
		got[r.id] = s
		if topID == 0 || s.Index > top.Index {
			top, topID = s, r.id
		}
	}
	if topID == 0 {
		return top, fmt.Errorf("no replica answers")
	}
	cs := top.Conf
	members := append(append(append([]uint64(nil), cs.GetVoters()...), cs.GetVotersOutgoing()...), cs.GetLearners()...)
	stranded := uint64(0)
	for _, id := range members {
		s, ok := got[id]
		if !ok {
			return top, fmt.Errorf("member %d does not answer", id)
		}
		if s.Index != top.Index && c.stranded(top, s, id) {
			stranded++
			continue
		}
		if s.Index != top.Index {
			return top, fmt.Errorf("replica %d applied %d, member %d applied %d", topID, top.Index, id, s.Index)
		}
		if !proto.Equal(cs, s.Conf) {
			return top, fmt.Errorf("replica %d's configuration %v, member %d's %v", topID, cs, id, s.Conf)
		}
		if !sameContents(top.Contents, s.Contents) {
			return top, fmt.Errorf("replicas %d and %d differ at index %d: %v, %v", topID, id, s.Index, top.Contents, s.Contents)
		}
	}
	c.Stats.StrandedLearners.Store(stranded)
	return top, nil
}

// sameContents says whether two stores hold the same values (a key's absence is the value "").
func sameContents(a, b map[string]string) bool {
	for k, v := range a {
		if b[k] != v {
			return false
		}
	}
	for k, v := range b {
		if a[k] != v {
			return false
		}
	}
	return true
}

// Converged waits up to timeout for the members to agree (agree), and returns the agreed status.
func (c *Cluster) Converged(timeout time.Duration) (kvnet.Status, error) {
	deadline := time.Now().Add(timeout)
	for {
		s, err := c.agree()
		if err == nil || time.Now().After(deadline) || c.aborted() {
			if err == nil {
				err = c.Err()
			}
			return s, err
		}
		time.Sleep(20 * time.Millisecond)
	}
}

// Dump describes every replica's state, for a run that fails.
func (c *Cluster) Dump() string {
	s := ""
	for _, r := range c.all() {
		c.mu.Lock()
		count := r.count
		c.mu.Unlock()
		st, ok := c.status(r.id, opTimeout)
		if !ok {
			s += fmt.Sprintf("%d: no answer (incarnation %d)\n", r.id, count)
			continue
		}
		s += fmt.Sprintf("%d: role %d term %d lead %d commit %d applied %d cfg %v (incarnation %d)\n",
			r.id, st.Role, st.Term, st.Lead, st.Commit, st.Index, st.Conf, count)
	}
	return s
}

// Stop kills every replica, reading their counters first, then removes the disks and the
// network. Every replica is killed before any disk is removed: a replica's process (in its
// machine's network namespace, by ip netns exec) has a mount namespace of its own, which holds the
// disks mounted before it started, so a disk stays busy until every replica is gone.
func (c *Cluster) Stop() {
	c.crashMu.Lock()
	defer c.crashMu.Unlock()
	rs := c.all()
	for _, r := range rs {
		if r.p != nil {
			c.kill(r)
		}
	}
	for _, r := range rs {
		if r.disk != nil {
			r.disk.Destroy()
		}
	}
	c.net.Close()
}

// NetStats describes the network faults made, if any.
func (c *Cluster) NetStats() string {
	if c.nemesis == nil {
		return "no network faults"
	}
	return c.nemesis.Stats.String()
}

// Result is a run's outcome: porcupine's answer on the client's history (Ok if the client
// returned, Illegal if it panicked on porcupine's answer), and the first failure (a replica that
// died on its own, the client failing otherwise or not done by the deadline, the members not
// converging, the store losing data in the final crash), nil if none.
type Result struct {
	Check porcupine.CheckResult
	Err   error
}

// runClient runs the checking client (kvcheck.Check) on the first client machine and waits for it
// to end, or for the deadline, or for the run to fail. It returns porcupine's answer as the
// client's end gives it.
func (c *Cluster) runClient() porcupine.CheckResult {
	logPath := filepath.Join(c.work, "logs", "client.log")
	lf, err := os.Create(logPath)
	if err != nil {
		c.fail(err)
		return porcupine.Unknown
	}
	defer lf.Close()
	done := make(chan error, 1)
	args := append(append([]string(nil), c.cmd.Args...), ClientArgs(c.addrs, c.cfg.Voters)...)
	p, err := c.clients[0].Start(c.cmd.Path, args, c.cmd.Env, lf, func(err error) { done <- err })
	if err != nil {
		c.fail(err)
		return porcupine.Unknown
	}
	var deadline <-chan time.Time
	if c.cfg.Deadline != 0 {
		deadline = time.After(c.cfg.Deadline)
	}
	select {
	case err := <-done:
		if err == nil {
			return porcupine.Ok
		}
		log := tail(logPath, 40)
		if strings.Contains(log, "porcupine rejected") {
			return porcupine.Illegal
		}
		c.fail(fmt.Errorf("the checking client failed (%v); its log:\n%s", err, log))
	case <-deadline:
		p.Kill()
		c.fail(fmt.Errorf("the checking client was not done after %v:\n%s", c.cfg.Deadline, c.Dump()))
	case <-c.failed:
		p.Kill()
	}
	return porcupine.Unknown
}

// Run starts a cluster (Start) and runs the checking client on it (runClient) while replicas
// crash and restart and, in the namespace mode, the network fails; once the client is done, it
// stops those and waits for the members to converge; then, if cfg.FinalCrash, it crashes the
// whole cluster at once, restarts it, waits for it to converge again and checks that the store
// holds exactly what it held, and that a Read of each key through the cluster returns it. It
// returns the result and the cluster, still running (the caller stops it, Cluster.Stop, after
// Dump if it failed).
func Run(cfg Config, cmd Command, work string) (Result, *Cluster) {
	c, err := Start(cfg, cmd, work)
	if err != nil {
		return Result{Check: porcupine.Unknown, Err: err}, nil
	}
	stop := make(chan struct{})
	var wg sync.WaitGroup
	spawn := func(f func()) {
		wg.Add(1)
		go func() {
			f()
			wg.Done()
		}()
	}
	if cfg.CrashPause != 0 {
		spawn(func() { c.Crash(cfg.CrashPause, stop) })
	}
	if c.nemesis != nil {
		spawn(func() {
			if err := c.nemesis.Run(stop); err != nil {
				c.fail(fmt.Errorf("the network nemesis: %v", err))
			}
		})
	}
	check := c.runClient()
	close(stop)
	wg.Wait()
	res := Result{Check: check}
	if err := c.Err(); err != nil || check != porcupine.Ok {
		res.Err = err
		return res, c
	}
	before, err := c.Converged(30 * time.Second)
	if err != nil {
		res.Err = fmt.Errorf("the members did not converge: %v", err)
		return res, c
	}
	if cfg.FinalCrash {
		res.Err = c.finalCrash(before)
	}
	return res, c
}

// finalCrash crashes the whole cluster at once and checks that it comes back holding what it held
// (before: the agreed status before the crash).
func (c *Cluster) finalCrash(before kvnet.Status) error {
	if err := c.CrashAll(); err != nil {
		return fmt.Errorf("the final crash: %v", err)
	}
	// The members may agree at once on less than they had applied: the commit index is not always
	// written (a Ready that changes only it is written one time in two), so a restarted replica
	// applies up to the last one written, and the rest only once a new leader commits an entry of
	// its own term. Wait for the agreement to reach the index applied before.
	deadline := time.Now().Add(30 * time.Second)
	var after kvnet.Status
	for {
		s, err := c.Converged(time.Until(deadline))
		if err != nil {
			return fmt.Errorf("after the final crash, the members did not converge: %v", err)
		}
		after = s
		if after.Index >= before.Index || time.Now().After(deadline) {
			break
		}
		time.Sleep(20 * time.Millisecond)
	}
	if !sameContents(before.Contents, after.Contents) || after.Index < before.Index {
		return fmt.Errorf("the final crash lost data: before, applied %d: %v; after, applied %d: %v",
			before.Index, before.Contents, after.Index, after.Contents)
	}
	for _, key := range []string{"a", "b", "c"} {
		v := c.Read(key)
		if err := c.Err(); err != nil {
			return err
		}
		if v != before.Contents[key] {
			return fmt.Errorf("after the final crash, a Read of %q returned %q, the store held %q", key, v, before.Contents[key])
		}
	}
	return nil
}
