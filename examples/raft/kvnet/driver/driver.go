// Package driver runs kvnet's test: a cluster of replicas of kvnet's store, each in a process of
// its own, connected by TCP on the loopback interface; clients running random Puts, Gets and Reads
// over TCP while proposers reconfigure the cluster, leadership is disrupted, and replicas crash
// for real -- the process killed with SIGKILL, and either its filesystem synced before it
// restarts (the restart Linux file extension's semantics allows: notes/decisions.md, "One file
// semantics, fsExt; power loss only") or its machine's disk losing power (disk: every replica on a
// filesystem of its own, which loses what was not durable); then porcupine's check of the trace,
// a check that the members converge, and a power loss of the whole cluster at once, after which
// the store must still hold everything it held.
//
// The driver is the test's harness, not part of the program meant to be verified (that is kvnet's
// replica, against any client): it holds the clients' operation ids and read sequence numbers,
// and it never crashes.
package driver

import (
	"fmt"
	"net"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"sync"
	"sync/atomic"
	"syscall"
	"time"

	"github.com/anishathalye/porcupine"
	"github.com/goose-lang/primitive"
	"github.com/mit-pdos/etcd-grove/examples/lib/lintest"
	"github.com/mit-pdos/etcd-grove/examples/raft/kvnet"
	pb "go.etcd.io/raft/v3/raftpb"
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

// maxReplicas bounds the replicas a cluster starts (removed ones keep running), as kvdurable's.
const maxReplicas = 9

// opTimeout is how long a client waits for an answer at one replica before it tries another.
const opTimeout = 300 * time.Millisecond

// Crash modes.
const (
	CrashKill  = "kill"  // SIGKILL, then syncfs of the replica's filesystem, then restart
	CrashPower = "power" // SIGKILL, then a power loss of the replica's disk, then restart
	CrashMixed = "mixed" // either, at random
)

// Config is a test run's cluster, size, pace and faults.
type Config struct {
	kvnet.Options
	Clients      int
	Ops          int           // per client
	Proposers    int           // of configuration changes, running concurrently
	ReconfPause  time.Duration // between two proposals of a proposer, on average
	DisruptPause time.Duration // between two leadership disruptions, on average (0: none)
	CrashPause   time.Duration // between two crashes, on average (0: none)
	Downtime     time.Duration // a crashed replica stays down a random time below it
	Crash        string        // CrashKill, CrashPower or CrashMixed (the last two need root: disk)
	FinalCrash   bool          // the whole cluster crashes at once at the end (in the crash mode)
	Faults       kvnet.Faults  // the transport's, on top of the real network's
	Deadline     time.Duration // the run fails if the clients are not done by then (0: none)
}

// RandomConfig is a run of random options (kvnet.RandomOptions), 4 clients of 100 operations,
// one to three proposers, disruptions, crashes in the given mode, the transport's faults, and the
// final crash.
func RandomConfig(crash string) Config {
	return Config{
		Options:      kvnet.RandomOptions(),
		Clients:      4,
		Ops:          100,
		Proposers:    1 + int(below(3)),
		ReconfPause:  20 * time.Millisecond,
		DisruptPause: 50 * time.Millisecond,
		CrashPause:   150 * time.Millisecond,
		Downtime:     50 * time.Millisecond,
		Crash:        crash,
		FinalCrash:   true,
		Faults:       kvnet.Faults{Drop: 20, Delay: 8, Duplicate: 32, Cut: 64},
		Deadline:     5 * time.Minute,
	}
}

// Stats counts what the driver did; Node is the replicas' own counters, summed over the
// incarnations (each read just before its crash, and at the end).
type Stats struct {
	ReplicasStarted atomic.Uint64
	Kills           atomic.Uint64 // crashes with the filesystem synced
	PowerLosses     atomic.Uint64 // crashes with the disk's power lost
	Retries         atomic.Uint64
	ConfProposed    atomic.Uint64
	Disruptions     atomic.Uint64
	mu              sync.Mutex
	Node            [kvnet.NumStats]uint64
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
	return fmt.Sprintf("replicas started %d, kills %d, power losses %d, client retries %d, conf changes sent %d, disruptions %d\n  replicas: %s",
		s.ReplicasStarted.Load(), s.Kills.Load(), s.PowerLosses.Load(), s.Retries.Load(), s.ConfProposed.Load(),
		s.Disruptions.Load(), kvnet.FormatStats(s.Node))
}

// A Command says how to start a replica's process: the program, the arguments before the node's
// own (kvnet.NodeArgs), and the environment added to the driver's.
type Command struct {
	Path string
	Args []string
	Env  []string
}

// proc is one incarnation of a replica: its process, closed exited when it ends, and whether the
// driver killed it.
type proc struct {
	cmd     *exec.Cmd
	exited  chan struct{}
	killed  atomic.Bool
	logFile *os.File
}

// replica is a replica the cluster started: its id, its directory (a disk's mount, in the power
// modes), its disk (nil but in the power modes), its current incarnation and how many it had.
type replica struct {
	id    uint64
	dir   string
	disk  *disk
	p     *proc
	count int
}

// Cluster is a running cluster of replica processes.
type Cluster struct {
	cfg   Config
	cmd   Command
	work  string
	addrs map[uint64]string
	Stats Stats

	nextOp, nextRead atomic.Uint64

	mu       sync.Mutex
	replicas map[uint64]*replica
	nextID   uint64
	lastConf *pb.ConfState // the latest configuration a replica reported (randomMember)

	// crashMu makes one crash, or the final crash, at a time
	crashMu sync.Mutex

	failOnce sync.Once
	failed   chan struct{}
	failErr  error
}

// freeAddrs are n addresses of the loopback interface free now.
func freeAddrs(n int) (map[uint64]string, error) {
	addrs := make(map[uint64]string)
	var ls []net.Listener
	defer func() {
		for _, l := range ls {
			l.Close()
		}
	}()
	for id := uint64(1); id <= uint64(n); id++ {
		l, err := net.Listen("tcp", "127.0.0.1:0")
		if err != nil {
			return nil, err
		}
		ls = append(ls, l)
		addrs[id] = l.Addr().String()
	}
	return addrs, nil
}

// Start starts a cluster of cfg.Voters replicas (ids 1 to cfg.Voters), each a process started
// by cmd, with their files, logs and disks in the directory work (which must exist).
func Start(cfg Config, cmd Command, work string) (*Cluster, error) {
	addrs, err := freeAddrs(maxReplicas)
	if err != nil {
		return nil, err
	}
	if err := os.MkdirAll(filepath.Join(work, "logs"), 0o755); err != nil {
		return nil, err
	}
	c := &Cluster{cfg: cfg, cmd: cmd, work: work, addrs: addrs, replicas: make(map[uint64]*replica),
		nextID: cfg.Voters + 1, failed: make(chan struct{})}
	for id := uint64(1); id <= cfg.Voters; id++ {
		if _, err := c.add(id); err != nil {
			c.Stop()
			return nil, err
		}
	}
	return c, nil
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

// add makes replica id's directory (on a disk of its own in the power modes) and starts it.
func (c *Cluster) add(id uint64) (*replica, error) {
	r := &replica{id: id, dir: filepath.Join(c.work, "replica-"+fmt.Sprint(id))}
	if c.cfg.Crash != CrashKill {
		d, err := newDisk(c.work, fmt.Sprintf("kvnet-%d-%d", os.Getpid(), id))
		if err != nil {
			return nil, err
		}
		r.disk, r.dir = d, d.mnt
	} else if err := os.MkdirAll(r.dir, 0o755); err != nil {
		return nil, err
	}
	c.mu.Lock()
	c.replicas[id] = r
	c.mu.Unlock()
	c.Stats.ReplicasStarted.Add(1)
	return r, c.start(r)
}

// start starts r's next incarnation. A process that ends without the driver killing it (a panic:
// raft's, or the store's on a file it cannot read) fails the run.
func (c *Cluster) start(r *replica) error {
	r.count++
	logPath := filepath.Join(c.work, "logs", fmt.Sprintf("replica-%d.log", r.id))
	lf, err := os.OpenFile(logPath, os.O_CREATE|os.O_APPEND|os.O_WRONLY, 0o644)
	if err != nil {
		return err
	}
	fmt.Fprintf(lf, "=== incarnation %d\n", r.count)
	args := append(append([]string(nil), c.cmd.Args...), kvnet.NodeArgs(kvnet.NodeConfig{
		ID: r.id, Dir: r.dir, Addrs: c.addrs, Opts: c.cfg.Options, Faults: c.cfg.Faults})...)
	cmd := exec.Command(c.cmd.Path, args...)
	cmd.Env = append(os.Environ(), c.cmd.Env...)
	cmd.Stdout, cmd.Stderr = lf, lf
	cmd.SysProcAttr = &syscall.SysProcAttr{Pdeathsig: syscall.SIGKILL}
	if err := cmd.Start(); err != nil {
		lf.Close()
		return err
	}
	p := &proc{cmd: cmd, exited: make(chan struct{}), logFile: lf}
	go func() {
		err := cmd.Wait()
		lf.Close()
		if !p.killed.Load() {
			c.fail(fmt.Errorf("replica %d (incarnation %d) exited on its own (%v); its log %s:\n%s",
				r.id, r.count, err, logPath, tail(logPath, 40)))
		}
		close(p.exited)
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
	b, ok := kvnet.Request(c.addrs[id], kvnet.ReqStatus, timeout, nil)
	if !ok {
		return kvnet.Status{}, false
	}
	return kvnet.GetStatus(b)
}

// kill kills r's incarnation and waits for its process to end, after reading its counters (best
// effort: a replica that does not answer at once keeps them).
func (c *Cluster) kill(r *replica) {
	if s, ok := c.status(r.id, 20*time.Millisecond); ok {
		c.Stats.addNode(s.Stats)
	}
	r.p.killed.Store(true)
	r.p.cmd.Process.Kill()
	<-r.p.exited
}

// syncfs makes durable everything of dir's filesystem (syncfs(2), by sync -f): the restart the
// file semantics allows after a kill.
func syncfs(dir string) error {
	if out, err := exec.Command("sync", "-f", dir).CombinedOutput(); err != nil {
		return fmt.Errorf("sync -f %s: %v: %s", dir, err, out)
	}
	return nil
}

// down takes r down after its kill: a power loss of its disk, or a sync of its filesystem, by
// the crash mode.
func (c *Cluster) down(r *replica) error {
	power := c.cfg.Crash == CrashPower || (c.cfg.Crash == CrashMixed && oneIn(2))
	if power {
		c.Stats.PowerLosses.Add(1)
		return r.disk.powerLoss()
	}
	c.Stats.Kills.Add(1)
	return syncfs(r.dir)
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

// all is every replica started, in no particular order.
func (c *Cluster) all() []*replica {
	c.mu.Lock()
	defer c.mu.Unlock()
	var rs []*replica
	for _, r := range c.replicas {
		rs = append(rs, r)
	}
	return rs
}

// randomID is a random started replica's id.
func (c *Cluster) randomID() uint64 {
	rs := c.all()
	return rs[below(uint64(len(rs)))].id
}

// randomMember is a random member of the latest configuration a replica reported, or, one time in
// four or if there is none, a random replica.
func (c *Cluster) randomMember() uint64 {
	c.mu.Lock()
	cs := c.lastConf
	c.mu.Unlock()
	members := append(append([]uint64(nil), cs.GetVoters()...), cs.GetLearners()...)
	if len(members) == 0 || oneIn(4) {
		return c.randomID()
	}
	id := members[below(uint64(len(members)))]
	if c.replica(id) == nil {
		return c.randomID()
	}
	return id
}

// conf asks a random replica for its configuration, and records it (randomMember); nil if it
// does not answer.
func (c *Cluster) conf() *pb.ConfState {
	s, ok := c.status(c.randomID(), opTimeout)
	if !ok {
		return nil
	}
	c.mu.Lock()
	c.lastConf = s.Conf
	c.mu.Unlock()
	return s.Conf
}

// aborted says whether the run has failed.
func (c *Cluster) aborted() bool {
	return c.Err() != nil
}

// do runs one operation through the log: it gives it a fresh id and proposes it at a random
// member until one answers (the same encoding each time: it takes effect once). It returns ""
// if the run fails meanwhile.
func (c *Cluster) do(kind byte, key, val string) string {
	op := kvnet.EncodeOp(c.nextOp.Add(1), kind, key, val)
	for !c.aborted() {
		if v, ok := kvnet.Request(c.addrs[c.randomMember()], kvnet.ReqPropose, opTimeout, op); ok {
			return string(v)
		}
		c.Stats.Retries.Add(1)
	}
	return ""
}

// Put sets key's value to val.
func (c *Cluster) Put(key, val string) { c.do(kvnet.OpPut, key, val) }

// Get returns key's value ("" for a key never set), through the log.
func (c *Cluster) Get(key string) string { return c.do(kvnet.OpGet, key, "") }

// Read returns key's value by a read index at a random member, retried (each attempt a fresh
// read) until one answers.
func (c *Cluster) Read(key string) string {
	for !c.aborted() {
		req := kvnet.EncodeRead(c.nextRead.Add(1), key)
		if v, ok := kvnet.Request(c.addrs[c.randomMember()], kvnet.ReqRead, opTimeout, req); ok {
			return string(v)
		}
		c.Stats.Retries.Add(1)
	}
	return ""
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

// startNew starts a replica of a fresh id, in no configuration yet; ok is false if the cluster
// has started maxReplicas already.
func (c *Cluster) startNew() (uint64, bool) {
	c.mu.Lock()
	if c.nextID > maxReplicas {
		c.mu.Unlock()
		return 0, false
	}
	id := c.nextID
	c.nextID++
	c.mu.Unlock()
	if _, err := c.add(id); err != nil {
		c.fail(fmt.Errorf("start of replica %d: %v", id, err))
		return 0, false
	}
	return id, true
}

// changeID is the id a random change names, as kvdurable's randomID: one of the configuration's,
// another replica's, or, for a change that adds one, sometimes a fresh replica's, started now.
func (c *Cluster) changeID(cs *pb.ConfState, add bool) uint64 {
	if add && oneIn(4) {
		if id, ok := c.startNew(); ok {
			return id
		}
	}
	ids := append(append(append([]uint64(nil), cs.GetVoters()...), cs.GetVotersOutgoing()...), cs.GetLearners()...)
	if len(ids) == 0 || oneIn(4) {
		return c.randomID()
	}
	return ids[below(uint64(len(ids)))]
}

// randomChange is a random configuration change, as kvdurable's: the leaving of a joint
// configuration (one time in eight), or one to three single changes of random ids and a random
// transition, as a ConfChangeV2, or, for one change of the automatic transition, one time in two
// as a ConfChange.
func (c *Cluster) randomChange(cs *pb.ConfState) pb.ConfChangeI {
	if oneIn(8) {
		return &pb.ConfChangeV2{}
	}
	count := 1
	if oneIn(2) {
		count = 1 + int(below(3))
	}
	var changes []*pb.ConfChangeSingle
	for i := 0; i < count; i++ {
		var t pb.ConfChangeType
		switch below(16) {
		case 0, 1, 2, 3, 4:
			t = pb.ConfChangeAddNode
		case 5, 6, 7, 8:
			t = pb.ConfChangeAddLearnerNode
		case 9, 10, 11, 12, 13, 14:
			t = pb.ConfChangeRemoveNode
		default:
			t = pb.ConfChangeUpdateNode
		}
		id := c.changeID(cs, t != pb.ConfChangeRemoveNode)
		changes = append(changes, &pb.ConfChangeSingle{Type: t.Enum(), NodeId: new(id)})
	}
	transition := []pb.ConfChangeTransition{pb.ConfChangeTransitionAuto,
		pb.ConfChangeTransitionJointImplicit, pb.ConfChangeTransitionJointExplicit}[below(3)]
	if count == 1 && transition == pb.ConfChangeTransitionAuto && oneIn(2) {
		return &pb.ConfChange{Type: changes[0].Type, NodeId: changes[0].NodeId}
	}
	return &pb.ConfChangeV2{Transition: transition.Enum(), Changes: changes}
}

// Reconfigure proposes random configuration changes through random replicas, at random times,
// until stop, never waiting for one to be committed (as kvdurable's).
func (c *Cluster) Reconfigure(pause time.Duration, stop <-chan struct{}) {
	for !c.sleep(pause, stop) {
		cc := c.randomChange(c.conf())
		c.Stats.ConfProposed.Add(1)
		kvnet.Request(c.addrs[c.randomID()], kvnet.ReqConf, opTimeout, kvnet.PutConfChange(nil, cc))
	}
}

// Disrupt moves leadership at random times until stop: a transfer to a random replica, a
// campaign, or a leader forgotten, asked of a random replica.
func (c *Cluster) Disrupt(pause time.Duration, stop <-chan struct{}) {
	for !c.sleep(pause, stop) {
		c.Stats.Disruptions.Add(1)
		kvnet.Request(c.addrs[c.randomID()], kvnet.ReqDisrupt, opTimeout, kvnet.EncodeDisrupt(below(3), c.randomID()))
	}
}

// Crash crashes a random replica at random times until stop, and restarts it: a member or not,
// a leader or not, at any point of its work.
func (c *Cluster) Crash(pause time.Duration, stop <-chan struct{}) {
	for !c.sleep(pause, stop) {
		c.crash(c.randomID())
	}
}

// agree is Converged's check, once: the members of the configuration of the replica that has
// applied the most agree with it on the applied index, the configuration and the store contents.
// It returns that replica's status.
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
	for _, id := range members {
		s, ok := got[id]
		if !ok {
			return top, fmt.Errorf("member %d does not answer", id)
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
		st, ok := c.status(r.id, opTimeout)
		if !ok {
			s += fmt.Sprintf("%d: no answer (incarnation %d)\n", r.id, r.count)
			continue
		}
		s += fmt.Sprintf("%d: role %d term %d lead %d commit %d applied %d cfg %v (incarnation %d)\n",
			r.id, st.Role, st.Term, st.Lead, st.Commit, st.Index, st.Conf, r.count)
	}
	return s
}

// Stop kills every replica, reading their counters first, and removes the disks.
func (c *Cluster) Stop() {
	c.crashMu.Lock()
	defer c.crashMu.Unlock()
	for _, r := range c.all() {
		if r.p != nil {
			c.kill(r)
		}
		if r.disk != nil {
			r.disk.destroy()
		}
	}
}

// Result is a run's outcome: porcupine's answer on the clients' trace, and the first failure
// (a replica that died on its own, the members not converging, the store losing data in the
// final crash, or the clients not done by the deadline), nil if none.
type Result struct {
	Check porcupine.CheckResult
	Err   error
}

// Run starts a cluster (Start) and runs cfg.Clients clients of cfg.Ops operations of kvnet's
// traffic (kvnet.Gen) on it, traced with the given clock, while proposers reconfigure it,
// leadership is disrupted, and replicas crash and restart; once the clients are done, it stops
// those, checks the trace with porcupine, and waits for the members to converge; then, if
// cfg.FinalCrash, it crashes the whole cluster at once, restarts it, waits for it to converge
// again and checks that the store holds exactly what it held, and that a Read of each key through
// the cluster returns it. It returns the result and the cluster, still running (the caller stops
// it, Cluster.Stop, after Dump if it failed).
func Run(cfg Config, cmd Command, work string, clock lintest.Clock) (Result, *Cluster) {
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
	for i := 0; i < cfg.Proposers; i++ {
		spawn(func() { c.Reconfigure(cfg.ReconfPause, stop) })
	}
	if cfg.DisruptPause != 0 {
		spawn(func() { c.Disrupt(cfg.DisruptPause, stop) })
	}
	if cfg.CrashPause != 0 {
		spawn(func() { c.Crash(cfg.CrashPause, stop) })
	}
	if cfg.Deadline != 0 {
		done := make(chan struct{})
		defer close(done)
		go func() {
			select {
			case <-time.After(cfg.Deadline):
				c.fail(fmt.Errorf("the clients were not done after %v:\n%s", cfg.Deadline, c.Dump()))
			case <-done:
			}
		}()
	}
	apply := func(input any) any {
		in := input.(kvnet.Input)
		switch in.Kind {
		case kvnet.OpPut:
			c.Put(in.Key, in.Val)
			return ""
		case kvnet.OpGet:
			return c.Get(in.Key)
		}
		return c.Read(in.Key)
	}
	check := lintest.Run(kvnet.Model(), apply, kvnet.Gen, clock, cfg.Clients, cfg.Ops, 0)
	close(stop)
	wg.Wait()
	res := Result{Check: check}
	if err := c.Err(); err != nil {
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
	after, err := c.Converged(30 * time.Second)
	if err != nil {
		return fmt.Errorf("after the final crash, the members did not converge: %v", err)
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
