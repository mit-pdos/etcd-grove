package robust

import (
	"fmt"
	"math/rand/v2"
	"os"
	"path/filepath"
	"strings"
	"sync"
	"sync/atomic"
	"time"
)

// Crash modes: what a crash does after the kill.
const (
	CrashKill  = "kill"  // SIGKILL, then syncfs of the machine's filesystem, then restart
	CrashPower = "power" // SIGKILL, then a power loss of the machine's disk, then restart
	CrashMixed = "mixed" // either, at random
)

// Config is a run's faults and limits.
type Config struct {
	Crash      string        // CrashKill, CrashPower or CrashMixed (the last two need disks)
	CrashPause time.Duration // between two crashes of a group, on average (0: none)
	Downtime   time.Duration // a crashed machine stays down a random time below it
	Netns      bool          // machines are network namespaces, with network faults
	NetPause   time.Duration // between two network faults, on average (0: none)
	NetHold    time.Duration // how long a network fault lasts, on average
	Deadline   time.Duration // the run fails if an orchestrator is not done by then
	// FaultsAtStart makes the faults from the start, through the orchestrators' set-ups;
	// otherwise they start once every orchestrator's set-up is done or the orchestrator ended, or
	// after SetupWait.
	FaultsAtStart bool
	SetupWait     time.Duration
}

// Command says how to start a run's processes: the program and the environment variables added.
type Command struct {
	Path string
	Env  []string
}

// Stats counts the faults made.
type Stats struct {
	Kills, PowerLosses, Restarts atomic.Uint64
	// SetupsDone is how many orchestrators had marked their set-up done when the faults started
	// (all, unless the wait ran out or one ended first); FaultsAfter is when they started, from
	// the orchestrators' start.
	SetupsDone  atomic.Int64
	FaultsAfter atomic.Int64
}

func (s *Stats) String() string {
	return fmt.Sprintf("kills %d, power losses %d; faults from %v, %d set-ups done then",
		s.Kills.Load(), s.PowerLosses.Load(), time.Duration(s.FaultsAfter.Load()).Round(100*time.Millisecond),
		s.SetupsDone.Load())
}

// A Restartable is a process on a machine that crashes: killed at any point, then its files
// synced or its disk's power lost (Config.Crash), then started again with the same program and
// arguments, on the same directory.
type Restartable struct {
	Name    string
	Machine *Machine
	// Dir is its files' directory: a directory of its own under the run's work directory, or its
	// disk's mount in the power modes.
	Dir string
	// Args are its arguments, set before its group starts (Group.Start).
	Args []string

	disk  *Disk
	p     *Proc
	count int
}

// A Run is a deployment's processes on the machines of a network, the faults made to them, and
// the run's first failure. Every process's output goes to logs/<name>.log under the work
// directory.
type Run struct {
	cfg  Config
	cmd  Command
	net  *Network
	work string

	Stats   Stats
	nemesis *NetNemesis

	mu     sync.Mutex
	groups []*Group

	failOnce sync.Once
	failed   chan struct{}
	failErr  error
}

// NewRun makes a run of processes started by cmd on the machines of n, with the faults and limits
// of cfg, its files in the directory work.
func NewRun(cfg Config, cmd Command, n *Network, work string) (*Run, error) {
	if err := os.MkdirAll(filepath.Join(work, "logs"), 0o755); err != nil {
		return nil, err
	}
	return &Run{cfg: cfg, cmd: cmd, net: n, work: work, failed: make(chan struct{})}, nil
}

// Work is the run's directory.
func (r *Run) Work() string { return r.work }

// LogPath is the log of the process named name.
func (r *Run) LogPath(name string) string { return filepath.Join(r.work, "logs", name+".log") }

// Fail records err as the run's failure, if it is the first.
func (r *Run) Fail(err error) {
	r.failOnce.Do(func() {
		r.failErr = err
		close(r.failed)
	})
}

// Err is the run's first failure, or nil.
func (r *Run) Err() error {
	select {
	case <-r.failed:
		return r.failErr
	default:
		return nil
	}
}

// Failed is closed once the run has failed (or stopped).
func (r *Run) Failed() <-chan struct{} { return r.failed }

// Tail is the last n lines of the file path.
func Tail(path string, n int) string {
	b, _ := os.ReadFile(path)
	lines := strings.Split(strings.TrimRight(string(b), "\n"), "\n")
	if len(lines) > n {
		lines = lines[len(lines)-n:]
	}
	return strings.Join(lines, "\n")
}

// startLogged starts the run's program on m with the arguments args, its output appended to the log of
// name (after the line header, if not empty). onExit (if not nil) is called if it ends without
// being killed, with Wait's error.
func (r *Run) startLogged(m *Machine, name string, args []string, header string, onExit func(error)) (*Proc, error) {
	lf, err := os.OpenFile(r.LogPath(name), os.O_CREATE|os.O_APPEND|os.O_WRONLY, 0o644)
	if err != nil {
		return nil, err
	}
	if header != "" {
		fmt.Fprintln(lf, header)
	}
	p, err := m.Start(r.cmd.Path, args, r.cmd.Env, lf, onExit)
	if err != nil {
		lf.Close()
		return nil, err
	}
	go func() {
		<-p.Exited()
		lf.Close()
	}()
	return p, nil
}

// A Group is restartables that the faults crash one at a time (a crasher of their own,
// Run.RunFaults).
type Group struct {
	r  *Run
	rs []*Restartable
	mu sync.Mutex
}

// NewGroup makes an empty group of the run's restartables.
func (r *Run) NewGroup() *Group {
	g := &Group{r: r}
	r.mu.Lock()
	r.groups = append(r.groups, g)
	r.mu.Unlock()
	return g
}

// Add makes a restartable process named name on m in g, not started: its directory (on a disk of
// its own, named name-disk, in the power modes). Its disk is removed by the run's Stop.
func (g *Group) Add(name string, m *Machine) (*Restartable, error) {
	r := g.r
	rs := &Restartable{Name: name, Machine: m, Dir: filepath.Join(r.work, name)}
	if r.cfg.Crash != CrashKill {
		dk, err := NewDisk(r.work, name+"-disk")
		if err != nil {
			return nil, err
		}
		rs.disk, rs.Dir = dk, dk.Mnt
	} else if err := os.MkdirAll(rs.Dir, 0o755); err != nil {
		return nil, err
	}
	g.mu.Lock()
	g.rs = append(g.rs, rs)
	g.mu.Unlock()
	return rs, nil
}

// Start starts g's restartables, each with its Args.
func (g *Group) Start() error {
	g.mu.Lock()
	defer g.mu.Unlock()
	for _, rs := range g.rs {
		if err := g.r.start(rs); err != nil {
			return err
		}
	}
	return nil
}

// start starts rs's next incarnation: a process that ends without being killed fails the run.
func (r *Run) start(rs *Restartable) error {
	r.mu.Lock()
	rs.count++
	count := rs.count
	r.mu.Unlock()
	logPath := r.LogPath(rs.Name)
	p, err := r.startLogged(rs.Machine, rs.Name, rs.Args, fmt.Sprintf("=== incarnation %d", count), func(err error) {
		r.Fail(fmt.Errorf("%s (incarnation %d) exited on its own (%v); its log %s:\n%s",
			rs.Name, count, err, logPath, Tail(logPath, 40)))
	})
	if err != nil {
		return err
	}
	r.mu.Lock()
	rs.p = p
	r.mu.Unlock()
	return nil
}

// crash crashes rs of g (SIGKILL, then its files synced or its disk's power lost) and restarts it
// after a random downtime.
func (r *Run) crash(g *Group, rs *Restartable) {
	g.mu.Lock()
	defer g.mu.Unlock()
	select {
	case <-r.failed: // stopped (or failed): Stop kills
		return
	default:
	}
	rs.p.Kill()
	power := r.cfg.Crash == CrashPower || (r.cfg.Crash == CrashMixed && rand.IntN(2) == 0)
	var err error
	if power {
		r.Stats.PowerLosses.Add(1)
		err = rs.disk.PowerLoss()
	} else {
		r.Stats.Kills.Add(1)
		err = SyncFS(rs.Dir)
	}
	if err != nil {
		r.Fail(fmt.Errorf("crash of %s: %v", rs.Name, err))
		return
	}
	time.Sleep(time.Duration(rand.Int64N(int64(r.cfg.Downtime) + 1)))
	if err := r.start(rs); err != nil {
		r.Fail(fmt.Errorf("restart of %s: %v", rs.Name, err))
		return
	}
	r.Stats.Restarts.Add(1)
}

// crasher crashes a random restartable of g at once, then at random times until stop (the first
// at once, so that a short workload, done within seconds of the faults' start, meets one).
func (r *Run) crasher(g *Group, stop <-chan struct{}) {
	if len(g.rs) == 0 {
		return
	}
	r.crash(g, g.rs[rand.IntN(len(g.rs))])
	for {
		select {
		case <-stop:
			return
		case <-r.failed:
			return
		case <-time.After(time.Duration(rand.Int64N(2*int64(r.cfg.CrashPause) + 1))):
		}
		r.crash(g, g.rs[rand.IntN(len(g.rs))])
	}
}

// RunFaults makes the run's faults until stop is closed: a crasher per group (Config's crashes,
// the first at once) and, if the configuration has network faults, a network nemesis over
// machines. It returns once they have stopped; NetStats then describes that nemesis.
func (r *Run) RunFaults(machines []*Machine, stop <-chan struct{}) {
	var wg sync.WaitGroup
	if r.cfg.CrashPause != 0 {
		r.mu.Lock()
		gs := append([]*Group(nil), r.groups...)
		r.mu.Unlock()
		for _, g := range gs {
			wg.Add(1)
			go func() { r.crasher(g, stop); wg.Done() }()
		}
	}
	if len(machines) != 0 && r.cfg.Netns && r.cfg.NetPause != 0 {
		nem := &NetNemesis{Net: r.net, Machines: machines, Pause: r.cfg.NetPause, Hold: r.cfg.NetHold}
		r.mu.Lock()
		r.nemesis = nem
		r.mu.Unlock()
		wg.Add(1)
		go func() {
			if err := nem.Run(stop); err != nil {
				r.Fail(fmt.Errorf("the network nemesis: %v", err))
			}
			wg.Done()
		}()
	}
	wg.Wait()
}

// NetStats describes the network faults made.
func (r *Run) NetStats() string {
	r.mu.Lock()
	defer r.mu.Unlock()
	if r.nemesis == nil {
		return "no network faults"
	}
	return r.nemesis.Stats.String()
}

// A Client is a process on a machine that never crashes: its name (its log's), its machine and
// its arguments; an orchestrator marks its set-up done by creating the file Ready.
type Client struct {
	Name    string
	Machine *Machine
	Args    []string
	Ready   string
}

// RunClients starts the processes nodes (which serve until killed: one that ends fails the run)
// and then the orchestrators orchs, and waits for every orchestrator to end, or for the deadline,
// or for the run to fail; then it kills them all and returns each orchestrator's last line of
// output (in orchs' order). Meanwhile it makes the faults (RunFaults, the network's over
// machines), from the start with Config.FaultsAtStart, otherwise once every orchestrator has
// marked its set-up done or ended, or SetupWait has passed. An orchestrator that ends with an
// error fails the run. The run's failure, if any, is Err.
func (r *Run) RunClients(nodes, orchs []Client, machines []*Machine) []string {
	return r.RunClientsAwait(nodes, orchs, machines, nil)
}

// RunClientsAwait is RunClients, calling await (unless nil) after starting the processes nodes
// and before starting the orchestrators: the harness's liveness wait (until the services the
// orchestrators use are up), so that the programs need not retry. An error from await fails the
// run.
func (r *Run) RunClientsAwait(nodes, orchs []Client, machines []*Machine, await func() error) []string {
	lines := make([]string, len(orchs))
	exited := make([]atomic.Bool, len(orchs))
	done := make(chan int, len(orchs))
	var nodeProcs, procs []*Proc
	stop := make(chan struct{})
	var wg sync.WaitGroup
	defer func() {
		for _, p := range procs {
			p.Kill()
		}
		for _, p := range nodeProcs {
			p.Kill()
		}
		close(stop)
		wg.Wait()
	}()
	for _, c := range nodes {
		logPath := r.LogPath(c.Name)
		p, err := r.startLogged(c.Machine, c.Name, c.Args, "", func(err error) {
			r.Fail(fmt.Errorf("%s exited (%v); its log:\n%s", c.Name, err, Tail(logPath, 30)))
		})
		if err != nil {
			r.Fail(err)
			return lines
		}
		nodeProcs = append(nodeProcs, p)
	}
	if await != nil {
		if err := await(); err != nil {
			r.Fail(err)
			return lines
		}
	}
	t0 := time.Now()
	for i, c := range orchs {
		logPath := r.LogPath(c.Name)
		p, err := r.startLogged(c.Machine, c.Name, c.Args, "", func(err error) {
			if err != nil {
				r.Fail(fmt.Errorf("%s failed (%v); its log:\n%s", c.Name, err, Tail(logPath, 30)))
			}
			lines[i] = strings.TrimSpace(Tail(logPath, 1))
			exited[i].Store(true)
			done <- i
		})
		if err != nil {
			r.Fail(err)
			return lines
		}
		procs = append(procs, p)
	}
	wg.Add(1)
	go func() {
		defer wg.Done()
		if !r.cfg.FaultsAtStart && !r.awaitSetUps(orchs, exited, stop) {
			return
		}
		r.Stats.FaultsAfter.Store(int64(time.Since(t0)))
		r.RunFaults(machines, stop)
	}()
	deadline := time.After(r.cfg.Deadline)
	for n := 0; n < len(procs) && r.Err() == nil; n++ {
		select {
		case <-done:
		case <-deadline:
			r.Fail(fmt.Errorf("the orchestrators were not done after %v", r.cfg.Deadline))
		case <-r.failed:
		}
	}
	return lines
}

// awaitSetUps waits until every orchestrator has marked its set-up done (its Ready file) or
// ended, or SetupWait has passed; it records how many set-ups were done, and reports false if the
// run stopped first.
func (r *Run) awaitSetUps(orchs []Client, exited []atomic.Bool, stop <-chan struct{}) bool {
	deadline := time.Now().Add(r.cfg.SetupWait)
	for {
		done, all := int64(0), true
		for i, c := range orchs {
			if _, err := os.Stat(c.Ready); err == nil {
				done++
			} else if !exited[i].Load() {
				all = false
			}
		}
		if all || time.Now().After(deadline) {
			r.Stats.SetupsDone.Store(done)
			return true
		}
		select {
		case <-stop:
			return false
		case <-r.failed:
			return false
		case <-time.After(100 * time.Millisecond):
		}
	}
}

// Stop kills every restartable, then removes their disks (not the network: the caller's). Every
// process is killed before any disk is removed: a process started by ip netns exec has a mount
// namespace of its own, which holds the disks mounted before it started. No failure is recorded
// after Stop: the kills are the run's.
func (r *Run) Stop() {
	r.failOnce.Do(func() { close(r.failed) })
	r.mu.Lock()
	gs := append([]*Group(nil), r.groups...)
	r.mu.Unlock()
	for _, g := range gs {
		g.mu.Lock()
	}
	for _, g := range gs {
		for _, rs := range g.rs {
			if rs.p != nil {
				rs.p.Kill()
			}
		}
	}
	for _, g := range gs {
		for _, rs := range g.rs {
			if rs.disk != nil {
				rs.disk.Destroy()
			}
		}
		g.mu.Unlock()
	}
}
