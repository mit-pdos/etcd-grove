package check

// Config is the binding's constants (B 40-42, R 75-78; antithesis-fm/spec/EtcdBinding*.cfg): the
// servers, the voters every node starts with, and Bootstrapped. Values = {"v"} and Nil = "" are
// fixed (Values is not used by the binding; Nil is the empty name).
type Config struct {
	Server       Set
	InitVoters   Set
	Bootstrapped bool
}

// Pre is the record an announced write keeps to be taken back (B 349-359, `pre`): what the node
// had on disk before it, the facts it made, and the bookkeeping of batched writes.
type Pre struct {
	Term      int
	VoteTerm  int
	VoteFor   string
	Commit    int
	Keep      int
	Suffix    []Entry
	Confirmed Confirmed
	Msgs      []Fact
	Votes     []VoteRec
	Acks      []Fact
	Low       int
	Made      bool
}

// QItem is a queued report `[ev |-> ev, m |-> ...]` (B 441, 452): the `mem` report and the
// message the node was handling then (<<>> or <<msg>>).
type QItem struct {
	Ev *Event
	M  []Msg
}

// ReadRec is a read index asked for, `[ctx |-> ..., floor |-> ...]` (B 658).
type ReadRec struct {
	Ctx   string
	Floor int
}

// State is a state of the binding (B 44-54 with R 89-116): every variable but commits, applied
// and read (package comment). Per-server variables are slices indexed like Cfg.Server. A State
// is never written once built.
type State struct {
	Cfg *Config

	// EtcdRaft's variables.
	CurrentTerm []int
	VoteTerm    []int
	VoteFor     []string
	Log         [][]Entry
	CommitIndex []int
	Role        []string
	LastApplied []int
	Config      []Conf
	ConfAt      []int
	Confirmed   []Confirmed
	Msgs        []Fact
	Votes       []VoteRec
	Leaders     []LeaderRec
	LedLog      TermLogs
	LedConf     TermConfs
	LedAt       TermInts
	ElAt        TermInts

	// EtcdBinding's variables.
	I       int
	Undo    []*Pre // nil: NoWrite (<<>>); p: LastWrite(p) (<<p>>)
	Pending [][]Msg
	Queue   [][]QItem
	Reads   [][]ReadRec
	Chain   []Entry
	TermLen TermInts
	Viol    Set
}

// The role names (R 85-87).
const (
	Follower  = "follower"
	Candidate = "candidate"
	Leader    = "leader"
)

// idx is the position of server n in Cfg.Server: applying a function on Server to a name outside
// it is an EvalError.
func (s *State) idx(n string) int {
	for k, x := range s.Cfg.Server {
		if x == n {
			return k
		}
	}
	evalError("a function on Server applied to a name that is not a server")
	return 0
}

func (s *State) clone() *State {
	c := *s
	return &c
}

func setInt(a []int, k int, v int) []int {
	out := make([]int, len(a))
	copy(out, a)
	out[k] = v
	return out
}

func setStr(a []string, k int, v string) []string {
	out := make([]string, len(a))
	copy(out, a)
	out[k] = v
	return out
}

func setLog(a [][]Entry, k int, v []Entry) [][]Entry {
	out := make([][]Entry, len(a))
	copy(out, a)
	out[k] = v
	return out
}

func setConf(a []Conf, k int, v Conf) []Conf {
	out := make([]Conf, len(a))
	copy(out, a)
	out[k] = v
	return out
}

func setConfirmed(a []Confirmed, k int, v Confirmed) []Confirmed {
	out := make([]Confirmed, len(a))
	copy(out, a)
	out[k] = v
	return out
}

func setPre(a []*Pre, k int, v *Pre) []*Pre {
	out := make([]*Pre, len(a))
	copy(out, a)
	out[k] = v
	return out
}

func setMsgs(a [][]Msg, k int, v []Msg) [][]Msg {
	out := make([][]Msg, len(a))
	copy(out, a)
	out[k] = v
	return out
}

func setQueue(a [][]QItem, k int, v []QItem) [][]QItem {
	out := make([][]QItem, len(a))
	copy(out, a)
	out[k] = v
	return out
}

func setReads(a [][]ReadRec, k int, v []ReadRec) [][]ReadRec {
	out := make([][]ReadRec, len(a))
	copy(out, a)
	out[k] = v
	return out
}

// violAdd is `viol \cup {name}`.
func violAdd(v Set, name string) Set { return SetAdd(v, name) }

// Init0 is B 755-764: BootInit (B 733-753) when Bootstrapped, else the model's Init (R 181-201).
func Init0(cfg *Config) *State {
	n := len(cfg.Server)
	s := &State{Cfg: cfg, I: 1}
	s.CurrentTerm = make([]int, n)
	s.VoteTerm = make([]int, n)
	s.VoteFor = make([]string, n)
	s.Log = make([][]Entry, n)
	s.CommitIndex = make([]int, n)
	s.Role = make([]string, n)
	s.LastApplied = make([]int, n)
	s.Config = make([]Conf, n)
	s.ConfAt = make([]int, n)
	s.Confirmed = make([]Confirmed, n)
	s.Undo = make([]*Pre, n)
	s.Pending = make([][]Msg, n)
	s.Queue = make([][]QItem, n)
	s.Reads = make([][]ReadRec, n)
	initConf := Conf{In: cfg.InitVoters, Out: nil}
	for k := 0; k < n; k++ {
		s.Role[k] = Follower
		s.Config[k] = initConf
	}
	if cfg.Bootstrapped {
		// First == CHOOSE s \in InitVoters : TRUE (B 731): TLC chooses the least element.
		first := cfg.InitVoters[0]
		boot := []Entry{{Term: 1, Type: "config", Value: Value{Str: ""}}}
		for k := 0; k < n; k++ {
			s.CurrentTerm[k] = 1
			s.VoteTerm[k] = 1
			s.VoteFor[k] = first
			s.Log[k] = boot
			s.Confirmed[k] = Confirmed{Term: 1, Index: 1}
		}
		s.Leaders = []LeaderRec{{Server: first, Term: 1}}
		s.LedLog = TermLogs{{T: 1, L: boot}}
		s.LedConf = TermConfs{{T: 1, C: initConf}}
		s.LedAt = TermInts{{T: 1, V: 0}}
		s.ElAt = TermInts{{T: 1, V: 0}}
	}
	return s
}
