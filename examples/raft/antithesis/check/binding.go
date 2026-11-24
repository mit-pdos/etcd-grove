package check

// The operators and actions of EtcdBinding.tla (B). An action returns its successor and true, or
// (nil, false) where the TLA+ action is false.

// ---------------------------------------------------------------------------------------------
// Facts from reported messages (B 61-100).

// VoteFact is B 63-65.
func VoteFact(m Msg) Fact {
	return Fact{Type: "vote", Src: m.from(), Term: m.term(), LastLogIndex: m.index(), LastLogTerm: m.logTerm()}
}

// ToAppendFact is B 68-71 `AppendFact(m)`.
func ToAppendFact(m Msg) AppendFact {
	return AppendFact{Src: m.from(), Dst: m.to(), Term: m.term(), PrevLogIndex: m.index(), PrevLogTerm: m.logTerm(),
		Entries: m.entries(), Commit: m.commit()}
}

// AckFact is B 73.
func AckFact(src, dst string, t, k int) Fact {
	return Fact{Type: "ack", Src: src, Dst: dst, Term: t, Index: k}
}

// IsReq is B 75 `IsReq(m) == m.type \in {"app", "hb", "snap"}`.
func IsReq(m Msg) bool { return m.typ() == "app" || m.typ() == "hb" || m.typ() == "snap" }

// SnapOk is B 80-83.
func SnapOk(ll TermLogs, m Msg) bool {
	if m.typ() != "snap" {
		return true
	}
	return ll.Has(m.term()) && m.index() <= len(ll.Get(m.term())) && TermAt(ll.Get(m.term()), m.index()) == m.logTerm()
}

// ReqFactIn is B 85-91.
func ReqFactIn(ll TermLogs, m Msg) AppendFact {
	if m.typ() == "snap" {
		var es []Entry
		if ll.Has(m.term()) {
			es = SubSeq(ll.Get(m.term()), 1, m.index())
		}
		return AppendFact{Src: m.from(), Dst: m.to(), Term: m.term(), PrevLogIndex: 0, PrevLogTerm: 0, Entries: es,
			Commit: m.index()}
	}
	return ToAppendFact(m)
}

// BootTerm is B 96.
func (s *State) BootTerm() int {
	if s.Cfg.Bootstrapped {
		return 1
	}
	return 0
}

// VoteOf is B 99.
func (s *State) VoteOf(vt int, vf string, t int) string {
	if vt == t && t > s.BootTerm() {
		return vf
	}
	return ""
}

// Vote is B 100.
func (s *State) Vote(n int) string { return s.VoteOf(s.VoteTerm[n], s.VoteFor[n], s.CurrentTerm[n]) }

// ---------------------------------------------------------------------------------------------
// Committed prefixes (B 102-143).

// RecordedIn is B 109-112.
func RecordedIn(ch []Entry, tl TermInts, l []Entry, c int, t int) bool {
	if !(c <= len(l) && c <= len(ch)) {
		return false
	}
	found := false
	for _, p := range tl {
		if p.T <= t && p.V >= c {
			found = true
			break
		}
	}
	if !found {
		return false
	}
	return EntriesEqual(SubSeq(ch, 1, c), SubSeq(l, 1, c))
}

// SendableIn is B 117-126.
func SendableIn(ld []LeaderRec, ll TermLogs, ch []Entry, tl TermInts, f AppendFact) bool {
	if !leadersHas(ld, LeaderRec{Server: f.Src, Term: f.Term}) {
		return false
	}
	if !ll.Has(f.Term) {
		return false
	}
	l := ll.Get(f.Term)
	p := f.PrevLogIndex
	k := len(f.Entries)
	if !(p+k <= len(l)) {
		return false
	}
	if f.PrevLogTerm != TermAt(l, p) {
		return false
	}
	if !EntriesEqual(f.Entries, SubSeq(l, p+1, p+k)) {
		return false
	}
	return f.Commit == 0 || RecordedIn(ch, tl, l, f.Commit, f.Term)
}

// Sendable is B 128.
func (s *State) Sendable(f AppendFact) bool {
	return SendableIn(s.Leaders, s.LedLog, s.Chain, s.TermLen, f)
}

// Comparable is B 130.
func Comparable(a, b []Entry) bool { return IsPrefix(a, b) || IsPrefix(b, a) }

// Matching is B 132-134.
func Matching(a, b []Entry) bool {
	for k := 1; k <= Min(len(a), len(b)); k++ {
		if a[k-1].Term == b[k-1].Term {
			if !a[k-1].Equal(b[k-1]) {
				return false
			}
			if k > 1 && a[k-2].Term != b[k-2].Term {
				return false
			}
		}
	}
	return true
}

// MemCommit is B 139.
func (s *State) MemCommit(n int) int {
	q := s.Queue[n]
	if len(q) == 0 {
		return s.CommitIndex[n]
	}
	return q[len(q)-1].Ev.commit()
}

// SameConf is B 142-143.
func SameConf(ev *Event, c Conf) bool {
	if !ev.has(FVoters) {
		return true
	}
	return SetOf(ev.voters()).Equal(c.In) && SetOf(ev.outgoing()).Equal(c.Out)
}

// ---------------------------------------------------------------------------------------------
// Announced writes (B 146-194).

// EffTerm is B 152.
func (s *State) EffTerm(j int) int {
	if s.Undo[j] == nil {
		return s.CurrentTerm[j]
	}
	return Min(s.CurrentTerm[j], s.Undo[j].Term)
}

// Over is B 153.
func (s *State) Over(t int) bool {
	for j := range s.Cfg.Server {
		if !(s.EffTerm(j) > t) {
			return false
		}
	}
	return true
}

// Recovered is B 155-157.
func Recovered(ev *Event, t int, v string, c int, l []Entry) bool {
	return ev.term() == t && ev.vote() == v && ev.commit() == c && ev.lastIndex() == len(l) &&
		ev.lastTerm() == TermAt(l, len(l))
}

// Boot is B 162-194.
func (s *State) Boot(n int, ev *Event) (*State, bool) {
	ns := s.clone()
	ns.Undo = setPre(s.Undo, n, nil)
	ns.Pending = setMsgs(s.Pending, n, nil)
	ns.Queue = setQueue(s.Queue, n, nil)
	ns.Reads = setReads(s.Reads, n, nil)
	ns.Role = setStr(s.Role, n, Follower)
	if !Recovered(ev, s.CurrentTerm[n], s.Vote(n), s.CommitIndex[n], s.Log[n]) {
		if s.Undo[n] == nil {
			return nil, false
		}
		u := s.Undo[n]
		if u.Made {
			return nil, false
		}
		l := Concat(SubSeq(s.Log[n], 1, u.Keep), u.Suffix)
		if !Recovered(ev, u.Term, s.VoteOf(u.VoteTerm, u.VoteFor, u.Term), u.Commit, l) {
			return nil, false
		}
		ns.CurrentTerm = setInt(s.CurrentTerm, n, u.Term)
		ns.VoteTerm = setInt(s.VoteTerm, n, u.VoteTerm)
		ns.VoteFor = setStr(s.VoteFor, n, u.VoteFor)
		ns.CommitIndex = setInt(s.CommitIndex, n, u.Commit)
		ns.Log = setLog(s.Log, n, l)
		ns.Confirmed = setConfirmed(s.Confirmed, n, u.Confirmed)
		ns.Msgs = factsMinus(s.Msgs, u.Msgs)
		ns.Votes = votesMinus(s.Votes, u.Votes)
	}
	a := 0
	if ev.has(FApplied) {
		a = ev.applied()
	}
	logn := ns.Log[n]
	if !(a == 0 || (a <= len(logn) && a <= len(s.Chain) && EntriesEqual(SubSeq(s.Chain, 1, a), SubSeq(logn, 1, a)))) {
		return nil, false
	}
	ns.LastApplied = setInt(s.LastApplied, n, a)
	c := ConfOf(logn, a, s.InitConf())
	ns.Config = setConf(s.Config, n, c)
	ns.ConfAt = setInt(s.ConfAt, n, LastConf(logn, a))
	if !SameConf(ev, c) {
		return nil, false
	}
	return ns, true
}

// ---------------------------------------------------------------------------------------------

// Recv is B 199-204.
func (s *State) Recv(n int, ev *Event) (*State, bool) {
	m := ev.msg()
	if m.to() != s.Cfg.Server[n] {
		return nil, false
	}
	ns := s.clone()
	ns.Pending = setMsgs(s.Pending, n, []Msg{m})
	if IsReq(m) && m.term() >= s.CurrentTerm[n] {
		if !(SnapOk(s.LedLog, m) && s.Sendable(ReqFactIn(s.LedLog, m))) {
			return nil, false
		}
	}
	return ns, true
}

// ---------------------------------------------------------------------------------------------

// MemResult is the record InMemory returns (B 231-275).
type MemResult struct {
	Ok      bool
	Role    []string
	Leaders []LeaderRec
	LedLog  TermLogs
	LedConf TermConfs
	Config  []Conf
	ConfAt  []int
	LedAt   TermInts
	ElAt    TermInts
	Chain   []Entry
	TermLen TermInts
	Viol    Set
}

// inMem holds InMemory's LET definitions (B 214-230), each a method evaluated where the TLA+
// uses it.
type inMem struct {
	s  *State
	n  int
	ev *Event
}

func (x inMem) T() int { return x.ev.term() }

func (x inMem) role1() string {
	if x.ev.role() == "precandidate" {
		return Follower
	}
	return x.ev.role()
}

func (x inMem) leads() bool { return x.ev.role() == Leader }

func (x inMem) wins() bool { return x.leads() && x.s.Role[x.n] != Leader }

func (x inMem) es() []Entry {
	if x.ev.has(FEntries) {
		return x.ev.entries()
	}
	return nil
}

func (x inMem) ld1() []LeaderRec {
	if x.wins() {
		return leadersAdd(x.s.Leaders, LeaderRec{Server: x.s.Cfg.Server[x.n], Term: x.T()})
	}
	return x.s.Leaders
}

func (x inMem) ll1() TermLogs {
	if x.wins() {
		return x.s.LedLog.With(x.T(), x.s.Log[x.n])
	}
	return x.s.LedLog
}

func (x inMem) lc1() TermConfs {
	if x.wins() {
		return x.s.LedConf.With(x.T(), x.s.Config[x.n])
	}
	return x.s.LedConf
}

func (x inMem) snapsM() bool { return x.ev.has(FSnap) }

func (x inMem) known() int {
	if x.s.TermLen.Has(x.T()) {
		return x.s.TermLen.Get(x.T())
	}
	return 0
}

func (x inMem) app() bool { return x.leads() && len(x.es()) != 0 }

func (x inMem) ll2() TermLogs {
	if x.app() && x.ll1().Has(x.T()) {
		ll1 := x.ll1()
		return ll1.With(x.T(), Concat(ll1.Get(x.T()), x.es()))
	}
	return x.ll1()
}

func (x inMem) L() []Entry {
	if x.ll2().Has(x.T()) {
		return x.ll2().Get(x.T())
	}
	return nil
}

func (x inMem) c() int { return x.ev.commit() }

func (x inMem) cmt() bool { return x.leads() && x.c() > x.known() && TermAt(x.L(), x.c()) == x.T() }

func (x inMem) newC() []Entry { return SubSeq(x.L(), 1, x.c()) }

func validBy(by string) bool {
	return by == "recv" || by == "tick" || by == "campaign" || by == "propose" || by == "write" ||
		by == "apply" || by == "boot" || by == "transfer" || by == "snapstatus" || by == "read"
}

// ok is the field `ok` of B 231-253.
func (x inMem) ok() bool {
	s, n, ev := x.s, x.n, x.ev
	if !validBy(ev.by()) {
		return false
	}
	r := ev.role()
	if !(r == Follower || r == Candidate || r == Leader || r == "precandidate") {
		return false
	}
	if x.snapsM() {
		if !(ev.role() != Leader && s.Role[n] != Leader && ev.snap().Index <= len(s.Chain)) {
			return false
		}
	}
	if x.wins() {
		if !(s.Role[n] == Candidate && s.CurrentTerm[n] == x.T()) {
			return false
		}
		if s.LedLog.Has(x.T()) {
			return false
		}
		if !IsQuorum(s.Granted(n), s.Config[n]) {
			return false
		}
		if !s.OneWaiting(n, s.Log[n]) {
			return false
		}
		if !(s.ConfAt[n] == 0 || RecordedIn(s.Chain, s.TermLen, s.Log[n], s.ConfAt[n], x.T()-1)) {
			return false
		}
	}
	if x.leads() {
		if !(s.CurrentTerm[n] == x.T() && x.ll1().Has(x.T()) && x.c() <= len(x.L())) {
			return false
		}
	}
	if x.app() {
		if ev.has(FFirst) {
			if ev.first() != len(x.ll1().Get(x.T()))+1 {
				return false
			}
		}
		es := x.es()
		for q := 1; q <= len(es); q++ {
			if es[q-1].Term != x.T() {
				return false
			}
		}
		for q := 1; q <= len(es); q++ {
			if IsConf(es[q-1]) {
				if !s.AllSwitched(n, x.ll1().Get(x.T())) {
					return false
				}
				for r := 1; r <= q-1; r++ {
					if IsConf(es[r-1]) {
						return false
					}
				}
				if !Legal(s.Config[n], es[q-1].Value) {
					return false
				}
			}
		}
	}
	if x.leads() && x.c() > 0 {
		if x.cmt() {
			return IsQuorum(s.Acked(n, x.T(), x.c()), x.lc1().Get(x.T()))
		}
		return RecordedIn(s.Chain, s.TermLen, x.L(), x.c(), x.T())
	}
	return true
}

// InMemory is B 213-275. TLC builds the record whole (every field evaluated, in order), so an
// evaluation error in any field is one even where `ok` is false; so here.
func (s *State) InMemory(n int, ev *Event) MemResult {
	x := inMem{s: s, n: n, ev: ev}
	var r MemResult
	r.Ok = x.ok()
	r.Role = setStr(s.Role, n, x.role1())
	r.Leaders = x.ld1()
	r.LedLog = x.ll2()
	r.LedConf = x.lc1()
	if x.snapsM() {
		r.Config = setConf(s.Config, n, ConfOf(s.Chain, ev.snap().Index, s.InitConf()))
		r.ConfAt = setInt(s.ConfAt, n, LastConf(s.Chain, ev.snap().Index))
	} else {
		r.Config = s.Config
		r.ConfAt = s.ConfAt
	}
	if x.wins() {
		r.LedAt = s.LedAt.With(x.T(), s.ConfAt[n])
		r.ElAt = s.ElAt.With(x.T(), s.ConfAt[n])
	} else {
		r.LedAt = s.LedAt
		r.ElAt = s.ElAt
	}
	if x.cmt() && x.c() > len(s.Chain) {
		r.Chain = x.newC()
	} else {
		r.Chain = s.Chain
	}
	if x.cmt() {
		r.TermLen = s.TermLen.With(x.T(), x.c())
	} else {
		r.TermLen = s.TermLen
	}
	viol := s.Viol
	if x.cmt() && !Comparable(s.Chain, x.newC()) {
		viol = violAdd(viol, "CommitSafety")
	}
	lc := false
	if x.cmt() {
		for _, p := range x.ll2() {
			if p.T > x.T() && !IsPrefix(x.newC(), p.L) {
				lc = true
				break
			}
		}
	}
	if !lc && x.wins() {
		for _, p := range s.TermLen {
			if p.T < x.T() && !IsPrefix(SubSeq(s.Chain, 1, p.V), s.Log[n]) {
				lc = true
				break
			}
		}
	}
	if lc {
		viol = violAdd(viol, "LeaderCompleteness")
	}
	if ev.role() == Candidate && s.Role[n] != Candidate &&
		!(s.Config[n].In.Has(s.Cfg.Server[n]) || s.Config[n].Out.Has(s.Cfg.Server[n])) {
		viol = violAdd(viol, "Unpromotable")
	}
	r.Viol = viol
	return r
}

// ---------------------------------------------------------------------------------------------

// Lowest is B 288.
func Lowest(a, b int) int {
	if a == 0 {
		return b
	}
	if b == 0 {
		return a
	}
	return Min(a, b)
}

// onDisk holds OnDisk's arguments and its LET definitions (B 291-359), each a method evaluated
// where the TLA+ uses it.
type onDisk struct {
	s    *State
	n    int
	q    QItem
	more bool
	ro   []string
	ld   []LeaderRec
	ll   TermLogs
	ch   []Entry
	tl   TermInts
	vi   Set
}

func (x onDisk) w() *Event  { return x.q.Ev }
func (x onDisk) hasM() bool { return len(x.q.M) != 0 }
func (x onDisk) m() Msg     { return msgSeqHead(x.q.M) }
func (x onDisk) T0() int    { return x.s.CurrentTerm[x.n] }
func (x onDisk) T1() int    { return x.w().term() }

func (x onDisk) elect() bool { return x.T1() != x.T0() && x.w().role() == Candidate }
func (x onDisk) adopt() bool { return x.T1() != x.T0() && !x.elect() }

func (x onDisk) V1() string {
	if x.T1() != x.T0() {
		return ""
	}
	return x.s.Vote(x.n)
}

func (x onDisk) voted() bool    { return x.w().vote() != x.V1() }
func (x onDisk) L0() []Entry    { return x.s.Log[x.n] }
func (x onDisk) leads() bool    { return x.w().role() == Leader }
func (x onDisk) moved() bool    { return x.w().commit() != x.s.CommitIndex[x.n] }
func (x onDisk) fm() AppendFact { return ReqFactIn(x.ll, x.m()) }
func (x onDisk) snaps() bool    { return x.w().has(FSnap) }
func (x onDisk) bat() bool      { return !x.w().has(FEntries) }

func (x onDisk) isApp() bool {
	return x.bat() && x.hasM() && x.m().typ() == "app" && x.m().term() == x.T1()
}

func (x onDisk) below() bool { return x.isApp() && x.fm().PrevLogIndex < x.s.CommitIndex[x.n] }

func (x onDisk) takes() bool { return x.isApp() && !x.below() && x.s.PrevOk(x.n, x.fm()) }

// K is B 314-316: the least x in Diff, or Len(fm.entries) + 1 when Diff is empty.
func (x onDisk) K() int {
	fm := x.fm()
	l0 := x.L0()
	for k := 1; k <= len(fm.Entries); k++ {
		y := fm.PrevLogIndex + k
		if y > len(l0) || At(l0, y).Term != fm.Entries[k-1].Term {
			return k
		}
	}
	return len(fm.Entries) + 1
}

func (x onDisk) es() []Entry {
	if x.snaps() || x.takes() {
		fm := x.fm()
		return SubSeq(fm.Entries, x.K(), len(fm.Entries))
	}
	if x.bat() {
		return nil
	}
	return x.w().entries()
}

func (x onDisk) first() int {
	if x.snaps() || x.takes() {
		return x.fm().PrevLogIndex + x.K()
	}
	if x.w().has(FFirst) {
		return x.w().first()
	}
	return len(x.L0()) + 1
}

func (x onDisk) stores() bool { return len(x.es()) != 0 }

func (x onDisk) f() AppendFact {
	if x.leads() {
		t1 := x.T1()
		f := AppendFact{Src: x.s.Cfg.Server[x.n], Dst: x.s.Cfg.Server[x.n], Term: t1, Entries: x.es()}
		if x.stores() {
			f.PrevLogIndex = x.first() - 1
		}
		if x.stores() && x.ll.Has(t1) {
			f.PrevLogTerm = TermAt(x.ll.Get(t1), x.first()-1)
		}
		if x.moved() {
			f.Commit = x.w().commit()
		}
		return f
	}
	return x.fm()
}

func (x onDisk) k() int { return x.first() - x.f().PrevLogIndex }

func (x onDisk) L1() []Entry {
	if x.stores() {
		return Concat(SubSeq(x.L0(), 1, x.first()-1), x.es())
	}
	return x.L0()
}

func (x onDisk) last() int { f := x.f(); return f.PrevLogIndex + len(f.Entries) }

func (x onDisk) acks() bool {
	if x.stores() && x.leads() {
		return true
	}
	if x.moved() && !x.leads() && x.hasM() && (x.m().typ() == "app" || x.m().typ() == "snap") {
		return true
	}
	return x.takes() || x.below()
}

func (x onDisk) ackAt() int {
	if x.below() {
		return x.s.CommitIndex[x.n]
	}
	return x.last()
}

func (x onDisk) conf1() Confirmed {
	if x.stores() {
		return Confirmed{Term: x.T1(), Index: x.last()}
	}
	if x.acks() && !x.below() {
		c := x.s.Confirmed[x.n]
		if c.Term == x.T1() {
			return Confirmed{Term: x.T1(), Index: Max(c.Index, x.last())}
		}
		return Confirmed{Term: x.T1(), Index: x.last()}
	}
	return x.s.Confirmed[x.n]
}

func (x onDisk) adv() bool     { return x.w().commit() > x.s.CommitIndex[x.n] }
func (x onDisk) newC() []Entry { return SubSeq(x.L1(), 1, x.w().commit()) }

func (x onDisk) ch1() []Entry {
	if x.adv() && len(x.newC()) > len(x.ch) {
		return x.newC()
	}
	return x.ch
}

func (x onDisk) old() int {
	if x.tl.Has(x.T1()) {
		return x.tl.Get(x.T1())
	}
	return 0
}

// OnDisk is B 290-436. It returns the successor's variables that OnDisk gives (currentTerm,
// voteTerm, voteFor, log, commitIndex, role, confirmed, msgs, votes, leaders, ledLog, undo, chain,
// termLen, viol); the caller gives the others.
func (s *State) OnDisk(n int, q QItem, more bool, ro []string, ld []LeaderRec, ll TermLogs, ch []Entry,
	tl TermInts, vi Set) (*State, bool) {
	x := onDisk{s: s, n: n, q: q, more: more, ro: ro, ld: ld, ll: ll, ch: ch, tl: tl, vi: vi}
	w := x.w()
	me := s.Cfg.Server[n]
	if more && s.Undo[n] == nil {
		return nil, false
	}
	if x.isApp() && !SendableIn(ld, ll, ch, tl, x.fm()) {
		return nil, false
	}
	// The term.
	if !(x.T1() >= x.T0()) {
		return nil, false
	}
	if x.T1() != x.T0() && ro[n] == Leader {
		return nil, false
	}
	if x.elect() && !(x.T1() == x.T0()+1 && w.vote() == me) {
		return nil, false
	}
	if x.adopt() {
		if !(x.hasM() && x.m().term() == x.T1()) {
			return nil, false
		}
		found := false
		for j := range s.Cfg.Server {
			if j != n && s.CurrentTerm[j] >= x.T1() {
				found = true
				break
			}
		}
		if !found {
			return nil, false
		}
	}
	// The vote.
	if x.voted() {
		if x.V1() != "" {
			return nil, false
		}
		if !x.elect() {
			if !(x.hasM() && x.m().typ() == "vote" && x.m().from() == w.vote() && x.m().term() == x.T1() &&
				factsHas(s.Msgs, VoteFact(x.m())) && s.UpToDate(VoteFact(x.m()), n)) {
				return nil, false
			}
		}
	}
	// The entries.
	if x.snaps() {
		if !(!x.leads() && x.hasM() && x.m().typ() == "snap" && x.stores() && w.snap().Index == x.m().index() &&
			w.snap().Term == x.m().logTerm() && w.commit() == x.m().index()) {
			return nil, false
		}
	}
	if x.stores() {
		if x.leads() {
			if !(x.T1() == x.T0() && x.first() == len(x.L0())+1 && SendableIn(ld, ll, ch, tl, x.f())) {
				return nil, false
			}
		} else {
			if !(x.hasM() && (x.m().typ() == "app" || x.m().typ() == "snap") && x.m().term() == x.T1()) {
				return nil, false
			}
			if x.m().typ() == "snap" && !x.snaps() {
				return nil, false
			}
			if !(SnapOk(ll, x.m()) && SendableIn(ld, ll, ch, tl, x.f())) {
				return nil, false
			}
			if !s.PrevOk(n, x.f()) {
				return nil, false
			}
			k := x.k()
			if !(1 <= k && k <= len(x.f().Entries)) {
				return nil, false
			}
			if !s.HasFirst(n, x.f(), k-1) {
				return nil, false
			}
			if !EntriesEqual(x.es(), SubSeq(x.f().Entries, k, len(x.f().Entries))) {
				return nil, false
			}
			if x.first() <= len(x.L0()) {
				if At(x.L0(), x.first()).Term == At(x.es(), 1).Term {
					return nil, false
				}
			} else if x.first() != len(x.L0())+1 {
				return nil, false
			}
		}
	}
	// The commit index.
	if x.moved() {
		if !(w.commit() > s.CommitIndex[n] && w.commit() <= len(x.L1())) {
			return nil, false
		}
		if x.leads() {
			if !(x.T1() == x.T0() && SendableIn(ld, ll, ch, tl, x.f())) {
				return nil, false
			}
		} else {
			if !(x.hasM() && IsReq(x.m()) && x.m().term() == x.T1()) {
				return nil, false
			}
			if !(SnapOk(ll, x.m()) && SendableIn(ld, ll, ch, tl, x.f())) {
				return nil, false
			}
			if !(w.commit() <= x.f().Commit) {
				return nil, false
			}
			if x.m().typ() == "app" || x.m().typ() == "snap" {
				if !(s.PrevOk(n, x.f()) && (x.stores() || s.HasFirst(n, x.f(), len(x.f().Entries)))) {
					return nil, false
				}
			}
		}
	}
	ns := s.clone()
	ns.CurrentTerm = setInt(s.CurrentTerm, n, x.T1())
	if x.voted() {
		ns.VoteTerm = setInt(s.VoteTerm, n, x.T1())
		ns.VoteFor = setStr(s.VoteFor, n, w.vote())
	}
	ns.Log = setLog(s.Log, n, x.L1())
	ns.CommitIndex = setInt(s.CommitIndex, n, w.commit())
	ns.Role = ro
	ns.Confirmed = setConfirmed(s.Confirmed, n, x.conf1())
	msgs := s.Msgs
	if x.elect() {
		msgs = factsAdd(msgs, s.VoteRequest(n, x.T1()))
	}
	if x.acks() {
		msgs = factsAdd(msgs, AckFact(me, x.f().Src, x.T1(), x.ackAt()))
	}
	ns.Msgs = msgs
	votes := s.Votes
	if x.voted() {
		votes = votesAdd(votes, VoteRec{Voter: me, Term: x.T1(), Cand: w.vote()})
	}
	ns.Votes = votes
	ns.Leaders = ld
	ns.LedLog = ll
	// pre (B 349-359), with msgs' and votes' as just given.
	pre := &Pre{Term: x.T0(), VoteTerm: s.VoteTerm[n], VoteFor: s.VoteFor[n], Commit: s.CommitIndex[n],
		Confirmed: s.Confirmed[n], Msgs: factsMinus(ns.Msgs, s.Msgs), Votes: votesMinus(ns.Votes, s.Votes)}
	if x.stores() {
		pre.Keep = x.first() - 1
		pre.Suffix = SubSeq(x.L0(), x.first(), len(x.L0()))
	} else {
		pre.Keep = len(x.L0())
	}
	if x.acks() {
		pre.Acks = []Fact{AckFact(me, x.f().Src, x.T1(), x.ackAt())}
	}
	if x.stores() {
		pre.Low = x.first()
	}
	if !more {
		ns.Undo = setPre(s.Undo, n, pre)
	} else {
		u := *s.Undo[n]
		nu := u
		nu.Keep = Min(u.Keep, pre.Keep)
		if pre.Keep >= u.Keep {
			nu.Suffix = u.Suffix
		} else {
			nu.Suffix = Concat(SubSeq(x.L0(), pre.Keep+1, u.Keep), u.Suffix)
		}
		nu.Msgs = factsUnion(u.Msgs, pre.Msgs)
		nu.Votes = votesUnion(u.Votes, pre.Votes)
		nu.Acks = factsUnion(u.Acks, pre.Acks)
		nu.Low = Lowest(u.Low, pre.Low)
		ns.Undo = setPre(s.Undo, n, &nu)
	}
	// Safety (B 422-436).
	ns.Chain = x.ch1()
	if x.adv() {
		ns.TermLen = tl.With(x.T1(), Max(x.old(), len(x.newC())))
	} else {
		ns.TermLen = tl
	}
	viol := vi
	if x.adv() && !Comparable(ch, x.newC()) {
		viol = violAdd(viol, "CommitSafety")
	}
	if x.adv() {
		for _, p := range ll {
			if p.T > x.T1() && !IsPrefix(x.newC(), p.L) {
				viol = violAdd(viol, "LeaderCompleteness")
				break
			}
		}
	}
	l1 := x.L1()
	l0 := x.L0()
	changed := !EntriesEqual(l1, l0)
	if changed {
		for b := range s.Cfg.Server {
			if b != n && !Matching(l1, s.Log[b]) {
				viol = violAdd(viol, "LogMatching")
				break
			}
		}
	}
	if (changed || x.adv()) && !IsPrefix(SubSeq(x.ch1(), 1, w.commit()), l1) {
		viol = violAdd(viol, "CommittedEntriesPreserved")
	}
	c1 := x.conf1()
	if x.adv() && (c1.Term != x.T1() || w.commit() > c1.Index) {
		viol = violAdd(viol, "CommitBeyondConfirmed")
	}
	ns.Viol = viol
	return ns, true
}

// queued is the item of a `ready`/`mem` report: `[ev |-> ev, m |-> IF ev.by = "recv" THEN
// pending[n] ELSE <<>>]` (B 441, 452).
func (s *State) queued(n int, ev *Event) QItem {
	if ev.by() == "recv" {
		return QItem{Ev: ev, M: s.Pending[n]}
	}
	return QItem{Ev: ev, M: nil}
}

// Ready is B 439-447.
func (s *State) Ready(n int, ev *Event) (*State, bool) {
	if len(s.Queue[n]) != 0 {
		return nil, false
	}
	r := s.InMemory(n, ev)
	if !r.Ok {
		return nil, false
	}
	ns, ok := s.OnDisk(n, s.queued(n, ev), false, r.Role, r.Leaders, r.LedLog, r.Chain, r.TermLen, r.Viol)
	if !ok {
		return nil, false
	}
	ns.LedConf = r.LedConf
	ns.LedAt = r.LedAt
	ns.ElAt = r.ElAt
	ns.Config = r.Config
	ns.ConfAt = r.ConfAt
	return ns, true
}

// Mem is B 450-459.
func (s *State) Mem(n int, ev *Event) (*State, bool) {
	r := s.InMemory(n, ev)
	if !r.Ok {
		return nil, false
	}
	ns := s.clone()
	ns.Role = r.Role
	ns.Leaders = r.Leaders
	ns.LedLog = r.LedLog
	ns.LedConf = r.LedConf
	ns.LedAt = r.LedAt
	ns.ElAt = r.ElAt
	ns.Config = r.Config
	ns.ConfAt = r.ConfAt
	ns.Chain = r.Chain
	ns.TermLen = r.TermLen
	ns.Viol = r.Viol
	if ev.w() == 1 {
		q := s.Queue[n]
		nq := make([]QItem, 0, len(q)+1)
		nq = append(nq, q...)
		nq = append(nq, s.queued(n, ev))
		ns.Queue = setQueue(s.Queue, n, nq)
	}
	return ns, true
}

// Write is B 462-470.
func (s *State) Write(n int, ev *Event) (*State, bool) {
	if len(s.Queue[n]) == 0 {
		return nil, false
	}
	q := s.Queue[n][0]
	w := q.Ev
	if !(ev.term() == w.term() && ev.vote() == w.vote() && ev.commit() == w.commit() && ev.first() == w.first() &&
		EntriesEqual(ev.entries(), w.entries())) {
		return nil, false
	}
	ns, ok := s.OnDisk(n, q, false, s.Role, s.Leaders, s.LedLog, s.Chain, s.TermLen, s.Viol)
	if !ok {
		return nil, false
	}
	ns.Queue = setQueue(s.Queue, n, s.Queue[n][1:])
	return ns, true
}

// Flush is B 474-478.
func (s *State) Flush(n int, ev *Event) (*State, bool) {
	if len(s.Queue[n]) == 0 {
		return nil, false
	}
	ns, ok := s.OnDisk(n, s.Queue[n][0], ev.more() == 1, s.Role, s.Leaders, s.LedLog, s.Chain, s.TermLen, s.Viol)
	if !ok {
		return nil, false
	}
	ns.Queue = setQueue(s.Queue, n, s.Queue[n][1:])
	return ns, true
}

// Net is B 483-492.
func (s *State) Net(n int, ev *Event) (*State, bool) {
	if s.Undo[n] == nil {
		return nil, false
	}
	u := s.Undo[n]
	if !(ev.term() == s.CurrentTerm[n] && ev.vote() == s.Vote(n) && ev.commit() == s.CommitIndex[n]) {
		return nil, false
	}
	if len(ev.entries()) == 0 {
		if u.Low != 0 {
			return nil, false
		}
	} else {
		ln := len(s.Log[n])
		if !(u.Low == ev.first() && ln == ev.first()+len(ev.entries())-1 &&
			EntriesEqual(SubSeq(s.Log[n], ev.first(), ln), ev.entries())) {
			return nil, false
		}
	}
	nu := *u
	nu.Low = 0
	ns := s.clone()
	ns.Undo = setPre(s.Undo, n, &nu)
	return ns, true
}

// Made is B 496-499.
func (s *State) Made(n int, ev *Event) (*State, bool) {
	if s.Undo[n] == nil {
		return nil, false
	}
	nu := *s.Undo[n]
	nu.Made = true
	ns := s.clone()
	ns.Undo = setPre(s.Undo, n, &nu)
	return ns, true
}

// Wrote is B 502-504.
func (s *State) Wrote(n int, ev *Event) (*State, bool) {
	ns := s.clone()
	ns.Undo = setPre(s.Undo, n, nil)
	return ns, true
}

// ---------------------------------------------------------------------------------------------

func isForwarded(t string) bool { return t == "readindex" || t == "transfer" || t == "prop" }

func isUnmodelled(t string) bool {
	return t == "prevote" || t == "prevoteresp" || t == "readindex" || t == "readindexresp" || t == "prop" ||
		t == "transfer" || t == "timeoutnow"
}

// Send is B 510-593.
func (s *State) Send(n int, ev *Event) (*State, bool) {
	m := ev.msg()
	me := s.Cfg.Server[n]
	late := ev.has(FCause)
	bt := ev.has(FB)
	var mine []Fact
	var cast []VoteRec
	if bt && s.Undo[n] != nil {
		mine = s.Undo[n].Msgs
		cast = s.Undo[n].Votes
	}
	dur := s.Undo[n] == nil || s.Undo[n].Made
	if !(m.from() == me || isForwarded(m.typ())) {
		return nil, false
	}
	if !(s.Cfg.Server.Has(m.to()) && m.to() != me) {
		return nil, false
	}
	ns := s.clone()
	if !(late || bt) {
		ns.Undo = setPre(s.Undo, n, nil)
	}
	if m.typ() == "vote" {
		if bt {
			if !(dur && (factsHas(s.Msgs, VoteFact(m)) || factsHas(mine, VoteFact(m)))) {
				return nil, false
			}
		} else if !(m.term() == s.CurrentTerm[n] && factsHas(s.Msgs, VoteFact(m))) {
			return nil, false
		}
		return ns, true
	}
	if m.typ() == "voteresp" {
		if !m.reject() {
			v := VoteRec{Voter: me, Term: m.term(), Cand: m.to()}
			if !(votesHas(s.Votes, v) || votesHas(cast, v)) {
				return nil, false
			}
			if bt && !dur {
				return nil, false
			}
			ns.Msgs = factsAdd(s.Msgs, Fact{Type: "grant", Src: me, Dst: m.to(), Term: m.term()})
		}
		return ns, true
	}
	if IsReq(m) {
		if !(bt || (m.term() == s.CurrentTerm[n] && s.Role[n] == Leader)) {
			return nil, false
		}
		if !(SnapOk(s.LedLog, m) && s.Sendable(ReqFactIn(s.LedLog, m))) {
			return nil, false
		}
		return ns, true
	}
	if m.typ() == "appresp" {
		if m.reject() {
			return ns, true
		}
		if bt {
			if m.index() == 0 {
				return ns, true
			}
			if !(s.Undo[n] != nil && dur && factsHas(s.Undo[n].Acks, AckFact(me, m.to(), m.term(), m.index()))) {
				return nil, false
			}
			return ns, true
		}
		var c []Msg
		if late {
			c = ev.cause()
		} else {
			c = s.Pending[n]
		}
		if len(c) != 0 && IsReq(c[0]) && c[0].term() < s.CurrentTerm[n] {
			if !(m.index() == 0 && m.term() == s.CurrentTerm[n]) {
				return nil, false
			}
			return ns, true
		}
		if m.index() == 0 {
			return ns, true
		}
		if len(c) == 0 {
			return nil, false
		}
		cm := msgSeqHead(c)
		f := ReqFactIn(s.LedLog, cm)
		last := f.PrevLogIndex + len(f.Entries)
		if !((cm.typ() == "app" || cm.typ() == "snap") && SnapOk(s.LedLog, cm) && s.Sendable(f)) {
			return nil, false
		}
		if !(m.to() == cm.from() && m.term() == cm.term() && s.CurrentTerm[n] == cm.term()) {
			return nil, false
		}
		if m.index() == last && s.PrevOk(n, f) && s.HasFirst(n, f, len(f.Entries)) {
			ns.Msgs = factsAdd(s.Msgs, AckFact(me, cm.from(), cm.term(), last))
			old := s.Confirmed[n]
			idx := last
			if old.Term == cm.term() {
				idx = Max(old.Index, last)
			}
			ns.Confirmed = setConfirmed(s.Confirmed, n, Confirmed{Term: cm.term(), Index: idx})
			return ns, true
		}
		if !(f.PrevLogIndex < s.CommitIndex[n] && m.index() == s.CommitIndex[n]) {
			return nil, false
		}
		ns.Msgs = factsAdd(s.Msgs, AckFact(me, cm.from(), cm.term(), s.CommitIndex[n]))
		return ns, true
	}
	if m.typ() == "hbresp" {
		t := s.CurrentTerm[n]
		if bt {
			t = s.EffTerm(n)
		}
		if !(t <= m.term()) {
			return nil, false
		}
		return ns, true
	}
	if isUnmodelled(m.typ()) {
		return ns, true
	}
	return nil, false
}

// ---------------------------------------------------------------------------------------------

// ApplyEv is B 598-609.
func (s *State) ApplyEv(n int, ev *Event) (*State, bool) {
	if ev.first() != s.LastApplied[n]+1 {
		return nil, false
	}
	last := ev.first() + len(ev.entries()) - 1
	if !(last <= len(s.Log[n]) && last <= len(s.Chain)) {
		return nil, false
	}
	if !EntriesEqual(SubSeq(s.Chain, 1, last), SubSeq(s.Log[n], 1, last)) {
		return nil, false
	}
	if !EntriesEqual(ev.entries(), SubSeq(s.Log[n], ev.first(), last)) {
		return nil, false
	}
	ns := s.clone()
	ns.LastApplied = setInt(s.LastApplied, n, last)
	if !ev.has(FA) {
		ns.Undo = setPre(s.Undo, n, nil)
	}
	if last > s.MemCommit(n) {
		ns.Viol = violAdd(s.Viol, "ApplyBeyondCommit")
	}
	return ns, true
}

// ConfEv is B 614-630.
func (s *State) ConfEv(n int, ev *Event) (*State, bool) {
	k := ev.index()
	logn := s.Log[n]
	if !(k > s.ConfAt[n] && k <= s.LastApplied[n] && k <= len(logn)) {
		return nil, false
	}
	if !(k <= len(s.Chain) && EntriesEqual(SubSeq(s.Chain, 1, k), SubSeq(logn, 1, k))) {
		return nil, false
	}
	if !IsConf(At(logn, k)) {
		return nil, false
	}
	for q := s.ConfAt[n] + 1; q <= k-1; q++ {
		if IsConf(At(logn, q)) {
			return nil, false
		}
	}
	if !Legal(s.Config[n], At(logn, k).Value) {
		return nil, false
	}
	if s.Role[n] == Leader && !RecordedIn(s.Chain, s.TermLen, logn, k, s.CurrentTerm[n]) {
		return nil, false
	}
	c := NextConf(s.Config[n], At(logn, k).Value)
	if !SameConf(ev, c) {
		return nil, false
	}
	ns := s.clone()
	ns.Config = setConf(s.Config, n, c)
	if s.Role[n] == Leader {
		ns.LedConf = s.LedConf.With(s.CurrentTerm[n], c)
		ns.LedAt = s.LedAt.With(s.CurrentTerm[n], k)
	}
	ns.ConfAt = setInt(s.ConfAt, n, k)
	return ns, true
}

// RestoreEv is B 634-643.
func (s *State) RestoreEv(n int, ev *Event) (*State, bool) {
	k := ev.index()
	if !(k <= len(s.Log[n]) && k <= len(s.Chain)) {
		return nil, false
	}
	if !EntriesEqual(SubSeq(s.Chain, 1, k), SubSeq(s.Log[n], 1, k)) {
		return nil, false
	}
	ns := s.clone()
	ns.LastApplied = setInt(s.LastApplied, n, k)
	if !SameConf(ev, ConfOf(s.Chain, k, s.InitConf())) {
		return nil, false
	}
	if !ev.has(FA) {
		ns.Undo = setPre(s.Undo, n, nil)
	}
	return ns, true
}

// SnapEv is B 647-650.
func (s *State) SnapEv(n int, ev *Event) (*State, bool) {
	if !(ev.index() <= s.LastApplied[n] && ev.index() <= s.CommitIndex[n]) {
		return nil, false
	}
	if TermAt(s.Log[n], ev.index()) != ev.term() {
		return nil, false
	}
	return s.clone(), true
}

// MaxReads is B 56.
const MaxReads = 16

// ReadAsked is B 657-661.
func (s *State) ReadAsked(n int, ev *Event) (*State, bool) {
	r := ReadRec{Ctx: ev.ctx(), Floor: len(s.Chain)}
	old := s.Reads[n]
	q := make([]ReadRec, 0, len(old)+1)
	q = append(q, old...)
	q = append(q, r)
	if len(q) > MaxReads {
		q = q[1:]
	}
	ns := s.clone()
	ns.Reads = setReads(s.Reads, n, q)
	return ns, true
}

// ReadGiven is B 663-667.
func (s *State) ReadGiven(n int, ev *Event) (*State, bool) {
	var kept []ReadRec
	stale := false
	for _, r := range s.Reads[n] {
		if r.Ctx != ev.ctx() {
			kept = append(kept, r)
		}
	}
	for _, r := range s.Reads[n] {
		if r.Ctx == ev.ctx() && ev.index() < r.Floor {
			stale = true
			break
		}
	}
	ns := s.clone()
	ns.Reads = setReads(s.Reads, n, kept)
	if stale {
		ns.Viol = violAdd(s.Viol, "ReadIndexStale")
	}
	return ns, true
}

// Bind is B 669-686.
func (s *State) Bind(n int, ev *Event) (*State, bool) {
	switch ev.E {
	case "boot":
		return s.Boot(n, ev)
	case "recv":
		return s.Recv(n, ev)
	case "ready":
		return s.Ready(n, ev)
	case "mem":
		return s.Mem(n, ev)
	case "write":
		return s.Write(n, ev)
	case "wrote":
		return s.Wrote(n, ev)
	case "flush":
		return s.Flush(n, ev)
	case "net":
		return s.Net(n, ev)
	case "made":
		return s.Made(n, ev)
	case "send":
		return s.Send(n, ev)
	case "apply":
		return s.ApplyEv(n, ev)
	case "restore":
		return s.RestoreEv(n, ev)
	case "conf":
		return s.ConfEv(n, ev)
	case "snap":
		return s.SnapEv(n, ev)
	case "readreq":
		return s.ReadAsked(n, ev)
	case "read":
		return s.ReadGiven(n, ev)
	}
	return nil, false
}

// ---------------------------------------------------------------------------------------------
// Forgetting facts (B 696-723).

// GCBatch is B 58.
const GCBatch = 32

// Garbage is B 696-706.
func (s *State) Garbage() []Fact {
	var out []Fact
	for _, m := range s.Msgs {
		g := false
		if m.Type == "vote" {
			g = s.Over(m.Term)
		} else if m.Type == "grant" {
			g = s.EffTerm(s.idx(m.Dst)) > m.Term
		} else if m.Type == "ack" {
			g = s.EffTerm(s.idx(m.Dst)) > m.Term
			if !g {
				for _, a := range s.Msgs {
					if a.Type == "ack" && a.Src == m.Src && a.Dst == m.Dst && a.Term == m.Term && a.Index > m.Index {
						u := s.Undo[s.idx(a.Src)]
						if u == nil || !factsHas(u.Msgs, a) {
							g = true
							break
						}
					}
				}
			}
		}
		if g {
			out = append(out, m)
		}
	}
	return out
}

// OldVotes is B 708.
func (s *State) OldVotes() []VoteRec {
	var out []VoteRec
	for _, v := range s.Votes {
		if s.EffTerm(s.idx(v.Voter)) > v.Term {
			out = append(out, v)
		}
	}
	return out
}

// StaleLed is B 709.
func (s *State) StaleLed() []int {
	var out []int
	for _, p := range s.LedLog {
		if s.Over(p.T) {
			out = append(out, p.T)
		}
	}
	return out
}

// GCDue is B 711.
func (s *State) GCDue() bool {
	return len(s.Garbage())+len(s.OldVotes()) >= GCBatch || len(s.StaleLed()) != 0
}

// GC is B 713-723 (without its guard GCDue).
func (s *State) GC() *State {
	stale := s.StaleLed()
	ns := s.clone()
	ns.Msgs = factsMinus(s.Msgs, s.Garbage())
	ns.Votes = votesMinus(s.Votes, s.OldVotes())
	ns.LedLog = s.LedLog.Without(stale)
	ns.LedConf = s.LedConf.Without(stale)
	ns.LedAt = s.LedAt.Without(stale)
	ns.ElAt = s.ElAt.Without(stale)
	var ld []LeaderRec
	for _, l := range s.Leaders {
		if !s.Over(l.Term) {
			ld = append(ld, l)
		}
	}
	ns.Leaders = ld
	return ns
}

// Step is B 766-772 (without its guard ~GCDue): event i of the stream bound.
func (s *State) Step(ev *Event) (*State, bool) {
	if ev.Bad != "" {
		evalError(ev.Bad)
	}
	n := s.idx(ev.Node)
	ns, ok := s.Bind(n, ev)
	if !ok {
		return nil, false
	}
	ns.I = s.I + 1
	return ns, true
}
