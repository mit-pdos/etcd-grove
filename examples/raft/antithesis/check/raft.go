package check

// The operators of EtcdRaft.tla (R) the binding uses. Those that read the model's variables are
// methods of State, evaluated in that state.

// Majority is R 127 `Majority(S, V) == Cardinality(S \cap V) * 2 > Cardinality(V)`.
func Majority(s, v Set) bool { return interCount(s, v)*2 > len(v) }

// IsQuorum is R 129 `IsQuorum(S, C) == Majority(S, C.in) /\ (C.out = {} \/ Majority(S, C.out))`.
func IsQuorum(s Set, c Conf) bool {
	return Majority(s, c.In) && (len(c.Out) == 0 || Majority(s, c.Out))
}

// IsConf is R 139 `IsConf(e) == e.type = "conf"`.
func IsConf(e Entry) bool { return e.Type == "conf" }

// Target is R 142 `Target(C, d) == (C.in \cup Range(d.add)) \ Range(d.remove)`.
func Target(c Conf, d Value) Set {
	r := d.rec()
	return c.In.Union(SetOf(r.Add)).Minus(SetOf(r.Remove))
}

// NextConf is R 145-147.
func NextConf(c Conf, d Value) Conf {
	if d.rec().Leave {
		return Conf{In: c.In, Out: nil}
	}
	t := Target(c, d)
	if d.Joint {
		return Conf{In: t, Out: c.In}
	}
	return Conf{In: t, Out: nil}
}

// Legal is R 152-156.
func Legal(c Conf, d Value) bool {
	if d.rec().Leave {
		return len(c.Out) != 0
	}
	if len(c.Out) != 0 {
		return false
	}
	t := Target(c, d)
	if len(t) == 0 {
		return false
	}
	return d.Joint || len(c.In.Minus(t).Union(t.Minus(c.In))) <= 1
}

// LastConf is R 161: the last index k in 1..a with IsConf(l[k]), 0 for none.
func LastConf(l []Entry, a int) int {
	last := 0
	for k := 1; k <= a; k++ {
		if IsConf(At(l, k)) {
			last = k
		}
	}
	return last
}

// ConfOf is R 163-168: the configuration the changes among the first a entries of l make.
func ConfOf(l []Entry, a int, initConf Conf) Conf {
	if a < 0 {
		evalError("ConfOf: a recursive function applied outside 0..a")
	}
	c := initConf
	for k := 1; k <= a; k++ {
		e := At(l, k)
		if IsConf(e) {
			c = NextConf(c, e.Value)
		}
	}
	return c
}

// confsAfterCount is R 171 `Cardinality(ConfsAfter(l, a))`, ConfsAfter(l, a) == {k \in (a + 1)..Len(l)
// : IsConf(l[k])}.
func confsAfterCount(l []Entry, a int) int {
	n := 0
	for k := a + 1; k <= len(l); k++ {
		if IsConf(l[k-1]) {
			n++
		}
	}
	return n
}

// InitConf is R 140 `InitConf == [in |-> InitVoters, out |-> {}]`.
func (s *State) InitConf() Conf { return Conf{In: s.Cfg.InitVoters, Out: nil} }

// AllSwitched is R 174 `AllSwitched(i, l) == ConfsAfter(l, confAt[i]) = {}`.
func (s *State) AllSwitched(i int, l []Entry) bool { return confsAfterCount(l, s.ConfAt[i]) == 0 }

// OneWaiting is R 175 `OneWaiting(i, l) == Cardinality(ConfsAfter(l, confAt[i])) <= 1`.
func (s *State) OneWaiting(i int, l []Entry) bool { return confsAfterCount(l, s.ConfAt[i]) <= 1 }

// LastTerm is R 132 `LastTerm(i) == TermAt(log[i], Len(log[i]))`.
func (s *State) LastTerm(i int) int { return TermAt(s.Log[i], len(s.Log[i])) }

// VoteRequest is R 217-219.
func (s *State) VoteRequest(i int, t int) Fact {
	return Fact{Type: "vote", Src: s.Cfg.Server[i], Term: t, LastLogIndex: len(s.Log[i]),
		LastLogTerm: s.LastTerm(i)}
}

// UpToDate is R 237-239, for a vote request m.
func (s *State) UpToDate(m Fact, i int) bool {
	return m.LastLogTerm > s.LastTerm(i) || (m.LastLogTerm == s.LastTerm(i) && m.LastLogIndex >= len(s.Log[i]))
}

// Granted is R 277-280.
func (s *State) Granted(i int) Set {
	var out Set
	me := s.Cfg.Server[i]
	for _, j := range s.Cfg.Server {
		if j != me && factsHas(s.Msgs, Fact{Type: "grant", Src: j, Dst: me, Term: s.CurrentTerm[i]}) {
			out = SetAdd(out, j)
		}
	}
	if votesHas(s.Votes, VoteRec{Voter: me, Term: s.CurrentTerm[i], Cand: me}) {
		out = SetAdd(out, me)
	}
	return out
}

// Acked is R 344-347.
func (s *State) Acked(i int, t int, c int) Set {
	var out Set
	me := s.Cfg.Server[i]
	for _, j := range s.Cfg.Server {
		for _, a := range s.Msgs {
			if a.Type == "ack" && a.Src == j && a.Dst == me && a.Term == t && a.Index >= c {
				out = SetAdd(out, j)
				break
			}
		}
	}
	return out
}

// PrevOk is R 366-369.
func (s *State) PrevOk(j int, m AppendFact) bool {
	if m.PrevLogIndex == 0 {
		return true
	}
	return m.PrevLogIndex <= len(s.Log[j]) && At(s.Log[j], m.PrevLogIndex).Term == m.PrevLogTerm
}

// HasFirst is R 372-375.
func (s *State) HasFirst(j int, m AppendFact, k int) bool {
	for q := 1; q <= k; q++ {
		if !(m.PrevLogIndex+q <= len(s.Log[j]) && At(s.Log[j], m.PrevLogIndex+q).Term == At(m.Entries, q).Term) {
			return false
		}
	}
	return true
}

// ElectionSafety is R 581-582.
func (s *State) ElectionSafety() bool {
	for _, a := range s.Leaders {
		for _, b := range s.Leaders {
			if a.Term == b.Term && a.Server != b.Server {
				return false
			}
		}
	}
	return true
}

// OneVotePerTerm is R 585-586.
func (s *State) OneVotePerTerm() bool {
	for _, a := range s.Votes {
		for _, b := range s.Votes {
			if a.Voter == b.Voter && a.Term == b.Term && a.Cand != b.Cand {
				return false
			}
		}
	}
	return true
}
