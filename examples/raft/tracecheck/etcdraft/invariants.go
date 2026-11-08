package etcdraft

// The correctness invariants of etcdraft.tla. Each is a predicate on a state; Invariants lists
// those Traceetcdraft.cfg checks (all but MessageTermsLtCurrentTerm, which no configuration
// checks).

// Committed is `Committed(i) == SubSeq(log[i],1,commitIndex[i])`.
func (s *State) Committed(i ID) []Entry {
	return SubSeq(s.S[i].Log, 1, s.S[i].CommitIndex)
}

// MessageTermsLtCurrentTerm is `MessageTermsLtCurrentTerm(m)` (a property of one message).
func (s *State) MessageTermsLtCurrentTerm(m *Msg) bool {
	v, ok := s.S[m.Source]
	return ok && m.Term <= v.CurrentTerm
}

// LogInv is `LogInv`.
func (s *State) LogInv() bool {
	for _, i := range s.Server {
		for _, j := range s.Server {
			ci, cj := s.Committed(i), s.Committed(j)
			if !(IsPrefix(ci, cj) || IsPrefix(cj, ci)) {
				return false
			}
		}
	}
	return true
}

// MoreThanOneLeaderInv is `MoreThanOneLeaderInv`.
func (s *State) MoreThanOneLeaderInv() bool {
	for _, i := range s.Server {
		for _, j := range s.Server {
			vi, vj := s.S[i], s.S[j]
			if vi.CurrentTerm == vj.CurrentTerm && vi.State == Leader && vj.State == Leader && i != j {
				return false
			}
		}
	}
	return true
}

// maxIndexOfTerm is `MaxOrZero({n \in DOMAIN xlog : xlog[n].term = t})`.
func maxIndexOfTerm(xlog []Entry, t int) int {
	m := 0
	for n := 1; n <= len(xlog); n++ {
		if xlog[n-1].Term == t {
			m = n
		}
	}
	return m
}

// ElectionSafetyInv is `ElectionSafetyInv`.
func (s *State) ElectionSafetyInv() bool {
	for _, i := range s.Server {
		vi := s.S[i]
		if vi.State != Leader {
			continue
		}
		for _, j := range s.Server {
			if maxIndexOfTerm(vi.Log, vi.CurrentTerm) < maxIndexOfTerm(s.S[j].Log, vi.CurrentTerm) {
				return false
			}
		}
	}
	return true
}

// LogMatchingInv is `LogMatchingInv`.
func (s *State) LogMatchingInv() bool {
	for _, i := range s.Server {
		for _, j := range s.Server {
			li, lj := s.S[i].Log, s.S[j].Log
			for n := 1; n <= len(li) && n <= len(lj); n++ {
				if li[n-1].Term == lj[n-1].Term && !EntriesEqual(li[:n], lj[:n]) {
					return false
				}
			}
		}
	}
	return true
}

// QuorumLogInv is `QuorumLogInv`: every quorum of GetConfig(i) has a server whose log extends
// Committed(i). Equivalently: the servers of GetConfig(i) whose log does not extend it are no
// quorum (a quorum's supersets within the configuration are quorums).
func (s *State) QuorumLogInv() bool {
	for _, i := range s.Server {
		cfg := s.GetConfig(i)
		committed := s.Committed(i)
		var without Set
		for _, j := range cfg {
			if v, ok := s.S[j]; !ok || !IsPrefix(committed, v.Log) {
				without = append(without, j)
			}
		}
		if IsQuorum(without, cfg) {
			return false
		}
	}
	return true
}

// MoreUpToDateCorrectInv is `MoreUpToDateCorrectInv`.
func (s *State) MoreUpToDateCorrectInv() bool {
	for _, i := range s.Server {
		for _, j := range s.Server {
			li, lj := s.S[i].Log, s.S[j].Log
			if (LastTerm(li) > LastTerm(lj) || (LastTerm(li) == LastTerm(lj) && len(li) >= len(lj))) &&
				!IsPrefix(s.Committed(j), li) {
				return false
			}
		}
	}
	return true
}

// LeaderCompletenessInv is `LeaderCompletenessInv`. (Where TLC would fail evaluating
// `log[l][idx]` beyond l's log, the invariant is false.)
func (s *State) LeaderCompletenessInv() bool {
	leaders := s.CurrentLeaders()
	for _, i := range s.Server {
		committed := s.Committed(i)
		for idx := 1; idx <= len(committed); idx++ {
			entry := s.S[i].Log[idx-1]
			for _, l := range leaders {
				vl := s.S[l]
				if vl.CurrentTerm > entry.Term && (idx > len(vl.Log) || !vl.Log[idx-1].Equal(entry)) {
					return false
				}
			}
		}
	}
	return true
}

// CommittedIsDurableInv is `CommittedIsDurableInv`.
func (s *State) CommittedIsDurableInv() bool {
	for _, i := range s.Server {
		v := s.S[i]
		if v.State == Leader && v.CommitIndex > v.Durable.Log {
			return false
		}
	}
	return true
}

// An Invariant is a named invariant.
type Invariant struct {
	Name  string
	Holds func(*State) bool
}

// Invariants are the invariants Traceetcdraft.cfg checks, in its order.
var Invariants = []Invariant{
	{"LogInv", (*State).LogInv},
	{"MoreThanOneLeaderInv", (*State).MoreThanOneLeaderInv},
	{"ElectionSafetyInv", (*State).ElectionSafetyInv},
	{"LogMatchingInv", (*State).LogMatchingInv},
	{"QuorumLogInv", (*State).QuorumLogInv},
	{"MoreUpToDateCorrectInv", (*State).MoreUpToDateCorrectInv},
	{"LeaderCompletenessInv", (*State).LeaderCompletenessInv},
	{"CommittedIsDurableInv", (*State).CommittedIsDurableInv},
}

// Violated is the name of the first invariant s violates, or "".
func (s *State) Violated() string {
	for _, inv := range Invariants {
		if !inv.Holds(s) {
			return inv.Name
		}
	}
	return ""
}
