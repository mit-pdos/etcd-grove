package winpendprobe

import (
	"io"
	"sort"
	"log"
	"math/rand"
	"testing"
)

var discard = log.New(io.Discard, "", 0)

func base(seed int64) Params {
	return Params{Seed: seed, SnapCount: 20, CatchUp: 5, ApplyPerRound: 1, PreVote: true}
}

func settle(s *Sim, n int) {
	for i := 0; i < n; i++ {
		s.Step()
	}
}

func dump(t *testing.T, s *Sim) {
	for _, l := range s.Log {
		t.Log(l)
	}
	for _, r := range s.Restarts {
		t.Logf("restart m%d round %d HSterm %d wasLeaderAtT %v sentSnapAtT %v replayLen %d", r.Member, r.Round, r.HSTerm, r.WasLeaderAtT, r.SentSnapAtT, r.ReplayLen)
		for _, b := range r.Batches {
			t.Logf("   replay batch rt=%d applied r%d failNow=%v failAny=%v", b.Rt, b.Round, b.FailNow, b.FailAny)
		}
	}
}

// scenario (a)/(b): leader 1 at T, follower 3 lags past the compacted index
// (a: MsgSnap sent) or not (b), then 1 is killed; restartDelay rounds later it
// restarts (0: before 2 and 3 can elect; 40: after).
func scenario(t *testing.T, withSnap bool, restartDelay int, p Params) *Sim {
	s := NewSim(p)
	s.Verbose = true
	s.Campaign(1)
	settle(s, 5)
	if s.Leader() != 1 {
		t.Fatalf("no leader 1")
	}
	T := s.Term(1)
	if withSnap {
		s.Partition(3, true)
	}
	for i := 0; i < 30; i++ {
		s.Propose(3)
		s.Step()
	}
	if withSnap {
		s.Partition(3, false)
	}
	settle(s, 60) // 3 catches up (by MsgSnap if partitioned); apply catches up
	s.Propose(40) // a backlog so the replay is long
	settle(s, 3)
	s.Propose(7)
	settle(s, 3)
	if s.Term(1) != T || s.Leader() != 1 {
		t.Fatalf("leader changed")
	}
	s.Kill(1)
	settle(s, restartDelay)
	s.RestartMember(1)
	settle(s, 200)
	s.Finish()
	dump(t, s)
	snaps := 0
	for _, r := range s.SentSnap[1] {
		if r.term == T {
			snaps++
		}
	}
	t.Logf("T=%d, MsgSnaps sent by 1 at T: %d; term of 2 now %d", T, snaps, s.Term(2))
	return s
}

func checkOutcome(t *testing.T, s *Sim, wantSnap bool) {
	r := s.Restarts[0]
	if wantSnap != r.SentSnapAtT {
		t.Errorf("SentSnapAtT = %v", r.SentSnapAtT)
	}
	fail := false
	for _, b := range r.Batches {
		if b.Rt == r.HSTerm {
			t.Logf("replay batch at rt = T = %d", b.Rt)
		}
		fail = fail || b.FailAny
	}
	t.Logf("OUTCOME: replay batches %d, premise fails: %v, LeanText proxy fails: %v", len(r.Batches), fail, s.LeanTextFails(r))
}

func TestScenarioA_RestartBeforeElection(t *testing.T) {
	for _, slow := range []bool{false, true} {
		p := base(1)
		if slow {
			p.ReadyPerRound, p.MaxCommittedReady = 1, 1
		}
		s := scenario(t, true, 0, p)
		checkOutcome(t, s, true)
	}
}

func TestScenarioA_RestartAfterElection(t *testing.T) {
	for _, slow := range []bool{false, true} {
		p := base(2)
		if slow {
			p.ReadyPerRound, p.MaxCommittedReady = 1, 1
		}
		s := scenario(t, true, 40, p)
		checkOutcome(t, s, true)
	}
}

func TestScenarioB_NoSnap(t *testing.T) {
	for _, d := range []int{0, 40} {
		s := scenario(t, false, d, base(3))
		checkOutcome(t, s, false)
		if len(s.SentSnap[1]) != 0 {
			t.Errorf("unexpected MsgSnap")
		}
	}
}

type stats struct {
	restarts, formerLeader, flSentSnapAtT, flSentAny       int
	batches, batchesRt0, batchesRtT, batchesFailNow        int
	restartsFail, flFail, flSentAnyFail, leanTextFail, flLeanTextFail int
	flRtT, failRtGtT, failSameInc, failOtherInc, failRtEqT, flReplayAllRt0 int
	rtHist                                                 map[string]int
}

// TestRandomized: random proposals, random lagging (partition a follower),
// random kill/restart of a random member (biased to the leader).
func TestRandomized(t *testing.T) {
	for _, mode := range []string{"etcd-like", "slow-handout", "slow-handout-novote"} {
		st := stats{rtHist: map[string]int{}}
		for seed := int64(0); seed < 400; seed++ {
			p := base(seed)
			p.ApplyPerRound = 1 + int(seed%3)
			if mode != "etcd-like" {
				p.ReadyPerRound, p.MaxCommittedReady = 1, 1
			}
			p.PreVote = mode != "slow-handout-novote"
			s := NewSim(p)
			rng := rand.New(rand.NewSource(seed * 7919))
			s.Campaign(1)
			down := map[uint64]int{} // member -> round to restart
			for r := 0; r < 1500; r++ {
				s.Propose(rng.Intn(4))
				// lagging: partition a random follower for a while
				if rng.Intn(60) == 0 {
					id := uint64(1 + rng.Intn(3))
					s.Partition(id, true)
					down[100+id] = s.Round + 10 + rng.Intn(60)
				}
				for _, k := range keys(down) {
					v := down[k]
					if k > 100 && v == s.Round {
						s.Partition(k-100, false)
						delete(down, k)
					}
				}
				// kill: 2/3 the leader, else a random member; at most one down
				if rng.Intn(80) == 0 {
					anyDown := false
					for k := range down {
						if k < 100 {
							anyDown = true
						}
					}
					if !anyDown {
						id := s.Leader()
						if id == 0 || rng.Intn(3) == 0 {
							id = uint64(1 + rng.Intn(3))
						}
						s.Kill(id)
						down[id] = s.Round + rng.Intn(40)
					}
				}
				for _, k := range keys(down) {
					v := down[k]
					if k < 100 && v <= s.Round {
						s.RestartMember(k)
						delete(down, k)
					}
				}
				s.Step()
			}
			s.Finish()
			for _, r := range s.Restarts {
				st.restarts++
				fail := false
				sentAny := len(s.SentSnap[r.Member]) > 0
				allRt0 := true
				for _, b := range r.Batches {
					if b.Rt != 0 {
						allRt0 = false
					}
					if r.WasLeaderAtT && b.Rt == r.HSTerm {
						st.flRtT++
					}
					if b.FailAny {
						if b.Rt > r.HSTerm {
							st.failRtGtT++
						} else if b.Rt == r.HSTerm {
							st.failRtEqT++
						}
						for _, rec := range s.SentSnap[r.Member] {
							if rec.term == b.Rt {
								if rec.inc == b.Inc {
									st.failSameInc++
								} else {
									st.failOtherInc++
								}
								break
							}
						}
					}
					st.batches++
					switch {
					case b.Rt == 0:
						st.batchesRt0++
						st.rtHist["0"]++
					case b.Rt == r.HSTerm:
						st.batchesRtT++
						st.rtHist["=T"]++
					case b.Rt > r.HSTerm:
						st.rtHist[">T"]++
					default:
						st.rtHist["<T"]++
					}
					if b.FailNow {
						st.batchesFailNow++
					}
					fail = fail || b.FailAny
				}
				if r.WasLeaderAtT && allRt0 {
					st.flReplayAllRt0++
				}
				lt := s.LeanTextFails(r)
				if fail {
					st.restartsFail++
				}
				if lt {
					st.leanTextFail++
				}
				if r.WasLeaderAtT {
					st.formerLeader++
					if r.SentSnapAtT {
						st.flSentSnapAtT++
					}
					if sentAny {
						st.flSentAny++
						if fail {
							st.flSentAnyFail++
						}
					}
					if fail {
						st.flFail++
					}
					if lt {
						st.flLeanTextFail++
					}
				}
			}
		}
		t.Logf("[%s] restarts %d; of them former leaders at T (leader at their HardState term) %d", mode, st.restarts, st.formerLeader)
		t.Logf("[%s]   former leaders that sent a MsgSnap at T: %d; that ever sent one: %d", mode, st.flSentSnapAtT, st.flSentAny)
		t.Logf("[%s]   premise fails (replay batch rt = term of a MsgSnap of this member): all restarts %d, former leaders %d (of those that sent any MsgSnap: %d)", mode, st.restartsFail, st.flFail, st.flSentAnyFail)
		t.Logf("[%s]   Lean-text proxy fails (a0 nonempty and a MsgSnap at a term with a commit): all %d, former leaders %d", mode, st.leanTextFail, st.flLeanTextFail)
		t.Logf("[%s] former-leader replay batches with rt = T: %d; former-leader restarts whose replay is all rt=0: %d", mode, st.flRtT, st.flReplayAllRt0)
		t.Logf("[%s] failing batches: rt > T %d, rt = T %d; the MsgSnap from the same incarnation %d, an earlier one %d", mode, st.failRtGtT, st.failRtEqT, st.failSameInc, st.failOtherInc)
		t.Logf("[%s] replay batches %d: rt histogram %v; batches failing at apply time %d", mode, st.batches, st.rtHist, st.batchesFailNow)
	}
}

func keys(m map[uint64]int) []uint64 {
	var ks []uint64
	for k := range m {
		ks = append(ks, k)
	}
	sort.Slice(ks, func(i, j int) bool { return ks[i] < ks[j] })
	return ks
}

// Scenario D (the failing shape): 1 leads at T while 3 lags; 1 and 2 crash;
// 1 restarts alone with 3 (healed). 1 wins the election at T' > T while its
// replay is still being handed out, and sends 3 a MsgSnap at T'; the replay
// batches handed out after that carry raftTerm T'.
func TestScenarioD_LeaderAgainDuringReplay(t *testing.T) {
	for _, slow := range []bool{false, true} {
		p := base(5)
		if slow {
			p.ReadyPerRound, p.MaxCommittedReady = 1, 1
		}
		s := NewSim(p)
		s.Verbose = true
		s.Campaign(1)
		settle(s, 5)
		s.Partition(3, true)
		for i := 0; i < 40; i++ {
			s.Propose(5)
			s.Step()
		}
		settle(s, 3)
		s.Kill(1)
		s.Kill(2)
		s.Partition(3, false)
		settle(s, 2)
		s.RestartMember(1)
		settle(s, 300)
		s.Finish()
		dump(t, s)
		r := s.Restarts[0]
		n, f := 0, 0
		for _, b := range r.Batches {
			n++
			if b.FailNow {
				f++
			}
		}
		t.Logf("OUTCOME slow=%v: T=%d, replay batches %d, failing at apply time %d; MsgSnaps of 1: %v", slow, r.HSTerm, n, f, s.SentSnap[1])
	}
}

// TestZZZ_Totals prints the follow-up checks, accumulated over the tests run before it.
func TestZZZ_Totals(t *testing.T) {
	t.Logf("MsgSnaps sent by restarted incarnations: %d; with Term <= restored HardState term: %d", Totals.RestartedMsgSnaps, Totals.RestartedMsgSnapBad)
	t.Logf("snapshot installs at a restarted member: in the replay window %d, outside %d", Totals.InstallsInWindow, Totals.InstallsOutsideWindow)
	t.Logf("in-window installs vs ghost (restored last index): < %d, = %d, > %d; snapIdx <= commit at restart: %d", Totals.SnapLtGhost, Totals.SnapEqGhost, Totals.SnapGtGhost, Totals.SnapLeReplayCommit)
	for _, tr := range Totals.Traces {
		t.Log(tr)
	}
}
