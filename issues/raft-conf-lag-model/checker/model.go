// The transition system of ../model.py, transcribed action by action (the comments
// name the Python lines they follow). README.md lists the deviations (none in the
// semantics; a ghost and extra invariants are added).
package main

import (
	"fmt"
	"math/bits"
	"strings"
)

const (
	MaxN   = 5 // nodes
	MaxLog = 6 // log entries per node
)

// Log entry: term<<12 | kind<<10 | op<<8 | arg.
const (
	KE = 1 // empty (leader's entry at election)
	KV = 2 // value; arg = value number
	KC = 3 // conf change; op, arg below
)
const (
	OpAdd   = 0 // arg = node id
	OpRem   = 1 // arg = node id
	OpEnter = 2 // arg = bitmask of the new incoming set (joint)
	OpLeave = 3
)

func mkEnt(t, k, op, arg int) uint16 { return uint16(t<<12 | k<<10 | op<<8 | arg) }
func eTerm(e uint16) int             { return int(e >> 12) }
func eKind(e uint16) int             { return int(e>>10) & 3 }
func eOp(e uint16) int               { return int(e>>8) & 3 }
func eArg(e uint16) int              { return int(e & 0xff) }

const (
	RF = 0
	RL = 1
)

// Node is model.py's (term, role, log, commit, applied, cfgidx, match, pending, pcommit).
// Match and Pending are zero at a follower (model.py's () and 0).
type Node struct {
	Term, Role, Len                           uint8
	Commit, Applied, CfgIdx, Pending, PCommit uint8
	Match                                     [MaxN]uint8
	Log                                       [MaxLog]uint16
}

// State is model.py's (nodes, nc, nv), plus the ghost Won (bit t: term t had a winner),
// used for election safety (zero unless -es).
type State struct {
	Nodes       [MaxN]Node
	NC, NV, Won uint8
	// ghost of one pending read-index request (-read): reader id (0: none), its term,
	// the read index (its commit at arrival), the largest commit of any node at arrival.
	RdNode, RdTerm, RdIdx, RdMax uint8
}

// Parameters (model.py's argv).
var (
	N                int
	INIT             uint8 // bitmask of the initial voters 1..init
	NInit            int
	Mode             string // faithful, lag, crash, fix, fixlit
	MAXT             int
	MAXLOG           int
	MAXCONF          int
	MAXVAL           int
	JOINT            bool
	REDUCED          bool
	GhostES          bool
	ReadIdx          bool  // read-index requests (extension, not in model.py)
	ReadNoTermCheck  bool  // validation only: drop committedEntryInCurrentTerm (must fail)
	ReadSingletonBug bool  // the pinned raft: a singleton leader answers without that check (review finding 1)
	RemSelf          bool  // a leader may propose its own removal (not in model.py)
	NoStepDown       bool  // StepDownOnRemoval off: a removed leader stays leader (model.py steps down)
	lagging          bool  // apply does not move cfgidx; applyconf is an action (at the nodes of LagMask)
	LagMask          uint8 // the nodes whose application may lag (-lagnodes; default all)
	InvMask          int   // the invariants checked (bit per violation kind, -inv)
	guardCfg         bool  // fix modes: the campaign guard scans from cfgidx
)

func bit(i int) uint8 { return 1 << (i - 1) }

type Cfg struct{ inc, out uint8 }

// cfg_at
func cfgAt(n *Node, k int) Cfg {
	c := Cfg{INIT, 0}
	for _, e := range n.Log[:k] {
		if eKind(e) != KC {
			continue
		}
		switch eOp(e) {
		case OpAdd:
			c.inc |= bit(eArg(e))
		case OpRem:
			c.inc &^= bit(eArg(e))
		case OpEnter:
			c.out, c.inc = c.inc, uint8(eArg(e))
		case OpLeave:
			c.out = 0
		}
	}
	return c
}

func pc(x uint8) int { return bits.OnesCount8(x) }

func maj(S, C uint8) bool { return pc(S&C)*2 > pc(C) }

func isq(c Cfg, S uint8) bool {
	return c.inc != 0 && maj(S, c.inc) && (c.out == 0 || maj(S, c.out))
}

func lastTerm(n *Node) int {
	if n.Len == 0 {
		return 0
	}
	return eTerm(n.Log[n.Len-1])
}

// uptodate(a, b): a at least as up to date as b.
func uptodate(a, b *Node) bool {
	ta, tb := lastTerm(a), lastTerm(b)
	return ta > tb || (ta == tb && a.Len >= b.Len)
}

func hasConf(n *Node, from, to int) bool {
	for p := from; p < to; p++ {
		if eKind(n.Log[p]) == KC {
			return true
		}
	}
	return false
}

// confApplied (guard-fix.md): the applied index, or the index before the oldest conf
// entry handed out (at or below applied) and not yet passed to ApplyConfChange.
func confApplied(n *Node) uint8 {
	for p := int(n.CfgIdx); p < int(n.Applied); p++ {
		if eKind(n.Log[p]) == KC {
			return uint8(p)
		}
	}
	return n.Applied
}

// Action labels, formatted as model.py's tuples.
const (
	AElect = iota
	APropV
	APropC
	AApp
	ACommit
	AApply
	AApplyConf
	ACrash
	AReadReq
	AReadOk
	AReadDrop
	AReadSingle
)

type Action struct {
	Kind uint8
	I, J uint8 // J: app's target
	X    uint8 // elect: T; propv: value; app: q; commit: Nn; apply/applyconf: index; crash: pcommit
	Set  uint8 // elect: voters S
	Ent  uint16
}

func tupleOfMask(m uint8) string {
	var xs []string
	for j := 1; j <= 8; j++ {
		if m&bit(j) != 0 {
			xs = append(xs, fmt.Sprint(j))
		}
	}
	if len(xs) == 1 {
		return "(" + xs[0] + ",)"
	}
	return "(" + strings.Join(xs, ", ") + ")"
}

func opString(e uint16) string {
	switch eOp(e) {
	case OpAdd:
		return fmt.Sprintf("('add', %d)", eArg(e))
	case OpRem:
		return fmt.Sprintf("('rem', %d)", eArg(e))
	case OpEnter:
		return fmt.Sprintf("('enter', %s)", tupleOfMask(uint8(eArg(e))))
	}
	return "('leave',)"
}

func (a Action) String() string {
	switch a.Kind {
	case AElect:
		return fmt.Sprintf("('elect', %d, %s, %d)", a.I, tupleOfMask(a.Set), a.X)
	case APropV:
		return fmt.Sprintf("('propv', %d, %d)", a.I, a.X)
	case APropC:
		return fmt.Sprintf("('propc', %d, %s)", a.I, opString(a.Ent))
	case AApp:
		return fmt.Sprintf("('app', %d, %d, %d)", a.I, a.J, a.X)
	case ACommit:
		return fmt.Sprintf("('commit', %d, %d)", a.I, a.X)
	case AApply:
		return fmt.Sprintf("('apply', %d, %d)", a.I, a.X)
	case AApplyConf:
		return fmt.Sprintf("('applyconf', %d, %d)", a.I, a.X)
	case ACrash:
		return fmt.Sprintf("('crash', %d, %d)", a.I, a.X)
	case AReadReq:
		return fmt.Sprintf("('readreq', %d, %d)", a.I, a.X)
	case AReadOk:
		return fmt.Sprintf("('readok', %d, %d)", a.I, a.X)
	case AReadDrop:
		return "('readdrop',)"
	case AReadSingle:
		return fmt.Sprintf("('readsingle', %d, %d)", a.I, a.X)
	}
	return "?"
}

func entString(e uint16) string {
	switch eKind(e) {
	case KE:
		return fmt.Sprintf("(%d, 'e', None)", eTerm(e))
	case KV:
		return fmt.Sprintf("(%d, 'v', %d)", eTerm(e), eArg(e))
	}
	return fmt.Sprintf("(%d, 'c', %s)", eTerm(e), opString(e))
}

func (s *State) Dump() string {
	var b strings.Builder
	for i := 1; i <= N; i++ {
		n := &s.Nodes[i-1]
		role := "F"
		if n.Role == RL {
			role = "L"
		}
		var es []string
		for _, e := range n.Log[:n.Len] {
			es = append(es, entString(e))
		}
		c := cfgAt(n, int(n.CfgIdx))
		fmt.Fprintf(&b, "  node %d term %d %s log [%s] commit %d applied %d cfgidx %d cfg %s",
			i, n.Term, role, strings.Join(es, ", "), n.Commit, n.Applied, n.CfgIdx, tupleOfMask(c.inc))
		if c.out != 0 {
			fmt.Fprintf(&b, "&%s", tupleOfMask(c.out))
		}
		if n.Role == RL {
			fmt.Fprintf(&b, " match %v pending %d", n.Match[:N], n.Pending)
		}
		if Mode == "crash" {
			fmt.Fprintf(&b, " pcommit %d", n.PCommit)
		}
		b.WriteString("\n")
	}
	if s.RdNode != 0 {
		fmt.Fprintf(&b, "  pending read: leader %d term %d read index %d, largest commit at arrival %d\n", s.RdNode, s.RdTerm, s.RdIdx, s.RdMax)
	}
	return b.String()
}

// Violation kinds.
const (
	VNone        = iota
	VSMS         // two nodes' committed prefixes differ (model.py's safe)
	VLogMatch    // same term at an index, different prefixes
	VElection    // two winners of one term (ghost Won)
	VLeaderCompl // a winner's log lacks some node's committed prefix
	VRead        // a confirmed read index below a commit that preceded the request
)

var vName = []string{"none", "state machine safety", "log matching", "election safety", "leader completeness", "read-index linearizability"}

// checkState: state invariants (safe() of model.py, plus log matching).
func checkState(s *State) int {
	v := checkState1(s)
	if InvMask&(1<<v) == 0 {
		return VNone
	}
	return v
}

func checkState1(s *State) int {
	for a := 0; a < N; a++ {
		na := &s.Nodes[a]
		for b := a + 1; b < N; b++ {
			nb := &s.Nodes[b]
			k := na.Commit
			if nb.Commit < k {
				k = nb.Commit
			}
			for p := 0; p < int(k); p++ {
				if na.Log[p] != nb.Log[p] {
					return VSMS
				}
			}
			m := na.Len
			if nb.Len < m {
				m = nb.Len
			}
			// log matching: the last index where both have the same term must have equal prefixes
			for p := int(m) - 1; p >= 0; p-- {
				if eTerm(na.Log[p]) == eTerm(nb.Log[p]) {
					for q := 0; q <= p; q++ {
						if na.Log[q] != nb.Log[q] {
							return VLogMatch
						}
					}
					break
				}
			}
		}
	}
	return VNone
}

// succ enumerates model.py's succ(st). emit gets the action, the successor and a
// transition violation (election safety, leader completeness at a win).
func succ(s *State, emit func(a Action, ns *State, viol int)) {
	var ns State
	for i := 1; i <= N; i++ {
		n := &s.Nodes[i-1]
		term := int(n.Term)
		L := int(n.Len)
		cfg := cfgAt(n, int(n.CfgIdx))
		// election (atomic; pre-vote uses the same quorum and up-to-date check)
		if n.Role != RL && (cfg.inc|cfg.out)&bit(i) != 0 {
			gfrom := int(n.Applied)
			if guardCfg {
				gfrom = int(n.CfgIdx)
			}
			if !hasConf(n, gfrom, int(n.Commit)) { // hasUnappliedConfChanges
				var others uint8
				for j := 1; j <= N; j++ {
					if j != i && uptodate(n, &s.Nodes[j-1]) {
						others |= bit(j)
					}
				}
				// every subset V of others
				for V := others; ; V = (V - 1) & others {
					S := V | bit(i)
					if isq(cfg, S) {
						T := 0
						for j := 1; j <= N; j++ {
							if S&bit(j) != 0 && int(s.Nodes[j-1].Term) > T {
								T = int(s.Nodes[j-1].Term)
							}
						}
						T++
						if T <= MAXT && L+1 <= MAXLOG {
							ns = *s
							for j := 1; j <= N; j++ {
								if V&bit(j) != 0 {
									m := &ns.Nodes[j-1]
									m.Term, m.Role, m.Match, m.Pending = uint8(T), RF, [MaxN]uint8{}, 0
								}
							}
							c := &ns.Nodes[i-1]
							c.Term, c.Role = uint8(T), RL
							c.Log[L] = mkEnt(T, KE, 0, 0)
							c.Len = uint8(L + 1)
							c.Match = [MaxN]uint8{}
							c.Match[i-1] = uint8(L + 1)
							c.Pending = uint8(L)
							viol := VNone
							if GhostES {
								if ns.Won&(1<<T) != 0 {
									viol = VElection
								}
								ns.Won |= 1 << T
							}
							if viol == VNone {
								// leader completeness: the winner's log extends every committed prefix
								for k := 0; k < N && viol == VNone; k++ {
									o := &s.Nodes[k]
									if int(o.Commit) > L {
										viol = VLeaderCompl
										break
									}
									for p := 0; p < int(o.Commit); p++ {
										if o.Log[p] != n.Log[p] {
											viol = VLeaderCompl
											break
										}
									}
								}
							}
							if InvMask&(1<<viol) == 0 {
								viol = VNone
							}
							emit(Action{Kind: AElect, I: uint8(i), X: uint8(T), Set: S}, &ns, viol)
						}
					}
					if V == 0 {
						break
					}
				}
			}
		}
		if n.Role == RL {
			if int(s.NV) < MAXVAL && L < MAXLOG { // propv
				ns = *s
				c := &ns.Nodes[i-1]
				c.Log[L] = mkEnt(term, KV, 0, int(s.NV)+1)
				c.Len++
				c.Match[i-1] = c.Len
				ns.NV++
				emit(Action{Kind: APropV, I: uint8(i), X: ns.NV}, &ns, VNone)
			}
			var pending bool
			switch Mode {
			case "fix": // guard-fix.md: pendingConfIndex > confApplied()
				pending = n.Pending > confApplied(n)
			default:
				pending = n.Pending > n.Applied
			}
			if int(s.NC) < MAXCONF && L < MAXLOG && !pending { // propc
				var ops []uint16
				if cfg.out == 0 { // joint: only an empty (leave) change is accepted; auto-leave proposes it
					for j := 1; j <= N; j++ {
						if cfg.inc&bit(j) == 0 {
							ops = append(ops, mkEnt(term, KC, OpAdd, j))
						}
					}
					for j := 1; j <= N; j++ {
						if cfg.inc&bit(j) != 0 && (j != i || RemSelf) && pc(cfg.inc) > 1 {
							ops = append(ops, mkEnt(term, KC, OpRem, j))
						}
					}
					if JOINT {
						for j := 1; j <= N; j++ {
							nw := cfg.inc ^ bit(j)
							if j != i && nw != 0 {
								ops = append(ops, mkEnt(term, KC, OpEnter, int(nw)))
							}
						}
					}
				}
				for _, e := range ops {
					ns = *s
					c := &ns.Nodes[i-1]
					c.Log[L] = e
					c.Len++
					c.Match[i-1] = c.Len
					c.Pending = c.Len
					ns.NC++
					emit(Action{Kind: APropC, I: uint8(i), Ent: e}, &ns, VNone)
				}
			}
			for j := 1; j <= N; j++ { // app: leader i to j, atomic request and response
				if j == i {
					continue
				}
				m := &s.Nodes[j-1]
				if int(m.Term) > term {
					continue
				}
				p := 0
				lm := int(m.Len)
				for p < lm && p < L && m.Log[p] == n.Log[p] {
					p++
				}
				if p < int(m.Commit) {
					continue
				}
				qmax := L
				if REDUCED && p+1 < qmax {
					qmax = p + 1
				}
				for q := p; q <= qmax; q++ {
					ns = *s
					d := &ns.Nodes[j-1]
					keep := q == p // lj[:q] == log[:q] and len(lj) >= q
					if !keep {
						d.Log = n.Log
						for x := q; x < MaxLog; x++ {
							d.Log[x] = 0
						}
						d.Len = uint8(q)
						d.PCommit = m.Commit
					}
					ncm := int(m.Commit)
					if mq := min(int(n.Commit), q); mq > ncm {
						ncm = mq
					}
					d.Term, d.Role, d.Commit, d.Match, d.Pending = uint8(term), RF, uint8(ncm), [MaxN]uint8{}, 0
					c := &ns.Nodes[i-1]
					if uint8(q) > c.Match[j-1] {
						c.Match[j-1] = uint8(q)
					}
					emit(Action{Kind: AApp, I: uint8(i), J: uint8(j), X: uint8(q)}, &ns, VNone)
				}
			}
			for Nn := L; Nn > int(n.Commit); Nn-- { // commit
				if eTerm(n.Log[Nn-1]) != term {
					continue
				}
				S := bit(i)
				for k := 1; k <= N; k++ {
					if int(n.Match[k-1]) >= Nn {
						S |= bit(k)
					}
				}
				if isq(cfg, S) {
					ns = *s
					ns.Nodes[i-1].Commit = uint8(Nn)
					emit(Action{Kind: ACommit, I: uint8(i), X: uint8(Nn)}, &ns, VNone)
					break
				}
			}
		}
		if n.Applied < n.Commit { // apply
			ns = *s
			c := &ns.Nodes[i-1]
			c.Applied++
			if !lagging || LagMask&bit(i) == 0 {
				c.CfgIdx = c.Applied
			}
			afterCfg(i, c)
			emit(Action{Kind: AApply, I: uint8(i), X: c.Applied}, &ns, VNone)
		}
		if lagging && LagMask&bit(i) != 0 && n.CfgIdx < n.Applied { // applyconf
			ns = *s
			c := &ns.Nodes[i-1]
			c.CfgIdx++
			afterCfg(i, c)
			emit(Action{Kind: AApplyConf, I: uint8(i), X: c.CfgIdx}, &ns, VNone)
		}
		if Mode == "crash" && n.PCommit < n.Commit { // crash: restart with the persisted commit
			ns = *s
			c := &ns.Nodes[i-1]
			c.Role, c.Commit, c.Applied, c.CfgIdx, c.Match, c.Pending = RF, n.PCommit, 0, 0, [MaxN]uint8{}, 0
			emit(Action{Kind: ACrash, I: uint8(i), X: n.PCommit}, &ns, VNone)
		}
		if ReadIdx && ReadSingletonBug && n.Role == RL && cfg.out == 0 && pc(cfg.inc) == 1 {
			// the pinned stepLeader: IsSingleton() answers at once with the commit index,
			// before committedEntryInCurrentTerm, whoever the voter is
			v := VNone
			for k := 0; k < N; k++ {
				if s.Nodes[k].Commit > n.Commit && InvMask&(1<<VRead) != 0 {
					v = VRead
				}
			}
			emit(Action{Kind: AReadSingle, I: uint8(i), X: n.Commit}, s, v)
		}
		if ReadIdx && n.Role == RL && s.RdNode == 0 && (ReadNoTermCheck || n.Commit > 0 && eTerm(n.Log[n.Commit-1]) == term) {
			// MsgReadIndex arrives at leader i (committedEntryInCurrentTerm holds)
			ns = *s
			ns.RdNode, ns.RdTerm, ns.RdIdx = uint8(i), n.Term, n.Commit
			for k := 0; k < N; k++ {
				if s.Nodes[k].Commit > ns.RdMax {
					ns.RdMax = s.Nodes[k].Commit
				}
			}
			emit(Action{Kind: AReadReq, I: uint8(i), X: n.Commit}, &ns, VNone)
		}
		if ReadIdx && s.RdNode == uint8(i) && n.Role == RL && n.Term == s.RdTerm {
			// confirmation: a quorum of i's current configuration answers a heartbeat of
			// RdTerm (every node of term <= RdTerm would)
			S := bit(i)
			for k := 1; k <= N; k++ {
				if s.Nodes[k-1].Term <= s.RdTerm {
					S |= bit(k)
				}
			}
			if isq(cfg, S) {
				ns = *s
				v := VNone
				if s.RdMax > s.RdIdx {
					v = VRead
				}
				if InvMask&(1<<v) == 0 {
					v = VNone
				}
				ns.RdNode, ns.RdTerm, ns.RdIdx, ns.RdMax = 0, 0, 0, 0
				emit(Action{Kind: AReadOk, I: uint8(i), X: s.RdIdx}, &ns, v)
			}
		}
	}
	if ReadIdx && s.RdNode != 0 { // the request is dropped (or answered and forgotten)
		ns = *s
		ns.RdNode, ns.RdTerm, ns.RdIdx, ns.RdMax = 0, 0, 0, 0
		emit(Action{Kind: AReadDrop}, &ns, VNone)
	}
}

// after_cfg: stepDownOnRemoval, auto-leave.
func afterCfg(i int, c *Node) {
	c2 := cfgAt(c, int(c.CfgIdx))
	if !NoStepDown && c.Role == RL && (c2.inc|c2.out)&bit(i) == 0 {
		c.Role, c.Match, c.Pending = RF, [MaxN]uint8{}, 0
		return
	}
	ap := c.Applied
	if guardCfg { // guard-fix.md: maybeAutoLeave compares confApplied() with pendingConfIndex
		ap = confApplied(c)
	}
	if JOINT && c.Role == RL && c2.out != 0 && ap >= c.Pending && int(c.Len) < MAXLOG {
		c.Log[c.Len] = mkEnt(int(c.Term), KC, OpLeave, 0)
		c.Len++
		c.Match[i-1] = c.Len
		c.Pending = c.Len
	}
}
