// Package deployment is etcd_safe's deployment (notes/etcd-dist-plan.md, §11.2): the cluster, its
// server configuration and its workloads with their client machines' addresses (Lean: Deployment,
// in Proof/.../examples/etcd/dist/TopLevelDefs.lean), and WellFormed, the check every machine's
// program makes first (Lean: Deployment.WellFormed). Every machine receives the whole deployment and
// its own index (server.MainDeployment, client.MainDeployment, client.NodeDeployment) and returns at
// once if WellFormed fails, so that the Lean statement needs no premise about the deployment.
package deployment

import (
	"fmt"
	"strconv"
	"strings"

	"go.etcd.io/etcd/client/pkg/v3/types"
	"go.etcd.io/etcd/server/v3/etcdserver/api/membership"
)

// Kind is a workload's kind (Lean: Workload's constructors, in this order).
type Kind int

const (
	KV           Kind = iota // txnlinfaultsN's workload: concurrent clients, porcupine (txnlin's model)
	Watch                    // partition.MainWatch's: a watch from revision 1 and writers (etcdstart.Check)
	Cache                    // cache's: etcd's watch cache over the client (cachekv's checks)
	Compact                  // compactwatch's rounds: Put, explicit Compact, latest and old Gets; watches
	PutGet                   // compacted's Put then Get, in rounds
	Auth                     // authN's set-up, barriers, four principals and checks
	AuthLease                // authlease's lease rows of auth
	LeaseRead                // leaseN's Leases/TimeToLive reads at every member
	LeaseCatchup             // leasecatchup's grant, fillers and listing (no cut: the network's)
	LeaseExpiry              // leaseexpiryN's shortest leases, polled until gone, listed once more
	Durable                  // restartN's check over gRPC: acknowledged Puts present, at version 1
)

// kindNames are the kinds' names, in the kinds' order (a function, not a package variable: the
// package has no state to initialize).
func kindNames() []string {
	return []string{"kv", "watch", "cache", "compact", "putget", "auth", "authLease",
		"leaseRead", "leaseCatchup", "leaseExpiry", "durable"}
}

// String is the kind's name (the Lean constructor's).
func (k Kind) String() string {
	if k < 0 || int(k) >= len(kindNames()) {
		return "unknown"
	}
	return kindNames()[k]
}

// Workload is one workload and its parameters (Lean: Workload; a kind without parameters in Lean
// ignores Clients and Ops).
type Workload struct {
	Kind    Kind
	Clients int // KV: concurrent clients; Watch, Cache: writers; Durable: Puts (at most MaxDurable)
	Ops     int // KV: operations per client; Watch, Cache: Puts per writer
}

// MaxDurable bounds the durable workload's Puts (restartN's keys: one byte after the prefix).
const MaxDurable = 256

// AuthPrincipals is the auth workload's client machines: one per principal, len(auth.Principals())
// (examples/etcd/auth; checked by examples/etcd/dist's TestNodeCount).
const AuthPrincipals = 4

// NodeCount is how many client machines a workload has (Lean: Workload.nodeCount; 0: it runs on
// its orchestrator machine alone).
func NodeCount(w Workload) int {
	switch w.Kind {
	case KV, Watch, Cache:
		return w.Clients
	case Auth:
		return AuthPrincipals
	}
	return 0
}

// The auto-compactor's modes (etcd's --auto-compaction-mode, v3compactor.ModeRevision and
// ModePeriodic).
const (
	CompactorRevision = "revision"
	CompactorPeriodic = "periodic"
)

// Member is a member of a deployment (Lean: Member).
type Member struct {
	Name   string
	Peer   string
	Client string
}

// ServerCfg is the server configuration, the same at every member (Lean: ServerCfg; its compactor
// is off when Retention is 0, otherwise CompactorMode's with Retention).
type ServerCfg struct {
	CompactorMode string // CompactorRevision or CompactorPeriodic
	Retention     int64  // revisions (revision mode) or nanoseconds (periodic); 0: no auto-compactor
	SnapCount     uint64
	CatchUp       uint64
	Auth          bool
}

// Deployment is a cluster and its workloads (Lean: Deployment): the members, in the initial
// cluster's order, the token, the server configuration, the workloads (each run by an orchestrator
// machine), and, per workload, its client machines' addresses (Nodes[j], NodeCount(Workloads[j])
// of them).
type Deployment struct {
	Members   []Member
	Token     string
	Cfg       ServerCfg
	Workloads []Workload
	Nodes     [][]string
}

// String describes d for the logs.
func (d Deployment) String() string {
	var ws []string
	for _, w := range d.Workloads {
		s := w.Kind.String()
		if w.Clients != 0 {
			s += fmt.Sprintf("(%d,%d)", w.Clients, w.Ops)
		}
		ws = append(ws, s)
	}
	comp := "off"
	if d.Cfg.Retention != 0 {
		comp = d.Cfg.CompactorMode + " " + strconv.FormatInt(d.Cfg.Retention, 10)
	}
	return fmt.Sprintf("%d members, compactor %s, snapshots %d/%d, auth %v; workloads %s",
		len(d.Members), comp, d.Cfg.SnapCount, d.Cfg.CatchUp, d.Cfg.Auth, strings.Join(ws, " "))
}

// Endpoints are the members' client addresses, in the members' order (the clients' eps).
func (d Deployment) Endpoints() []string {
	var eps []string
	for _, m := range d.Members {
		eps = append(eps, m.Client)
	}
	return eps
}

// Node is the n-th client machine of d (Lean: Deployment.nodeList's n-th entry: in the workloads'
// order, then by index within the workload): its workload's index j, its index c among the
// workload's client machines, and its address d.Nodes[j][c]; ok is false if d has no n-th client
// machine.
func (d Deployment) Node(n int) (j int, c int, ok bool) {
	if n < 0 {
		return 0, 0, false
	}
	for j := 0; j < len(d.Workloads) && j < len(d.Nodes); j++ {
		if n < len(d.Nodes[j]) {
			return j, n, true
		}
		n -= len(d.Nodes[j])
	}
	return 0, 0, false
}

// The workload predicates (Lean: Workload.writesKeys, needsSoleWriter, alone, needsAuth,
// grantsLeases, needsNoExpiry).
func writesKeys(k Kind) bool {
	return k != LeaseRead && k != LeaseCatchup && k != LeaseExpiry
}
func needsSoleWriter(k Kind) bool {
	return k == KV || k == Watch || k == Cache || k == Auth || k == AuthLease
}
func alone(k Kind) bool { return k == Auth || k == AuthLease }

// NeedsAuth says whether a workload of kind k needs the simple token provider (Lean:
// Workload.needsAuth).
func NeedsAuth(k Kind) bool { return alone(k) }
func grantsLeases(k Kind) bool {
	return k == AuthLease || k == LeaseCatchup || k == LeaseExpiry
}
func needsNoExpiry(k Kind) bool { return k == AuthLease || k == LeaseCatchup }

// compatible is Lean's Compatible (the kinds known: WellFormed checks them first).
func compatible(ws []Workload) bool {
	seen := map[Kind]bool{}
	hasExpiry, hasNoExpiry := false, false
	for _, w := range ws {
		if seen[w.Kind] {
			return false
		}
		seen[w.Kind] = true
		if alone(w.Kind) && len(ws) != 1 {
			return false
		}
		if w.Kind == LeaseExpiry {
			hasExpiry = true
		}
		if needsNoExpiry(w.Kind) {
			hasNoExpiry = true
		}
	}
	for i, w := range ws {
		if !needsSoleWriter(w.Kind) {
			continue
		}
		for j, x := range ws {
			if i != j && writesKeys(x.Kind) {
				return false
			}
		}
	}
	return !(hasExpiry && hasNoExpiry)
}

// boundsOk is Lean's Workload.BoundsOk (Lean's parameters are naturals: none negative here).
func boundsOk(w Workload) bool {
	c, o := w.Clients, w.Ops
	switch w.Kind {
	case KV:
		return 0 <= c && c < 1<<31 && 0 <= o && (c == 0 || o <= (1<<60-1)/c)
	case Watch, Cache:
		return 0 <= c && c < 1<<31 && 0 <= o && (c == 0 || o <= (1<<62-1)/c)
	case Durable:
		return 0 <= c && c <= MaxDurable
	}
	return true
}

// nameOk is Lean's nameOk: nonempty, ASCII letters, digits and '-'.
func nameOk(n string) bool {
	if n == "" {
		return false
	}
	for _, c := range []byte(n) {
		if !('0' <= c && c <= '9' || 'A' <= c && c <= 'Z' || 'a' <= c && c <= 'z' || c == '-') {
			return false
		}
	}
	return true
}

// AddrOk is the net extension's addrOk (Lean: Net.addrOk; kvnet.AddrOk's, copied: kvnet is a
// module of its own): a canonical a.b.c.d:p, the first octet 1-223, the port 1-65535 outside
// Linux's ephemeral range.
func AddrOk(a string) bool {
	host, port, ok := strings.Cut(a, ":")
	if !ok {
		return false
	}
	octs := strings.Split(host, ".")
	if len(octs) != 4 {
		return false
	}
	var v [5]int
	for i, s := range append(octs, port) {
		n, err := strconv.Atoi(s)
		// n < 0: Atoi takes a sign, and "-1" is Itoa's own spelling of -1
		if err != nil || n < 0 || strconv.Itoa(n) != s {
			return false
		}
		v[i] = n
	}
	return 1 <= v[0] && v[0] < 224 && v[1] <= 255 && v[2] <= 255 && v[3] <= 255 &&
		1 <= v[4] && v[4] <= 65535 && (v[4] < 32768 || 60999 < v[4])
}

// memberIDs are the member ids etcd computes for d's cluster (Lean: Deployment.ids, memberId):
// membership.NewMember's, from the member's one peer URL as server.Config builds it (http://Peer)
// and the token, as bootstrap does; in the members' order.
func memberIDs(d Deployment) []uint64 {
	var ids []uint64
	for _, m := range d.Members {
		u := types.URLs{{Scheme: "http", Host: m.Peer}}
		ids = append(ids, uint64(membership.NewMember(m.Name, u, d.Token, nil).ID))
	}
	return ids
}

// IdsOk is WellFormed's condition 3: the member ids' 16 low bits distinct and nonzero, and, if a
// workload grants leases, their 15 low bits distinct (Lean: leaseIdsApart).
func IdsOk(d Deployment) bool {
	ids := memberIDs(d)
	grants := false
	for _, w := range d.Workloads {
		grants = grants || grantsLeases(w.Kind)
	}
	low16, low15 := map[uint64]bool{}, map[uint64]bool{}
	for _, id := range ids {
		a, b := id&0xffff, id&0x7fff
		if a == 0 || low16[a] || (grants && low15[b]) {
			return false
		}
		low16[a], low15[b] = true, true
	}
	return true
}

// WellFormed is Lean's Deployment.WellFormed (clause by clause, numbered as there), with the
// bounds of the workloads (Workload.BoundsOk) and of the server configuration (ServerCfg.Supported):
// nil if d is well formed, otherwise the first clause it fails. (Its messages format a kind as
// w.Kind.String() under %s, or int(w.Kind) under %d: fmt calls no method of a basic-typed argument,
// which the proof's model of fmt needs.)
func WellFormed(d Deployment) error {
	// 1. a member; the names valid and distinct
	if len(d.Members) == 0 {
		return fmt.Errorf("no member")
	}
	names := map[string]bool{}
	for _, m := range d.Members {
		if !nameOk(m.Name) || names[m.Name] {
			return fmt.Errorf("member name %q", m.Name)
		}
		names[m.Name] = true
	}
	// 5 (first): every workload of a kind Lean has (Workload's constructors), within its bounds
	for _, w := range d.Workloads {
		if w.Kind < 0 || int(w.Kind) >= len(kindNames()) {
			return fmt.Errorf("unknown workload kind %d", int(w.Kind))
		}
		if !boundsOk(w) {
			return fmt.Errorf("%s: bounds", w.Kind.String())
		}
	}
	// 2. every address valid (Deployment.addrs: the members' peer and client addresses, then the
	// client machines'), all distinct; each workload has its NodeCount client machines
	if len(d.Nodes) != len(d.Workloads) {
		return fmt.Errorf("client machines: %d lists for %d workloads", len(d.Nodes), len(d.Workloads))
	}
	addrs := map[string]bool{}
	addr := func(a string) error {
		if !AddrOk(a) || addrs[a] {
			return fmt.Errorf("address %q", a)
		}
		addrs[a] = true
		return nil
	}
	for _, m := range d.Members {
		if err := addr(m.Peer); err != nil {
			return err
		}
		if err := addr(m.Client); err != nil {
			return err
		}
	}
	for j, w := range d.Workloads {
		if len(d.Nodes[j]) != NodeCount(w) {
			return fmt.Errorf("%s: %d client machines, not %d", w.Kind.String(), len(d.Nodes[j]), NodeCount(w))
		}
		for _, a := range d.Nodes[j] {
			if err := addr(a); err != nil {
				return err
			}
		}
	}
	// 3. the member ids
	if !IdsOk(d) {
		return fmt.Errorf("member ids")
	}
	// 4. the token; the server configuration supported
	if d.Token == "" {
		return fmt.Errorf("empty token")
	}
	c := d.Cfg
	if c.SnapCount < 1 || c.CatchUp < 1 {
		return fmt.Errorf("snapshot settings")
	}
	if c.Retention != 0 && !(c.CompactorMode == CompactorRevision && c.Retention >= 1 ||
		c.CompactorMode == CompactorPeriodic && c.Retention >= 10) {
		return fmt.Errorf("compactor")
	}
	// 5. compatible; the token provider where needed; no compact under the periodic compactor;
	// no leaseExpiry beside the token provider
	if !compatible(d.Workloads) {
		return fmt.Errorf("workloads not compatible")
	}
	for _, w := range d.Workloads {
		if NeedsAuth(w.Kind) && !c.Auth {
			return fmt.Errorf("%s needs the token provider", w.Kind.String())
		}
		if w.Kind == Compact && c.Retention != 0 && c.CompactorMode == CompactorPeriodic {
			return fmt.Errorf("compact under the periodic compactor")
		}
		if w.Kind == LeaseExpiry && c.Auth {
			return fmt.Errorf("leaseExpiry with the token provider")
		}
	}
	return nil
}
