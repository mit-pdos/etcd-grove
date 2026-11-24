// Package dist runs etcd_safe's deployments for real (notes/etcd-dist-plan.md, stage D1)
// over examples/lib/robust: every member a process of server.Main on a
// machine of its own, every workload a process of client.Main on a client machine of its own, all
// started at once and connected by TCP through examples/lib/robust's network; meanwhile the environment
// makes the faults the theorem's executions allow: members crash for real (SIGKILL, then their
// files synced, or their disk losing power where the device mapper is available) and restart with
// the same program and configuration, and the network partitions (both ways or one way) and
// delays, loses, duplicates and reorders packets (robust.NetNemesis, in the namespace mode). The
// programs have no fault of their own.
//
// A run passes if no process panics (a client's failed check, or a member's panic) and no member
// exits on its own, and every client is done by the deadline. A client that ends without a check
// (its start failed, a watch ended, a lease was never seen gone) is not a failure: the theorem
// says nothing more; the test reports how many checks ran.
//
// The deployments are random among the well-formed ones (WellFormed, the Lean predicate's Go
// mirror) of a fixed member count: a random server configuration and a random compatible mix of
// workloads.
package dist

import (
	"fmt"
	"math/rand/v2"
	"strconv"
	"strings"
	"time"

	"go.uber.org/zap"

	"go.etcd.io/etcd/client/pkg/v3/types"
	"go.etcd.io/etcd/server/v3/etcdserver/api/membership"

	"github.com/mit-pdos/etcd-grove/examples/etcd/dist/client"
	"github.com/mit-pdos/etcd-grove/examples/etcd/dist/server"
)

// Member is a member of a deployment (Lean: Member).
type Member struct {
	Name   string
	Peer   string
	Client string
}

// ServerCfg is the server configuration, the same at every member (Lean: ServerCfg).
type ServerCfg struct {
	CompactorMode string // server.CompactorRevision or CompactorPeriodic
	Retention     int64  // 0: no auto-compactor
	SnapCount     uint64
	CatchUp       uint64
	Auth          bool
}

// Deployment is a cluster and its client machines' workloads (Lean: Deployment).
type Deployment struct {
	Members   []Member
	Token     string
	Cfg       ServerCfg
	Workloads []client.Workload
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

// ServerConfig is member i's configuration (cmd/server's input).
func (d Deployment) ServerConfig(i int) server.Config {
	var cl []server.Peer
	for _, m := range d.Members {
		cl = append(cl, server.Peer{Name: m.Name, Addr: m.Peer})
	}
	m := d.Members[i]
	return server.Config{Name: m.Name, Peer: m.Peer, Client: m.Client, Cluster: cl, Token: d.Token,
		CompactorMode: d.Cfg.CompactorMode, Retention: d.Cfg.Retention, SnapCount: d.Cfg.SnapCount,
		CatchUp: d.Cfg.CatchUp, Auth: d.Cfg.Auth}
}

// Endpoints are the members' client addresses, in the members' order (the clients' eps).
func (d Deployment) Endpoints() []string {
	var eps []string
	for _, m := range d.Members {
		eps = append(eps, m.Client)
	}
	return eps
}

// The workload predicates (Lean: Workload.writesKeys, needsSoleWriter, alone, needsAuth,
// grantsLeases, needsNoExpiry).
func writesKeys(k client.Kind) bool {
	return k != client.LeaseRead && k != client.LeaseCatchup && k != client.LeaseExpiry
}
func needsSoleWriter(k client.Kind) bool {
	return k == client.KV || k == client.Watch || k == client.Cache || k == client.Auth || k == client.AuthLease
}
func alone(k client.Kind) bool     { return k == client.Auth || k == client.AuthLease }
func needsAuth(k client.Kind) bool { return alone(k) }
func grantsLeases(k client.Kind) bool {
	return k == client.AuthLease || k == client.LeaseCatchup || k == client.LeaseExpiry
}
func needsNoExpiry(k client.Kind) bool { return k == client.AuthLease || k == client.LeaseCatchup }

// compatible is Lean's Compatible.
func compatible(ws []client.Workload) bool {
	seen := map[client.Kind]bool{}
	hasExpiry, hasNoExpiry := false, false
	for _, w := range ws {
		if seen[w.Kind] {
			return false
		}
		seen[w.Kind] = true
		if alone(w.Kind) && len(ws) != 1 {
			return false
		}
		if w.Kind == client.LeaseExpiry {
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

// addrOk is the net extension's addrOk (kvnet.AddrOk's, copied: kvnet is a module of its own): a
// canonical a.b.c.d:p, the first octet 1-223, the port outside Linux's ephemeral range.
func addrOk(a string) bool {
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
		if err != nil || strconv.Itoa(n) != s {
			return false
		}
		v[i] = n
	}
	return 1 <= v[0] && v[0] < 224 && v[1] <= 255 && v[2] <= 255 && v[3] <= 255 &&
		1 <= v[4] && v[4] <= 65535 && (v[4] < 32768 || 60999 < v[4])
}

// memberIDs are the member ids etcd computes for d's cluster (from the peer URLs and the token, as
// bootstrap does), in the members' order.
func memberIDs(d Deployment) ([]uint64, error) {
	urls := types.URLsMap{}
	for _, m := range d.Members {
		u, err := types.NewURLs([]string{"http://" + m.Peer})
		if err != nil {
			return nil, err
		}
		urls[m.Name] = u
	}
	cl, err := membership.NewClusterFromURLsMap(zap.NewNop(), d.Token, urls)
	if err != nil {
		return nil, err
	}
	var ids []uint64
	for _, m := range d.Members {
		ids = append(ids, uint64(cl.MemberByName(m.Name).ID))
	}
	return ids, nil
}

// idsOk is WellFormed's condition 3: the ids' 16 low bits distinct and nonzero, and, if a workload
// grants leases, their 15 low bits distinct (leaseIdsApart).
func idsOk(d Deployment) bool {
	ids, err := memberIDs(d)
	if err != nil {
		return false
	}
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

// WellFormed is Lean's Deployment.WellFormed, with the bounds of the workloads (Workload.BoundsOk)
// and of the server configuration (ServerCfg.Supported).
func WellFormed(d Deployment) error {
	if len(d.Members) == 0 {
		return fmt.Errorf("no member")
	}
	names, addrs := map[string]bool{}, map[string]bool{}
	for _, m := range d.Members {
		if !nameOk(m.Name) || names[m.Name] {
			return fmt.Errorf("member name %q", m.Name)
		}
		names[m.Name] = true
		for _, a := range []string{m.Peer, m.Client} {
			if !addrOk(a) || addrs[a] {
				return fmt.Errorf("address %q", a)
			}
			addrs[a] = true
		}
	}
	if !idsOk(d) {
		return fmt.Errorf("member ids")
	}
	if d.Token == "" {
		return fmt.Errorf("empty token")
	}
	c := d.Cfg
	if c.SnapCount < 1 || c.CatchUp < 1 {
		return fmt.Errorf("snapshot settings")
	}
	if c.Retention != 0 && !(c.CompactorMode == server.CompactorRevision && c.Retention >= 1 ||
		c.CompactorMode == server.CompactorPeriodic && c.Retention >= 10) {
		return fmt.Errorf("compactor")
	}
	if !compatible(d.Workloads) {
		return fmt.Errorf("workloads not compatible")
	}
	for _, w := range d.Workloads {
		switch w.Kind {
		case client.KV, client.Watch, client.Cache:
			if w.Clients < 0 || w.Ops < 0 || w.Clients >= 1<<31 {
				return fmt.Errorf("workload bounds")
			}
		case client.Durable:
			if w.Clients < 0 || w.Clients > client.MaxDurable {
				return fmt.Errorf("durable bound")
			}
		}
		if needsAuth(w.Kind) && !c.Auth {
			return fmt.Errorf("%v needs the token provider", w.Kind)
		}
		if w.Kind == client.Compact && c.Retention != 0 && c.CompactorMode == server.CompactorPeriodic {
			return fmt.Errorf("compact under the periodic compactor")
		}
		if w.Kind == client.LeaseExpiry && c.Auth {
			return fmt.Errorf("leaseExpiry with the token provider")
		}
	}
	return nil
}

// Sizes are the workloads' sizes in a random deployment.
type Sizes struct {
	KVClients, KVOps   int
	Writers, WriterOps int
	DurablePuts        int
}

// ShortSizes and FullSizes are the short mode's and the full test's.
var (
	ShortSizes = Sizes{KVClients: 3, KVOps: 25, Writers: 3, WriterOps: 15, DurablePuts: 40}
	FullSizes  = Sizes{KVClients: 4, KVOps: 200, Writers: 4, WriterOps: 200, DurablePuts: 256}
)

// pick is a random element of xs.
func pick[T any](xs ...T) T { return xs[rand.IntN(len(xs))] }

// randomWorkloads is a random compatible mix: one workload that reads revisions as its own (kv,
// watch or cache) or some of compact, putget and durable, or auth or authLease alone; with the
// lease workloads beside the first two kinds, at random (never leaseExpiry beside leaseCatchup).
func randomWorkloads(sz Sizes) []client.Workload {
	var ws []client.Workload
	switch rand.IntN(8) {
	case 0, 1:
		ws = append(ws, client.Workload{Kind: client.KV, Clients: sz.KVClients, Ops: sz.KVOps})
	case 2:
		ws = append(ws, client.Workload{Kind: client.Watch, Clients: sz.Writers, Ops: sz.WriterOps})
	case 3:
		ws = append(ws, client.Workload{Kind: client.Cache, Clients: sz.Writers, Ops: sz.WriterOps})
	case 4, 5:
		for len(ws) == 0 {
			if rand.IntN(2) == 0 {
				ws = append(ws, client.Workload{Kind: client.Compact})
			}
			if rand.IntN(2) == 0 {
				ws = append(ws, client.Workload{Kind: client.PutGet})
			}
			if rand.IntN(2) == 0 {
				ws = append(ws, client.Workload{Kind: client.Durable, Clients: sz.DurablePuts})
			}
		}
	case 6:
		return []client.Workload{{Kind: client.Auth}}
	case 7:
		return []client.Workload{{Kind: client.AuthLease}}
	}
	if rand.IntN(2) == 0 {
		ws = append(ws, client.Workload{Kind: client.LeaseRead})
	}
	switch rand.IntN(3) {
	case 0:
		ws = append(ws, client.Workload{Kind: client.LeaseCatchup})
	case 1:
		ws = append(ws, client.Workload{Kind: client.LeaseExpiry})
	}
	return ws
}

// randomCfg is a random supported server configuration for the workloads ws: the token provider
// if a workload needs it, and otherwise at random but never beside leaseExpiry; the compactor off,
// in revision mode or in periodic mode (not beside compact); snapshots often or rarely.
func randomCfg(ws []client.Workload) ServerCfg {
	var c ServerCfg
	auth, compact, expiry := false, false, false
	for _, w := range ws {
		auth = auth || needsAuth(w.Kind)
		compact = compact || w.Kind == client.Compact
		expiry = expiry || w.Kind == client.LeaseExpiry
	}
	c.Auth = auth || (!expiry && rand.IntN(4) == 0)
	switch rand.IntN(4) {
	case 1:
		c.CompactorMode, c.Retention = server.CompactorRevision, pick[int64](1, 10, 1000)
	case 2:
		if !compact {
			c.CompactorMode, c.Retention = server.CompactorPeriodic, pick(int64(10*time.Millisecond), int64(time.Second))
		}
	}
	c.SnapCount = pick[uint64](1, 10, 100, 10000)
	c.CatchUp = pick[uint64](1, 5, 100, 1<<48)
	return c
}

// RandomDeployment is a random well-formed deployment of k members at the addresses addr(i)
// (peer and client), its names and token tagged by tag: a random configuration, a random
// compatible mix of workloads of the sizes sz, and the first token tag-<n> whose member ids pass
// WellFormed's condition 3.
func RandomDeployment(tag string, k int, addr func(i int) (peer, client string), sz Sizes) (Deployment, error) {
	ws := randomWorkloads(sz)
	d := Deployment{Cfg: randomCfg(ws), Workloads: ws}
	for i := 0; i < k; i++ {
		p, c := addr(i)
		d.Members = append(d.Members, Member{Name: fmt.Sprintf("%s-%d", tag, i), Peer: p, Client: c})
	}
	for n := 0; n < 1000; n++ {
		d.Token = fmt.Sprintf("%s-%d", tag, n)
		if idsOk(d) {
			break
		}
	}
	return d, WellFormed(d)
}
