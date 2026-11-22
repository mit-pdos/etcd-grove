// Package client is the program of a client machine of etcd_dist_safe (notes/etcd-dist-plan.md,
// §2): one process runs one workload against the cluster's client endpoints, checks its property
// and panics if the check fails; the machine never crashes (Lean: Robust's stable list), so the
// workload keeps its history.
//
// Each workload is today's driver with its start removed: the driver's Main minus etcdstart's
// StartMembers/Serve, the bridges, the partitioner, CutPeer/MendPeer and HardStop, its clients made
// of the endpoints it is given. Faults are the network's (cuts, delays, refused dials) and the
// server machines' crashes, never the program's. Where a driver's helpers are exported and take
// clients, they are called (txnlin.Apply/Gen/Model, etcdstart.Writer/Collect/Check, auth.SetUp/
// Work/CheckHistory, ...); where its workload is inline in Main or its helpers are unexported, the
// code is copied here, each copy saying which driver function it is (the list: the plan's §2,
// "Copies").
//
// Rules every checker follows (etcd-grove#24, the grpc model's errors), audited per workload in the
// plan (§2, "The error rules, audited"): any non-OK gRPC error is an unknown outcome (the request
// may or may not have been applied, now or later), never "not applied"; a server stream's clean end
// (io.EOF, a closed watch channel) is never taken as complete (grpc-go's spurious EOF after a
// transparent retry, nonissues/grpc-transparent-retry-spurious-eof.md); and keepalive is never
// relied on for safety (the model accepts its options and does nothing).
//
// Keys (Q1, review F1): each workload writes only under its own prefix, and no two workloads write
// one key: kv's keys are txnlin's (k0, k1, k2; its List ranges over [k, l)), auth's and authLease's
// are package auth's (a/..., c/..., z/...: they run alone), and the others' prefixes below start
// with none of a, c/, k, z. A workload whose check reads the store's revisions as its own (kv,
// watch, cache, auth, authLease) runs beside none that writes keys (Lean: Compatible).
//
// Clients on separate machines (the plan's §2, the user's decision; stage D8): a workload with
// several clients (kv, watch, cache, auth) runs each client on a machine of its own, which serves
// the orchestrator's calls through examples/lib/remote (NodeMain, nodes.go), and the orchestrating
// part (generating the operations, recording the history, the check) on this machine.
package client

import (
	"context"
	"time"

	"go.uber.org/zap"

	clientv3 "go.etcd.io/etcd/client/v3"

	"github.com/mit-pdos/etcd-grove/examples/etcd/dist/env"
	"github.com/mit-pdos/etcd-grove/examples/lib/etcdstart"
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

var kindNames = []string{"kv", "watch", "cache", "compact", "putget", "auth", "authLease",
	"leaseRead", "leaseCatchup", "leaseExpiry", "durable"}

// String is the kind's name (the Lean constructor's).
func (k Kind) String() string {
	if k < 0 || int(k) >= len(kindNames) {
		return "unknown"
	}
	return kindNames[k]
}

// Workload is one client machine's workload and its parameters (Lean: Workload).
type Workload struct {
	Kind    Kind
	Clients int // KV: concurrent clients; Watch, Cache: writers; Durable: Puts (at most MaxDurable)
	Ops     int // KV: operations per client; Watch, Cache: Puts per writer
}

// Result is how a workload ended without a panic: Checked if its checks ran (and passed: a failed
// check is a panic), otherwise Why names the step that ended it (an error, a stream that ended, a
// lease never seen gone): the specs allow every step to fail.
type Result struct {
	Checked bool
	Why     string
}

// checked and ended are a workload's results.
func checked() Result         { return Result{Checked: true} }
func ended(why string) Result { return Result{Why: why} }
func (r Result) String() string {
	if r.Checked {
		return "checked"
	}
	return "ended: " + r.Why
}

// The prefixes of the workloads that write keys under a prefix of their own (see the package doc).
const (
	watchPrefix   = "wk/"
	cachePrefix   = "ck/"
	compactPrefix = "cw/"
	putgetPrefix  = "pg/"
	durablePrefix = "du/"
)

// newClient connects a client of the endpoints eps (etcdstart.NewClients: the examples' timeouts
// and etcd's default retries).
func newClient(eps []string) (*clientv3.Client, error) {
	return etcdstart.NewClients(eps, zap.NewNop())
}

// How many times, and how far apart, AwaitCluster tries its read.
const (
	readyTries = 60
	readyPause = 500 * time.Millisecond
)

// AwaitCluster waits until a linearizable read through a client of eps returns (a liveness wait,
// as restartN's wait for a leader: the members may still be starting, or down): a read writes
// nothing, so trying it again is safe, where a workload's first write (auth's set-up) cannot be
// retried after an unknown outcome. It reports whether one returned.
func AwaitCluster(eps []string) bool {
	cli, err := newClient(eps)
	if err != nil {
		return false
	}
	defer cli.Close()
	for t := 0; t < readyTries; t++ {
		ctx, cancel := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)
		_, err := cli.Get(ctx, "dist/ready")
		cancel()
		if err == nil {
			return true
		}
		time.Sleep(readyPause)
	}
	return false
}

// Main runs w with no observer of its set-up (MainReady).
func Main(w Workload, eps []string, nodes []string) Result {
	return MainReady(w, eps, nodes, func() {})
}

// hasSetUp says whether a workload of kind k has a set-up: steps before its checks whose unknown
// outcome cannot be redone (auth's users and AuthEnable, authLease's leases, leaseCatchup's first
// lease) or that must precede the writes (the watch and the cache opened before any write), or that
// wait for its client machines (kv, watch, cache, auth).
func hasSetUp(k Kind) bool {
	return k == KV || k == Watch || k == Cache || k == Auth || k == AuthLease || k == LeaseCatchup
}

// MainReady runs w against the members' client endpoints eps (in the members' order: the workloads
// that pick a member use eps[i mod len(eps)]), with its client machines nodes (NodeCount(w) of
// them: nodes.go), after clearing the proxy variables as the server
// does (review F8). A failed check is a panic inside the workload.
//
// ready is called once the workload's set-up is done (at once, after the cluster's first read, for
// a workload with none), or not at all if the workload ends before: the test may hold its faults
// until then (examples/etcd/dist (its test)). It is an observer only: nothing the workload does
// depends on it.
func MainReady(w Workload, eps []string, nodes []string, ready func()) Result {
	env.ClearProxy()
	if len(eps) == 0 {
		return ended("no endpoint")
	}
	if len(nodes) != NodeCount(w) {
		return ended("not one client machine per client")
	}
	if !AwaitCluster(eps) {
		return ended("the cluster never answered a read")
	}
	if !hasSetUp(w.Kind) {
		ready()
	}
	switch w.Kind {
	case KV:
		return RunKV(nodes, w.Ops, ready)
	case Watch:
		return RunWatch(eps, nodes, w.Ops, ready)
	case Cache:
		return RunCache(eps, nodes, w.Ops, ready)
	case Compact:
		return RunCompact(eps)
	case PutGet:
		return RunPutGet(eps)
	case Auth:
		return RunAuth(eps, nodes, ready)
	case AuthLease:
		return RunAuthLease(eps, ready)
	case LeaseRead:
		return RunLeaseRead(eps)
	case LeaseCatchup:
		return RunLeaseCatchup(eps, ready)
	case LeaseExpiry:
		return RunLeaseExpiry(eps)
	case Durable:
		return RunDurable(eps, w.Clients)
	}
	return ended("unknown workload")
}

// Args is a client machine's configuration, as cmd/client reads it: its workload, the members'
// client endpoints, in the members' order, and the workload's client machines' addresses
// (NodeCount(W) of them, client c's at Nodes[c]). On the workload's orchestrator machine
// (MainReady) IsNode is false; on its client machine c (NodeMain, at Nodes[c]) IsNode is true and
// Node is c.
type Args struct {
	W      Workload
	Eps    []string
	Nodes  []string
	IsNode bool
	Node   int
}
