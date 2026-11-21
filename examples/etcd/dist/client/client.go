//go:build etcddist_sketch

// Package client is the program of a client machine of etcd_dist_safe (notes/etcd-dist-plan.md;
// DRAFT, a sketch: not built, not translated, kept out of every build by its build tag). One
// process runs one workload against the cluster's client endpoints, checks its property and
// panics if the check fails; the machine never crashes (Lean: Robust's stable list), so the
// workload keeps its history.
//
// Each workload is today's driver with its start removed: the driver's Main minus etcdstart's
// StartMembers/Serve/bridges/partitioner, the clients made of the endpoints it is given. The
// functions called below are the PROPOSED split of each driver into its start and its workload
// (stage D1 of the plan); none exists yet. Faults are the network's (the net extension's cuts,
// delays, refused dials) and the server machines' crashes, never the program's: no bridge, no
// CutPeer/MendPeer, no HardStop.
//
// Rules every checker follows (etcd-grove#24, the grpc model's errors): any non-OK gRPC error is
// an unknown outcome (the request may or may not have been applied), never "not applied"; a
// server stream's clean end (io.EOF, a closed watch channel) is never taken as complete (grpc-go's
// spurious EOF after a transparent retry, nonissues/grpc-transparent-retry-spurious-eof.md); and
// keepalive is never relied on for safety (the model accepts its options and does nothing).
package client

// Kind is a workload's kind (Lean: Workload's constructors, in this order).
type Kind int

const (
	KV           Kind = iota // txnlinfaultsN's workload: partition.Check, porcupine (txnlin's model)
	Watch                    // partition.MainWatch's workload: a watch from revision 1 and writers (etcdstart.Check)
	Cache                    // cache's workload: etcd's watch cache over the client (cachekv's check)
	Compact                  // compactwatch's rounds: Put, explicit Compact, latest and old Gets; watches
	PutGet                   // compacted's Put then Get
	Auth                     // authN's set-up, barrier, four principals and checks
	AuthLease                // authlease's lease rows of auth
	LeaseRead                // leaseN's Leases/TimeToLive reads at every member
	LeaseCatchup             // leasecatchup's grant, fillers and listing (no cut: the network's)
	LeaseExpiry              // leaseexpiryN's 2 s leases, polled until gone, listed once more
	Durable                  // restartN's check: acknowledged Puts all present, at version 1
)

// Workload is one client machine's workload and its parameters (Lean: Workload).
type Workload struct {
	Kind    Kind
	Clients int // KV: concurrent clients; Watch, Cache: writers; Durable: Puts
	Ops     int // KV: operations per client; Watch, Cache: Puts per writer
}

// Main runs w against the members' client endpoints eps (in the members' order: the workloads
// that pick a member, authN's principals, leaseN's per-member reads, use eps[i mod len(eps)]).
// Results are dropped: a failed check is a panic inside the workload.
func Main(w Workload, eps []string) {
	switch w.Kind {
	case KV:
		txnlinfaultsN.Run(eps, w.Clients, w.Ops) // PROPOSED: NewClients(eps) x clients; partition.Check; panic on Illegal
	case Watch:
		partition.RunWatch(eps, w.Clients, w.Ops) // PROPOSED: MainWatch minus the start and partitioner
	case Cache:
		cache.Run(eps, w.Clients, w.Ops) // PROPOSED
	case Compact:
		compactwatch.Run(eps) // PROPOSED
	case PutGet:
		compacted.Run(eps) // PROPOSED
	case Auth:
		authN.Run(eps) // PROPOSED: principal i through eps[i mod k]
	case AuthLease:
		authlease.Run(eps) // PROPOSED
	case LeaseRead:
		leaseN.Run(eps) // PROPOSED
	case LeaseCatchup:
		leasecatchup.Run(eps) // PROPOSED: grant via eps[k-1], fillers via eps[0], list at eps[k-1]
	case LeaseExpiry:
		leaseexpiryN.Run(eps) // PROPOSED
	case Durable:
		restartN.RunDurable(eps, w.Clients) // PROPOSED: Puts of the client's keys, then a linearizable
		// Range checked exactly but for the response's revision (other clients write too)
	}
}
