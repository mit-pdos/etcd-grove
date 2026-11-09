// Requirement snippets for etcd's apply thread and raft driver (batch 2d): durability across stops,
// restarts, crashes and snapshots, as a client sees it (K5, K6 of notes/specs-only/top.md).
package etcdserverapply

import (
	"context"

	clientv3 "go.etcd.io/etcd/client/v3"
)

// Member is how a program stops and starts one member of a running cluster on its data directory
// (2e's StartServer and HardStop; a crash is a kill of the process and a start on the same
// directory).
type Member interface {
	Stop()
	Crash()
	Start()
}

// REQ etcdserverapply/restart-continues: a write acknowledged before a member stops is seen after
// the member restarts on its data directory, whatever the member did meanwhile (snapshots,
// compactions of the raft log, a received snapshot): the history is the committed log's (histAt),
// and the restarted member continues it from its durable state.
// Users: examples/lib/etcdstart (StartServer, HardStop), Kubernetes' etcd upgrades (rolling
// restarts), etcd's integration tests (TestRestartMember).
// Assumes: cli reaches the cluster's members (any of them may answer); m is a member of it; no
// other client writes or deletes k, and k is put without a lease (so nothing else removes it).
// Specs: EtcdServer.run.spec (srvStopped), raftNode.stop.spec, applySnapshot.spec; 2e's
// memberStart_restart; W0's KV.PutTriple, KV.GetTriple, etcdLb_reach.
func ReqRestartContinues(ctx context.Context, cli *clientv3.Client, m Member, k, v string) {
	if _, err := cli.Put(ctx, k, v); err != nil {
		return
	}
	m.Stop()
	m.Start()
	resp, err := cli.Get(ctx, k)
	if err != nil {
		return
	}
	if len(resp.Kvs) != 1 || string(resp.Kvs[0].Value) != v {
		panic("restart-continues: acknowledged write lost across a restart")
	}
}

// REQ etcdserverapply/crash-keeps-answered: a write acknowledged to the client is durable on a
// quorum (each follower's WAL Save fires raft's readyEnter before it acknowledges; the leader
// commits only on a quorum): a crash of every member and a restart of all of them from their data
// directories loses no acknowledged write.
// Users: etcd's robustness tests (kill and restart), the model's absence of a crash transition.
// Assumes: ms are all the cluster's members; cli reaches them once restarted; no other client
// writes or deletes k, and k is put without a lease.
// Specs: raftNode.start.spec (the write before the follower's send), RestartNode (R1), 2e's
// memberStart_restart, the WAL's Save (2e).
func ReqCrashKeepsAnswered(ctx context.Context, cli *clientv3.Client, ms []Member, k, v string) {
	if _, err := cli.Put(ctx, k, v); err != nil {
		return
	}
	for _, m := range ms {
		m.Crash()
	}
	for _, m := range ms {
		m.Start()
	}
	resp, err := cli.Get(ctx, k)
	if err != nil {
		return
	}
	if len(resp.Kvs) != 1 || string(resp.Kvs[0].Value) != v {
		panic("crash-keeps-answered: acknowledged write lost across a crash")
	}
}

// REQ etcdserverapply/lease-expiry: a lease whose TTL passes is revoked by the leader at a commit
// at which it is live, its keys deleted in one revision (EnvStep.leaseExpire through envUpd); a
// client reading after the revocation sees none of its keys.
// Users: client/v3/concurrency (sessions), Kubernetes' events (leases).
// Assumes: the cluster's environment lets leases expire (EnvCfg.leaseExpiry); nobody keeps id alive;
// id is never granted again (no client asks for it by number), so no later key carries it.
// Specs: revokeExpiredLeases.spec, 2c's LeaseRevoke.spec, 3c's expiry channel.
func ReqLeaseExpiry(ctx context.Context, cli *clientv3.Client, id clientv3.LeaseID, k string) {
	ttl, err := cli.TimeToLive(ctx, id)
	if err != nil || ttl.TTL != -1 {
		return // not expired yet (or unknown)
	}
	resp, err := cli.Get(ctx, k)
	if err != nil {
		return
	}
	for _, kv := range resp.Kvs {
		if clientv3.LeaseID(kv.Lease) == id {
			panic("lease-expiry: a key of a revoked lease survives")
		}
	}
}
