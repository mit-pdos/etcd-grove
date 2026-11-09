package raftnode

import (
	"go.etcd.io/raft/v3"
)

// config is etcd's raftConfig (bootstrap.go:580): CheckQuorum on, PreVote as configured, Applied 0.
func config(id uint64, s raft.Storage, preVote bool) *raft.Config {
	return &raft.Config{
		ID:              id,
		ElectionTick:    10,
		HeartbeatTick:   1,
		Storage:         s,
		MaxSizePerMsg:   1 << 20,
		MaxInflightMsgs: 512,
		CheckQuorum:     true,
		PreVote:         preVote,
	}
}

// REQ raftnode/start-fresh: a member of a new cluster starts with the bootstrap peers on an empty
// storage; StartNode does not panic.
// Users: server/etcdserver/bootstrap.go:599 (newRaftNode, peers from bootstrapRaftFromCluster).
// Assumes: the cluster was allocated with these peers' bootstrap log; id's durable state is empty
// and vacant.
// Specs: StartNode.spec, NewMemoryStorage.spec; laws: cluster_alloc.spec, memStor_isStorage.spec;
// peersPts (a definition over the []Peer slice and its contexts: the caller's own slice); a nil
// logger (Config.validate takes the package logger, raft_init.spec's raftLoggerMu invariant).
func ReqStartFresh(id uint64, peers []raft.Peer) raft.Node {
	if len(peers) == 0 {
		panic("no peers")
	}
	return raft.StartNode(config(id, raft.NewMemoryStorage(), true), peers)
}

// REQ raftnode/restart-durable: a member restarts from any durable state it wrote (after its
// first snapshot too), at Applied 0, on a storage rebuilt from it; RestartNode does not panic.
// Users: server/etcdserver/bootstrap.go:597 (bootstrapRaftFromWAL), examples/raft/kvdurable/cluster.go:216.
// Assumes: ms holds id's durable state (StorageHolds: the image the client wrote at its last
// Ready's commit point); its stored snapshot is empty or one made by snap_make (snapValid), and its
// configuration is the cluster's at a committed point a at or above its compaction point (the
// snapshot's, for a MemoryStorage); id is vacant (the previous node stopped).
// Specs: RestartNode.spec; laws: memStor_isStorage.spec.
func ReqRestartDurable(id uint64, ms *raft.MemoryStorage) raft.Node {
	return raft.RestartNode(config(id, ms, true))
}

// REQ raftnode/join: a member added to a running cluster starts from an empty storage with no
// configuration, and waits for the leader.
// Users: server/etcdserver/bootstrap.go:533 (bootstrapRaftFromCluster with no peers).
// Assumes: id is fresh (freshIds_take: never used before in the cluster), its durable state empty;
// the cluster has a bootstrap log (its configuration at index 0 is empty).
// Specs: RestartNode.spec; laws: freshIds_take.spec.
func ReqJoin(id uint64) raft.Node {
	return raft.RestartNode(config(id, raft.NewMemoryStorage(), true))
}

// REQ raftnode/stop-restart: after Stop, the id may run again (on a new storage built from the
// durable state); Stop twice does not block.
// Users: server/etcdserver/raft.go:420 (onStop), examples/raft/kvdurable/kv.go:379 (crash, restart).
// Assumes: as ReqRestartDurable for ms.
// Specs: node.Stop.spec, RestartNode.spec.
func ReqStopRestart(n raft.Node, id uint64, ms *raft.MemoryStorage) raft.Node {
	n.Stop()
	n.Stop()
	return raft.RestartNode(config(id, ms, false))
}

// quietLogger is the examples' logger (kv/cluster.go:157, kvreconf/cluster.go:159, kvdurable): it
// drops everything.
type quietLogger struct{}

func (quietLogger) Debug(v ...interface{})                   {}
func (quietLogger) Debugf(format string, v ...interface{})   {}
func (quietLogger) Error(v ...interface{})                   {}
func (quietLogger) Errorf(format string, v ...interface{})   {}
func (quietLogger) Info(v ...interface{})                    {}
func (quietLogger) Infof(format string, v ...interface{})    {}
func (quietLogger) Warning(v ...interface{})                 {}
func (quietLogger) Warningf(format string, v ...interface{}) {}
func (quietLogger) Fatal(v ...interface{})                   { panic("fatal") }
func (quietLogger) Fatalf(format string, v ...interface{})   { panic("fatal") }
func (quietLogger) Panic(v ...interface{})                   { panic("panic") }
func (quietLogger) Panicf(format string, v ...interface{})   { panic("panic") }

// REQ raftnode/client-logger: a client-defined logger is passed to raft, in a Config and as the
// package logger; raft calls its formatting methods (not Fatal/Panic) on reachable paths.
// Users: server/etcdserver/bootstrap.go:591 (NewRaftLoggerZap in Config.Logger), raft.go:138
// (raft.SetLogger); examples/raft/kv/cluster.go:157, kvreconf/cluster.go:159 (quietLogger{}).
// Assumes: as ReqStartFresh.
// Specs: StartNode.spec, SetLogger.spec; loggerOk (a definition: the logger's Debugf, Infof,
// Warningf, Errorf and Error return, which quietLogger's empty bodies give).
func ReqClientLogger(id uint64, peers []raft.Peer) raft.Node {
	raft.SetLogger(quietLogger{})
	c := config(id, raft.NewMemoryStorage(), true)
	c.Logger = quietLogger{}
	if len(peers) == 0 {
		panic("no peers")
	}
	return raft.StartNode(c, peers)
}
