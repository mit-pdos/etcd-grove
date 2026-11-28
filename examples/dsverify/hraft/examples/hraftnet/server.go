package hraftnet

import (
	"net"
	"net/rpc"
	"strconv"
	"time"

	"github.com/hashicorp/raft"
	"github.com/hashicorp/raft/examples/hraftnet/rpctransport"
	"github.com/hashicorp/raft/examples/hraftnet/service"
	"github.com/hashicorp/raft/examples/snapstore"
)

// The server machine.

// serverID is server s's raft ID, its number in decimal.
func serverID(s uint64) raft.ServerID {
	return raft.ServerID(strconv.Itoa(int(s)))
}

// serverAddr is server s's raft address: its ID (the transport maps it to ServerAddrs).
func serverAddr(s uint64) raft.ServerAddress {
	return raft.ServerAddress(strconv.Itoa(int(s)))
}

// peers is every server's network address, by raft address (the transport's peers).
func peers() map[raft.ServerAddress]string {
	ps := make(map[raft.ServerAddress]string)
	addrs := ServerAddrs()
	for i := uint64(1); i <= NS; i++ {
		ps[serverAddr(i)] = addrs[i-1]
	}
	return ps
}

// bootConfiguration is the first configuration: servers 1..n0, voters.
func bootConfiguration(n0 uint64) raft.Configuration {
	var servers []raft.Server
	for i := uint64(1); i <= n0; i++ {
		servers = append(servers, raft.Server{Suffrage: raft.Voter, ID: serverID(i), Address: serverAddr(i)})
	}
	return raft.Configuration{Servers: servers}
}

// raftConfig is server id's raft configuration: upstream's test timeouts (50 ms heartbeat and
// election timeouts and leader lease, 5 ms commit timeout); a removed server keeps running; and,
// at random, how often it snapshots (once 4-19 entries follow its last snapshot, checked every
// 10-20 ms), how many entries it keeps when it compacts its log (1, 4 or 32), and how many
// entries one AppendEntries carries (1, or up to upstream's default 64).
func raftConfig(id uint64) *raft.Config {
	conf := raft.DefaultConfig()
	conf.LocalID = serverID(id)
	conf.HeartbeatTimeout = 50 * time.Millisecond
	conf.ElectionTimeout = 50 * time.Millisecond
	conf.LeaderLeaseTimeout = 50 * time.Millisecond
	conf.CommitTimeout = 5 * time.Millisecond
	conf.ShutdownOnRemove = false
	conf.SnapshotThreshold = 4 + rnd(16)
	conf.SnapshotInterval = 10 * time.Millisecond
	conf.TrailingLogs = []uint64{1, 4, 32}[rnd(3)]
	if rnd(2) == 0 {
		conf.MaxAppendEntries = 1
	}
	return conf
}

// listen listens at addr, retrying a failed Listen.
func listen(addr string) net.Listener {
	l, err := net.Listen("tcp", addr)
	for err != nil {
		time.Sleep(time.Duration(RetryMs) * time.Millisecond)
		l, err = net.Listen("tcp", addr)
	}
	return l
}

// Server is server machine id's program (1 <= id <= NS): it waits for the first configuration's
// size n0 (configure), then runs raft over in-memory log and stable stores and the snapshot store
// examples/snapstore, with the register as its FSM, bootstrapped with servers 1..n0 as voters if
// it is one of them (else it starts empty, a non-member until a leader adds it), and serves its
// raft RPCs and its API on one net/rpc server at ServerAddrs()[id-1]. It returns only if its
// raft configuration is invalid or raft does not start.
func Server(id uint64) {
	ch := make(chan uint64, 1)
	go awaitConf(ConfAddrs()[id-1], ch)
	n0 := <-ch
	Register()
	conf := raftConfig(id)
	if err := raft.ValidateConfig(conf); err != nil {
		return
	}
	logs := raft.NewInmemStore()
	stable := raft.NewInmemStore()
	snaps := snapstore.New()
	trans := rpctransport.New(serverAddr(id), peers(), time.Duration(RPCTimeoutMs)*time.Millisecond)
	srv := rpc.NewServer()
	if err := srv.Register(trans.Receiver()); err != nil {
		return
	}
	if id <= n0 {
		if err := raft.BootstrapCluster(conf, logs, stable, snaps, trans, bootConfiguration(n0)); err != nil {
			return
		}
	}
	fsm := service.NewStore()
	r, err := raft.NewRaft(conf, fsm, logs, stable, snaps, trans)
	if err != nil {
		return
	}
	api := service.New(r, fsm, time.Duration(EnqueueMs)*time.Millisecond, time.Duration(FutureMs)*time.Millisecond)
	if err := srv.Register(api); err != nil {
		return
	}
	// Serve once both services are registered (kit change 6: a request that arrives before its
	// service is registered would be answered "can't find service"; peers and clients retry a
	// failed dial).
	go srv.Accept(listen(ServerAddrs()[id-1]))
	for {
		time.Sleep(time.Duration(IdleMs) * time.Millisecond)
	}
}
