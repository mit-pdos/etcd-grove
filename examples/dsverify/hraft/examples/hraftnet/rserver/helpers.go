package rserver

import (
	"net"
	"strconv"
	"time"

	"github.com/goose-lang/primitive"
	"github.com/hashicorp/raft"
	"github.com/hashicorp/raft/examples/hraftnet"
)

// Copies of hraftnet's unexported helpers (server.go, kit.go), unchanged but for the package
// qualifiers of hraftnet's exported constants and functions.

// rnd is a number below n, at random (in the theorem, any).
func rnd(n uint64) uint64 {
	return primitive.RandomUint64() % n
}

// confAck is a server's answer to a configuration it accepted.
const confAck = 0x6b

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
	addrs := hraftnet.ServerAddrs()
	for i := uint64(1); i <= hraftnet.NS; i++ {
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
		time.Sleep(time.Duration(hraftnet.RetryMs) * time.Millisecond)
		l, err = net.Listen("tcp", addr)
	}
	return l
}
