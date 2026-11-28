// Package rserver is the hraft kit's restartable server machine (hraft_robust; notes/dsv-hraft.md,
// "hraft_robust"): hraftnet.Server's program over durable stores (package disk), for machines that
// crash and restart. A package of its own, so that hraftnet (the program of hraft_nocrash_robust,
// whose servers never crash) is unchanged: Server's unexported helpers (raftConfig, serverAddr,
// peers, bootConfiguration, listen, rnd, confAck) are copied here (helpers.go), unchanged.
package rserver

import (
	"io"
	"net/rpc"
	"time"

	"github.com/hashicorp/raft"
	"github.com/hashicorp/raft/examples/hraftnet"
	"github.com/hashicorp/raft/examples/hraftnet/disk"
	"github.com/hashicorp/raft/examples/hraftnet/rpctransport"
	"github.com/hashicorp/raft/examples/hraftnet/service"
	"github.com/mit-pdos/etcd-grove/examples/lib/durable"
)

// DataDir is a restartable server machine's data directory (cmd/rserver*): an empty root of its
// file system at its first start.
const DataDir = "/var/lib/hraft"

// n0File is the marker of a completed first start in dir: the first configuration's size, one
// byte, written last.
func n0File(dir string) string { return dir + "/n0" }

// readN0 is the size dir's marker holds, and true, or false if dir has no valid marker (no first
// start completed).
func readN0(dir string) (uint64, bool) {
	s, ok := durable.Read(n0File(dir))
	if !ok || len(s) != 1 {
		return 0, false
	}
	n0 := uint64(s[0])
	if n0 < 1 || hraftnet.NS < n0 {
		return 0, false
	}
	return n0, true
}

// awaitConfDurable is awaitConf for a machine that persists the first configuration's size before
// it acknowledges it: it listens on addr (retrying a failed Listen) and answers each connection
// in turn. Until it knows n0 (known 0: a first start), the first size it reads (1 to hraftnet.NS) is sent
// on ch, and acknowledged once persisted is closed (the marker written); from then on (or from the
// start, known the marker's size, on a restart) every connection whose byte is n0 is acknowledged
// (the orchestrator sends again until it has an answer, which a crash may have lost). A connection
// that fails, or whose byte is anything else, is closed without an answer.
func awaitConfDurable(addr string, known uint64, ch chan uint64, persisted chan struct{}) {
	l := listen(addr)
	n0 := known
	for {
		c, err := l.Accept()
		if err != nil {
			continue
		}
		var b [1]byte
		if _, err := io.ReadFull(c, b[:]); err == nil {
			m := uint64(b[0])
			if n0 == 0 && 1 <= m && m <= hraftnet.NS {
				ch <- m
				<-persisted
				n0 = m
			}
			if n0 != 0 && m == n0 {
				c.Write([]byte{confAck})
			}
		}
		c.Close()
	}
}

// ServerR is restartable server machine id's program (1 <= id <= hraftnet.NS), over its data directory
// dir: Server's, with raft's stores durable in dir (package disk) and RestoreCommittedLogs on or
// off at random (each start draws its own raft options).
//
// The first start (dir has no marker n0File): it waits for the first configuration's size n0,
// starts from empty stores (disk.Fresh, disk.FreshSnaps: whatever an earlier first start, cut
// short by a crash, wrote is overwritten), bootstraps servers 1..n0 as voters if it is one of them,
// and only then writes the marker and acknowledges n0. A crash before the marker repeats the
// first start, so a first start is all or nothing. A restart (a marker): the stores as dir holds
// them (disk.Open, disk.OpenSnaps), no bootstrap; it acknowledges the marker's size to an
// orchestrator that sends it again. Then, as Server: raft over the kit's transport, with a fresh
// register as its state machine (raft restores it from the latest snapshot and, with
// RestoreCommittedLogs, the committed entries after it), and its API, on one net/rpc server. It
// returns only if its raft configuration is invalid, a store's file does not decode, or raft does
// not start.
func ServerR(id uint64, dir string) {
	hraftnet.Register()
	conf := raftConfig(id)
	conf.RestoreCommittedLogs = rnd(2) == 0
	if err := raft.ValidateConfig(conf); err != nil {
		return
	}
	trans := rpctransport.New(serverAddr(id), peers(), time.Duration(hraftnet.RPCTimeoutMs)*time.Millisecond)
	srv := rpc.NewServer()
	if err := srv.Register(trans.Receiver()); err != nil {
		return
	}
	var d *disk.Disk
	var snaps *disk.Snaps
	n0, ok := readN0(dir)
	if ok {
		go awaitConfDurable(hraftnet.ConfAddrs()[id-1], n0, nil, nil)
		var err error
		if d, err = disk.Open(dir); err != nil {
			return
		}
		if snaps, err = disk.OpenSnaps(dir); err != nil {
			return
		}
	} else {
		ch := make(chan uint64, 1)
		persisted := make(chan struct{})
		go awaitConfDurable(hraftnet.ConfAddrs()[id-1], 0, ch, persisted)
		n0 = <-ch
		d = disk.Fresh(dir)
		snaps = disk.FreshSnaps(dir)
		if id <= n0 {
			if err := raft.BootstrapCluster(conf, d, d, snaps, trans, bootConfiguration(n0)); err != nil {
				return
			}
		}
		durable.Write(n0File(dir), string([]byte{byte(n0)}))
		close(persisted)
	}
	fsm := service.NewStore()
	r, err := raft.NewRaft(conf, fsm, d, d, snaps, trans)
	if err != nil {
		return
	}
	api := service.New(r, fsm, time.Duration(hraftnet.EnqueueMs)*time.Millisecond, time.Duration(hraftnet.FutureMs)*time.Millisecond)
	if err := srv.Register(api); err != nil {
		return
	}
	go srv.Accept(listen(hraftnet.ServerAddrs()[id-1]))
	for {
		time.Sleep(time.Duration(hraftnet.IdleMs) * time.Millisecond)
	}
}
