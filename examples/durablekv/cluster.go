package durablekv

import (
	"context"
	"encoding/binary"
	"sync"
	"time"

	"github.com/mit-pdos/etcd-grove/examples/durable"
	pb "go.etcd.io/raft/v3/raftpb"
	"google.golang.org/protobuf/proto"
)

// quietLogger is a raft.Logger that discards what raft logs; Fatal and Panic panic, as raft
// expects of them.
type quietLogger struct{}

func (quietLogger) Debug(v ...interface{})                   {}
func (quietLogger) Debugf(format string, v ...interface{})   {}
func (quietLogger) Error(v ...interface{})                   {}
func (quietLogger) Errorf(format string, v ...interface{})   {}
func (quietLogger) Info(v ...interface{})                    {}
func (quietLogger) Infof(format string, v ...interface{})    {}
func (quietLogger) Warning(v ...interface{})                 {}
func (quietLogger) Warningf(format string, v ...interface{}) {}
func (quietLogger) Fatal(v ...interface{})                   { panic("raft: fatal") }
func (quietLogger) Fatalf(format string, v ...interface{})   { panic(format) }
func (quietLogger) Panic(v ...interface{})                   { panic("raft: panic") }
func (quietLogger) Panicf(format string, v ...interface{})   { panic(format) }

const (
	tickInterval = 5 * time.Millisecond
	// ticks bounds the ticks of a replica (an hour and a half of them): each moves raft's
	// clock, and the terms it starts must stay below 2^64.
	ticks = 1 << 20
	// retryAfter is how long a client waits for an operation's answer before it proposes it
	// again (the proposal may be lost: a leader that crashes before it replicates it).
	retryAfter = 200 * time.Millisecond
)

// maxSeq is the last sequence number (and epoch): a client that has used them all up stops.
const maxSeq = ^uint64(0)

// Cluster is a cluster of the given voters connected in process, each replica's durable file
// in the directory dir, and the store's client: the current incarnation of each replica, and
// the client's epoch (one more than the last client's on dir, kept durably in the file
// dir/epoch) and the last sequence number it used in it, which make its operations' encodings
// unique, across restarts of the client too. stopped ends the ticks.
type Cluster struct {
	dir    string
	voters []uint64

	mu       sync.Mutex
	replicas map[uint64]*Replica
	epoch    uint64
	seq      uint64
	stopped  bool
}

// itoa is n in decimal.
func itoa(n uint64) string {
	if n == 0 {
		return "0"
	}
	var b []byte
	for n != 0 {
		b = append([]byte{byte('0' + n%10)}, b...)
		n = n / 10
	}
	return string(b)
}

// fileOf is the durable file of replica id in dir.
func fileOf(dir string, id uint64) string {
	return dir + "/replica-" + itoa(id)
}

// nextEpoch is one more than the epoch dir/epoch holds (0 if none), which it then holds.
func nextEpoch(dir string) uint64 {
	data, ok := durable.Read(dir + "/epoch")
	epoch := uint64(0)
	if ok && len(data) == 8 {
		epoch = binary.LittleEndian.Uint64([]byte(data))
	}
	if epoch == maxSeq {
		for {
		}
	}
	epoch++
	var b [8]byte
	binary.LittleEndian.PutUint64(b[:], epoch)
	durable.Write(dir+"/epoch", string(b[:]))
	return epoch
}

// StartCluster starts the cluster of the given voters on the directory dir, which must exist:
// each replica from its file there (a new replica if there is none, so that an empty dir is a
// new cluster), with the transport between them and their ticks.
func StartCluster(dir string, voters []uint64) *Cluster {
	c := &Cluster{dir: dir, voters: voters, replicas: make(map[uint64]*Replica),
		epoch: nextEpoch(dir)}
	c.mu.Lock()
	for _, id := range voters {
		c.replicas[id] = start(id, fileOf(dir, id), voters, c.send)
	}
	c.mu.Unlock()
	for _, id := range voters {
		go c.tick(id)
	}
	return c
}

// replica is the current incarnation of replica id (nil for an unknown id).
func (c *Cluster) replica(id uint64) *Replica {
	c.mu.Lock()
	r := c.replicas[id]
	c.mu.Unlock()
	return r
}

// send delivers messages to the current incarnation of their targets, each as a fresh copy
// (the wire's; the receiver may adopt it); a message to an unknown replica or to its sender
// is dropped, as is the error of Step.
func (c *Cluster) send(ms []*pb.Message) {
	for _, m := range ms {
		if m.GetTo() == m.GetFrom() {
			continue
		}
		r := c.replica(m.GetTo())
		if r == nil {
			continue
		}
		r.node.Step(context.Background(), proto.Clone(m).(*pb.Message))
	}
}

// tick drives the clock of replica id, whichever its incarnation, until the cluster stops.
func (c *Cluster) tick(id uint64) {
	for i := 0; i < ticks; i++ {
		time.Sleep(tickInterval)
		c.mu.Lock()
		stopped := c.stopped
		r := c.replicas[id]
		c.mu.Unlock()
		if stopped {
			return
		}
		r.node.Tick()
	}
}

// Restart crashes the current incarnation of replica id, which loses everything but its
// durable file, and starts the next one from the file. An unknown id restarts nothing.
func (c *Cluster) Restart(id uint64) {
	c.mu.Lock()
	r, ok := c.replicas[id]
	if ok {
		r.crash()
		c.replicas[id] = start(id, fileOf(c.dir, id), c.voters, c.send)
	}
	c.mu.Unlock()
}

// Stop crashes every replica and stops the ticks; the cluster can be started again on its
// directory (StartCluster).
func (c *Cluster) Stop() {
	c.mu.Lock()
	c.stopped = true
	for _, r := range c.replicas {
		r.crash()
	}
	c.mu.Unlock()
}

// do runs one operation on replica id and waits until it is applied; it returns the key's
// value after the operation. The operation gets a fresh encoding, and is proposed again, with
// the same encoding, to the current incarnation of the replica when the proposal is dropped
// (no leader known), when the incarnation crashes, or after retryAfter without an answer: it
// takes effect once however often it is proposed (Replica.apply).
func (c *Cluster) do(id uint64, kind byte, key, val string) string {
	c.mu.Lock()
	if c.seq == maxSeq {
		for {
		}
	}
	c.seq++
	o := encode(c.epoch, c.seq, kind, key, val)
	c.mu.Unlock()
	for {
		r := c.replica(id)
		ch := r.propose(o)
		if ch == nil {
			time.Sleep(tickInterval)
			continue
		}
		select {
		case v := <-ch:
			return v
		case <-r.done:
		case <-time.After(retryAfter):
		}
	}
}

// Put sets key's value to val, through replica id.
func (c *Cluster) Put(id uint64, key, val string) {
	c.do(id, opPut, key, val)
}

// Get returns key's value ("" for a key never set), through replica id.
func (c *Cluster) Get(id uint64, key string) string {
	return c.do(id, opGet, key, "")
}

// Append appends val to key's value, through replica id.
func (c *Cluster) Append(id uint64, key, val string) {
	c.do(id, opAppend, key, val)
}
