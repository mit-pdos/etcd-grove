package kv

import (
	"context"
	"fmt"
	"sync"
	"testing"
	"time"

	"go.etcd.io/raft/v3"
	pb "go.etcd.io/raft/v3/raftpb"
	"google.golang.org/protobuf/proto"

	"github.com/anishathalye/porcupine"
	"github.com/mit-pdos/etcd-grove/examples/lintest"
)

// cluster starts n replicas connected in process, with a ticker each.
func cluster(t *testing.T, n int) ([]*KV, func()) {
	var voters []uint64
	for i := 1; i <= n; i++ {
		voters = append(voters, uint64(i))
	}
	nodes := make([]raft.Node, n)
	regs := make([]*KV, n)
	send := func(ms []*pb.Message) {
		for _, m := range ms {
			m := m
			go nodes[m.GetTo()-1].Step(context.Background(), m)
		}
	}
	stop := make(chan struct{})
	for i := 0; i < n; i++ {
		st := NewStorage(voters)
		c := &raft.Config{
			ID:              uint64(i + 1),
			ElectionTick:    10,
			HeartbeatTick:   1,
			Storage:         st,
			MaxSizePerMsg:   1 << 20,
			MaxInflightMsgs: 256,
		}
		nodes[i] = raft.RestartNode(c)
		regs[i] = New(uint64(i+1), nodes[i], st, send)
		go func(nd raft.Node) {
			tk := time.NewTicker(5 * time.Millisecond)
			defer tk.Stop()
			for {
				select {
				case <-tk.C:
					nd.Tick()
				case <-stop:
					return
				}
			}
		}(nodes[i])
	}
	return regs, func() {
		close(stop)
		for _, nd := range nodes {
			nd.Stop()
		}
	}
}

func TestPutGet(t *testing.T) {
	regs, stop := cluster(t, 3)
	defer stop()
	if v := regs[0].Get("k"); v != "" {
		t.Fatalf("initial Get = %q, want empty", v)
	}
	regs[0].Put("k", "a")
	if v := regs[1].Get("k"); v != "a" {
		t.Fatalf("Get after Put(a) = %q", v)
	}
	regs[2].Put("k", "b")
	for i, r := range regs {
		if v := r.Get("k"); v != "b" {
			t.Fatalf("replica %d: Get after Put(b) = %q", i+1, v)
		}
	}
}

func TestMainPasses(t *testing.T) {
	Main()
}

// TestRead reads through read-index on every replica after Puts, on a cluster connected by
// the store's own transport (deliver), which must pass the read-index messages and the
// heartbeats' contexts.
func TestRead(t *testing.T) {
	voters := []uint64{1, 2, 3}
	peers := make(map[uint64]raft.Node)
	storages := make(map[uint64]*Storage)
	for _, id := range voters {
		st := NewStorage(voters)
		peers[id] = raft.RestartNode(&raft.Config{
			ID:              id,
			ElectionTick:    10,
			HeartbeatTick:   1,
			Storage:         st,
			MaxSizePerMsg:   1 << 20,
			MaxInflightMsgs: 256,
			Logger:          quietLogger{},
		})
		storages[id] = st
	}
	tr := &transfers{left: timeouts}
	send := func(ms []*pb.Message) { deliver(peers, tr, ms) }
	stop := make(chan struct{})
	defer func() {
		close(stop)
		for _, nd := range peers {
			nd.Stop()
		}
	}()
	regs := make(map[uint64]*KV)
	for _, id := range voters {
		regs[id] = New(id, peers[id], storages[id], send)
		go func(nd raft.Node) {
			tk := time.NewTicker(5 * time.Millisecond)
			defer tk.Stop()
			for {
				select {
				case <-tk.C:
					nd.Tick()
				case <-stop:
					return
				}
			}
		}(peers[id])
	}
	regs[1].Put("k", "a")
	for _, id := range voters {
		if v := regs[id].Read("k"); v != "a" {
			t.Fatalf("replica %d: Read after Put(a) = %q", id, v)
		}
	}
	regs[3].Put("k", "b")
	for _, id := range voters {
		if v := regs[id].Read("k"); v != "b" {
			t.Fatalf("replica %d: Read after Put(b) = %q", id, v)
		}
	}
	if v := regs[2].Get("k"); v != "b" {
		t.Fatalf("Get after Put(b) = %q", v)
	}
}

// snapAt is a snapshot at index i.
func snapAt(i uint64) *pb.Snapshot {
	return &pb.Snapshot{Metadata: &pb.SnapshotMetadata{Index: proto.Uint64(i), Term: proto.Uint64(1)}}
}

func TestDeliverable(t *testing.T) {
	hb := []byte{1, 0, 0, 0, 0, 0, 0, 0}
	cases := []struct {
		m    *pb.Message
		want bool
	}{
		{&pb.Message{Type: pb.MsgReadIndex.Enum(), From: proto.Uint64(2), To: proto.Uint64(1)}, true},
		{&pb.Message{Type: pb.MsgReadIndex.Enum(), From: proto.Uint64(2), To: proto.Uint64(1), Term: proto.Uint64(3)}, false},
		{&pb.Message{Type: pb.MsgReadIndexResp.Enum(), From: proto.Uint64(1), To: proto.Uint64(2), Term: proto.Uint64(3)}, true},
		{&pb.Message{Type: pb.MsgHeartbeat.Enum(), From: proto.Uint64(1), To: proto.Uint64(2), Term: proto.Uint64(3), Context: hb}, true},
		{&pb.Message{Type: pb.MsgHeartbeatResp.Enum(), From: proto.Uint64(2), To: proto.Uint64(1), Term: proto.Uint64(3), Context: hb}, true},
		{&pb.Message{Type: pb.MsgVote.Enum(), From: proto.Uint64(2), To: proto.Uint64(1), Term: proto.Uint64(3), Context: []byte("CampaignTransfer")}, true},
		{&pb.Message{Type: pb.MsgVote.Enum(), From: proto.Uint64(2), To: proto.Uint64(1)}, false},
		{&pb.Message{Type: pb.MsgTimeoutNow.Enum(), From: proto.Uint64(1), To: proto.Uint64(2), Term: proto.Uint64(3)}, true},
		{&pb.Message{Type: pb.MsgTimeoutNow.Enum(), From: proto.Uint64(1), To: proto.Uint64(2)}, false},
		{&pb.Message{Type: pb.MsgTimeoutNow.Enum(), From: proto.Uint64(1), To: proto.Uint64(2), Term: proto.Uint64(3), Context: hb}, false},
		{&pb.Message{Type: pb.MsgTimeoutNow.Enum(), From: proto.Uint64(1), To: proto.Uint64(2), Term: proto.Uint64(3), Entries: []*pb.Entry{}}, false},
		{&pb.Message{Type: pb.MsgTimeoutNow.Enum(), From: proto.Uint64(2), To: proto.Uint64(2), Term: proto.Uint64(3)}, false},
		{&pb.Message{Type: pb.MsgTransferLeader.Enum(), From: proto.Uint64(3), To: proto.Uint64(1), Term: proto.Uint64(3)}, false},
		{&pb.Message{Type: pb.MsgApp.Enum(), From: proto.Uint64(1), To: proto.Uint64(2), Term: proto.Uint64(3)}, true},
		{&pb.Message{Type: pb.MsgApp.Enum(), From: proto.Uint64(1), To: proto.Uint64(1), Term: proto.Uint64(3)}, false},
		{&pb.Message{Type: pb.MsgSnap.Enum(), From: proto.Uint64(1), To: proto.Uint64(2), Term: proto.Uint64(3), Snapshot: snapAt(5)}, true},
		{&pb.Message{Type: pb.MsgSnap.Enum(), From: proto.Uint64(1), To: proto.Uint64(2), Term: proto.Uint64(3)}, false},
		{&pb.Message{Type: pb.MsgSnap.Enum(), From: proto.Uint64(1), To: proto.Uint64(2), Snapshot: snapAt(5)}, false},
		{&pb.Message{Type: pb.MsgSnap.Enum(), From: proto.Uint64(1), To: proto.Uint64(1), Term: proto.Uint64(3), Snapshot: snapAt(5)}, false},
		{&pb.Message{Type: pb.MsgSnap.Enum(), From: proto.Uint64(1), To: proto.Uint64(2), Term: proto.Uint64(3), Snapshot: snapAt(maxIndex)}, false},
		{&pb.Message{Type: pb.MsgSnap.Enum(), From: proto.Uint64(1), To: proto.Uint64(2), Term: proto.Uint64(3), Snapshot: snapAt(5), Context: hb}, false},
	}
	for i, c := range cases {
		if got := deliverable(c.m); got != c.want {
			t.Errorf("case %d: deliverable = %v, want %v", i, got, c.want)
		}
	}
}

func TestTransfersTake(t *testing.T) {
	tr := &transfers{left: 2}
	if !tr.take() || !tr.take() {
		t.Fatal("take failed with timeouts left")
	}
	if tr.take() {
		t.Fatal("take succeeded with none left")
	}
}

// TestTransfer hands the leadership around a cluster connected by the register's own
// transport (deliver), which must pass MsgTimeoutNow and the transfer's vote requests, and
// checks that the operations go on working under each new leader.
func TestTransfer(t *testing.T) {
	voters := []uint64{1, 2, 3}
	peers := make(map[uint64]raft.Node)
	storages := make(map[uint64]*Storage)
	for _, id := range voters {
		st := NewStorage(voters)
		peers[id] = raft.RestartNode(&raft.Config{
			ID:              id,
			ElectionTick:    10,
			HeartbeatTick:   1,
			Storage:         st,
			MaxSizePerMsg:   1 << 20,
			MaxInflightMsgs: 256,
			Logger:          quietLogger{},
		})
		storages[id] = st
	}
	tr := &transfers{left: timeouts}
	send := func(ms []*pb.Message) { deliver(peers, tr, ms) }
	stop := make(chan struct{})
	defer func() {
		close(stop)
		for _, nd := range peers {
			nd.Stop()
		}
	}()
	regs := make(map[uint64]*KV)
	for _, id := range voters {
		regs[id] = New(id, peers[id], storages[id], send)
		go func(nd raft.Node) {
			tk := time.NewTicker(5 * time.Millisecond)
			defer tk.Stop()
			for {
				select {
				case <-tk.C:
					nd.Tick()
				case <-stop:
					return
				}
			}
		}(peers[id])
	}
	regs[1].Put("k", "a")
	for i, to := range []uint64{1, 2, 3, 1} {
		// the leader acts on the request; the followers' forwarded requests are dropped
		deadline := time.Now().Add(10 * time.Second)
		for peers[to].Status().Lead != to || peers[to].Status().RaftState != raft.StateLeader {
			if time.Now().After(deadline) {
				t.Fatalf("transfer %d: replica %d did not become the leader", i, to)
			}
			for _, id := range voters {
				regs[id].TransferLeadership(to)
			}
			time.Sleep(20 * time.Millisecond)
		}
		val := string(rune('b' + i))
		regs[to].Put("k", val)
		// a Get first (a proposal dropped for want of a leader is retried), so that the
		// replica knows the new leader by the time it asks for a read index
		for _, id := range voters {
			if v := regs[id].Get("k"); v != val {
				t.Fatalf("transfer %d, replica %d: Get = %q, want %q", i, id, v, val)
			}
			if v := regs[id].Read("k"); v != val {
				t.Fatalf("transfer %d, replica %d: Read = %q, want %q", i, id, v, val)
			}
		}
	}
	if tr.left == timeouts {
		t.Fatal("no MsgTimeoutNow went through the transport")
	}
}

// TestKeys runs Put, Append and Get on several keys from different replicas.
func TestKeys(t *testing.T) {
	kvs, stop := cluster(t, 3)
	defer stop()
	kvs[0].Put("x", "1")
	kvs[1].Append("x", "2")
	kvs[2].Append("y", "3")
	kvs[0].Put("z", "")
	want := map[string]string{"x": "12", "y": "3", "z": "", "w": ""}
	for i, r := range kvs {
		for k, v := range want {
			if got := r.Get(k); got != v {
				t.Fatalf("replica %d: Get(%q) = %q, want %q", i+1, k, got, v)
			}
		}
	}
}

// TestEncode: decode reads back what encode wrote, and refuses what it did not.
func TestEncode(t *testing.T) {
	b := encode(7, 9, opAppend, "key", "value")
	r, s, k, key, val, ok := decode(b)
	if !ok || r != 7 || s != 9 || k != opAppend || key != "key" || val != "value" {
		t.Fatalf("decode(encode) = %v %v %v %q %q %v", r, s, k, key, val, ok)
	}
	if _, _, _, _, _, ok := decode(b[:24]); ok {
		t.Fatal("decode accepted a short entry")
	}
	bad := encode(7, 9, opPut, "key", "")
	bad[17] = 200 // a key longer than the entry
	if _, _, _, _, _, ok := decode(bad); ok {
		t.Fatal("decode accepted a key longer than the entry")
	}
}

func op(client int, kind byte, key, val string, call, ret int64, out string) porcupine.Operation {
	return porcupine.Operation{ClientId: client, Input: Input{Kind: kind, Key: key, Val: val},
		Call: call, Output: out, Return: ret}
}

// TestModel: the model accepts linearizable histories and rejects others.
func TestModel(t *testing.T) {
	ok := []porcupine.Operation{
		op(0, opPut, "a", "1", 0, 10, ""),
		op(1, opAppend, "a", "2", 5, 15, ""),
		op(2, opGet, "a", "", 20, 30, "12"),
		op(2, opGet, "b", "", 31, 32, ""),
	}
	if !porcupine.CheckOperations(Model(), ok) {
		t.Fatal("the model rejected a linearizable history")
	}
	concurrent := []porcupine.Operation{
		op(0, opPut, "a", "1", 0, 10, ""),
		op(1, opAppend, "a", "2", 0, 10, ""),
		op(2, opGet, "a", "", 0, 10, "21"),
	}
	if porcupine.CheckOperations(Model(), concurrent) {
		t.Fatal("the model accepted a value no order gives (a Put overwrites, it does not prepend)")
	}
	concurrentOk := []porcupine.Operation{
		op(0, opPut, "a", "1", 0, 10, ""),
		op(1, opAppend, "a", "2", 0, 10, ""),
		op(2, opGet, "a", "", 0, 10, "1"),
	}
	if !porcupine.CheckOperations(Model(), concurrentOk) {
		t.Fatal("the model rejected a concurrent history (Append, Put, Get)")
	}
	stale := []porcupine.Operation{
		op(0, opPut, "a", "1", 0, 10, ""),
		op(1, opPut, "a", "2", 11, 20, ""),
		op(2, opGet, "a", "", 21, 30, "1"),
	}
	if porcupine.CheckOperations(Model(), stale) {
		t.Fatal("the model accepted a stale read")
	}
	phantom := []porcupine.Operation{op(0, opGet, "a", "", 0, 10, "x")}
	if porcupine.CheckOperations(Model(), phantom) {
		t.Fatal("the model accepted a value nobody wrote")
	}
}

// TestCheck runs the randomized linearizability test with both clocks (etcd's robustness
// tests' monotonic clock and a counter), with more clients and longer runs than Main.
func TestCheck(t *testing.T) {
	// a fresh cluster for each run: the model starts from the empty store
	for i, clock := range []lintest.Clock{lintest.MonotonicClock(), lintest.CounterClock()} {
		if r := Check(StartCluster([]uint64{1, 2, 3}), clock, 8, 50); r != porcupine.Ok {
			t.Fatalf("clock %d: got %v", i, r)
		}
	}
}

// TestEncodeState checks that decodeState reads back what encodeState writes, that the encoding
// does not depend on the maps' iteration order, and that decodeState refuses what it did not
// write.
func TestEncodeState(t *testing.T) {
	kv := map[string]string{"b": "2", "a": "1", "": "e", "ab": ""}
	ops := map[string]string{string(encode(1, 2, opPut, "a", "1")): "1", "x": "", "y": "v"}
	b := encodeState(kv, ops)
	for i := 0; i < 20; i++ {
		if c := encodeState(kv, ops); string(c) != string(b) {
			t.Fatalf("encodeState is not deterministic")
		}
	}
	kv2, ops2, ok := decodeState(b)
	if !ok || len(kv2) != len(kv) || len(ops2) != len(ops) {
		t.Fatalf("decodeState(encodeState) = %v, %v, %v", kv2, ops2, ok)
	}
	for k, v := range kv {
		if kv2[k] != v {
			t.Fatalf("key %q: %q, want %q", k, kv2[k], v)
		}
	}
	for o := range ops {
		if v, ok := ops2[o]; !ok || v != ops[o] {
			t.Fatalf("op %q: %q, %v, want %q", o, v, ok, ops[o])
		}
	}
	if _, _, ok := decodeState(b[:len(b)-1]); ok {
		t.Fatalf("decodeState accepted a truncated encoding")
	}
	if _, _, ok := decodeState(append(b, 0)); ok {
		t.Fatalf("decodeState accepted trailing bytes")
	}
	if _, _, ok := decodeState(encodeState(map[string]string{}, map[string]string{})); !ok {
		t.Fatalf("decodeState refused the empty state")
	}
}

// TestSnapshotCatchUp cuts replica 3 off (no message to it is delivered, and none from it but
// its proposals), runs more than 2*snapEvery operations, so that the others take snapshots and
// compact their logs past what replica 3 has, and then heals the cut: replica 3 catches up by a
// snapshot (a MsgSnap is delivered to it), serves the latest values, and applies operations after
// it. An operation replica 3 proposed while cut off, committed by the others, is among those the
// snapshot covers: replica 3 never applies its entry, and answers it at the install, with the
// key's value after it. Replica 3 does not tick until the cut heals, so that it stays a follower
// of the leader it knew (and forwards its proposal to it).
func TestSnapshotCatchUp(t *testing.T) {
	voters := []uint64{1, 2, 3}
	peers := make(map[uint64]raft.Node)
	storages := make(map[uint64]*Storage)
	for _, id := range voters {
		st := NewStorage(voters)
		peers[id] = raft.RestartNode(&raft.Config{
			ID:              id,
			ElectionTick:    10,
			HeartbeatTick:   1,
			Storage:         st,
			MaxSizePerMsg:   1 << 20,
			MaxInflightMsgs: 256,
			Logger:          quietLogger{},
		})
		storages[id] = st
	}
	tr := &transfers{left: timeouts}
	var mu sync.Mutex
	cut := false
	healed := false
	snaps := 0
	send := func(ms []*pb.Message) {
		var pass []*pb.Message
		mu.Lock()
		for _, m := range ms {
			if cut && (m.GetTo() == 3 || (m.GetFrom() == 3 && m.GetType() != pb.MsgProp)) {
				continue
			}
			if m.GetType() == pb.MsgSnap && m.GetTo() == 3 && deliverable(m) {
				snaps++
			}
			pass = append(pass, m)
		}
		mu.Unlock()
		deliver(peers, tr, pass)
	}
	stop := make(chan struct{})
	defer func() {
		close(stop)
		for _, nd := range peers {
			nd.Stop()
		}
	}()
	regs := make(map[uint64]*KV)
	for _, id := range voters {
		regs[id] = New(id, peers[id], storages[id], send)
		go func(id uint64, nd raft.Node) {
			tk := time.NewTicker(5 * time.Millisecond)
			defer tk.Stop()
			for {
				select {
				case <-tk.C:
					mu.Lock()
					tick := id != 3 || healed
					mu.Unlock()
					if tick {
						nd.Tick()
					}
				case <-stop:
					return
				}
			}
		}(id, peers[id])
	}
	// replica 3 follows a leader (one of the others: it does not tick)
	regs[3].Put("w", "a")
	mu.Lock()
	cut = true
	mu.Unlock()
	// replica 3's operation, committed by the others while it is cut off
	ans := make(chan string, 1)
	go func() { ans <- regs[3].do(opAppend, "w", "b") }()
	op := string(encode(3, 2, opAppend, "w", "b"))
	for deadline := time.Now().Add(10 * time.Second); ; {
		regs[1].mu.Lock()
		_, done := regs[1].applied[op]
		regs[1].mu.Unlock()
		if done {
			break
		}
		if time.Now().After(deadline) {
			t.Fatalf("replica 3's operation was not committed while it was cut off")
		}
		time.Sleep(time.Millisecond)
	}
	const n = 2*snapEvery + 50
	for i := 0; i < n; i++ {
		regs[uint64(1+i%2)].Put(fmt.Sprintf("k%d", i%7), fmt.Sprint(i))
	}
	regs[1].Append("k0", "+")
	if fi, _ := storages[1].FirstIndex(); fi <= 3 {
		t.Fatalf("replica 1 did not compact its log past replica 3's operation (first index %d)", fi)
	}
	mu.Lock()
	cut = false
	healed = true
	mu.Unlock()
	// replica 3's operation, answered when it installs the snapshot that covers it
	select {
	case v := <-ans:
		if v != "ab" {
			t.Fatalf("replica 3's operation answered %q, want %q", v, "ab")
		}
	case <-time.After(10 * time.Second):
		t.Fatalf("replica 3's operation, covered by the snapshot it installed, was not answered")
	}
	// an operation of replica 3's, applied once it has caught up
	if v, want := regs[3].Get("k0"), regs[1].Get("k0"); v != want {
		t.Fatalf("replica 3: Get(k0) = %q, want %q", v, want)
	}
	for k := 0; k < 7; k++ {
		key := fmt.Sprintf("k%d", k)
		want := regs[1].Get(key)
		if v := regs[3].Read(key); v != want {
			t.Fatalf("replica 3: Read(%s) = %q, want %q", key, v, want)
		}
	}
	regs[3].Put("k1", "z")
	if v := regs[3].Get("k1"); v != "z" {
		t.Fatalf("replica 3: Get after its Put = %q", v)
	}
	mu.Lock()
	defer mu.Unlock()
	if snaps == 0 {
		t.Fatalf("no MsgSnap was delivered to replica 3")
	}
}
