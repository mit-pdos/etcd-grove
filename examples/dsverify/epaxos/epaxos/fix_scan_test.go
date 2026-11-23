package epaxos

import (
	"bytes"
	"encoding/binary"
	"testing"

	"github.com/imdea-software/swiftpaxos-epaxos/state"
)

// scan is SwiftPaxos's SCAN of n keys after k (client.SendScan: V is n as 8 little-endian bytes).
func scan(k int64, n uint64) state.Command {
	v := make([]byte, 8)
	binary.LittleEndian.PutUint64(v, n)
	return state.Command{Op: state.SCAN, K: state.Key(k), V: state.Value(v)}
}

// scanSchedule: replica 0 commits δ = 0.0 (PUT k1 "v15") with 2 and 3 (1 and 4 do not hear of it
// yet), and replies to its client. Then replica 1 proposes γ = 1.0, a SCAN of keys 0..1, which
// state.Conflict says interferes with δ (key 1 is in its range). γ's committed attributes must
// order it after δ or δ after γ (EPaxos's dependency rule: of two interfering committed
// instances, one has the other in its deps), and γ's reply, given after δ's, must see "a".
func TestScanDependsOnPutInRange(t *testing.T) {
	c := newCluster(t, 5)
	for _, q := range []int32{1, 4} {
		c.r[0].Alive[q] = false
	}
	c.propose(0, put(1, "v15"))
	c.settle(instOf(0, 0), among(0, 2, 3))
	if !committed(c.inst(0, 0, 0)) {
		t.Fatalf("setup: 0 did not commit 0.0: %s", instString(c.inst(0, 0, 0)))
	}
	c.execAll(0)
	if c.replies[0].Len() == 0 {
		t.Fatalf("setup: no reply to δ's client")
	}
	c.drop(instOf(0, 0))

	c.propose(1, scan(0, 1))
	c.settle(instOf(1, 0))
	if !committed(c.inst(1, 1, 0)) {
		t.Fatalf("setup: 1 did not commit 1.0: %s", instString(c.inst(1, 1, 0)))
	}
	if e := c.depsError(); e != "" {
		t.Error(e)
	}
	// γ's leader executes it (δ, unknown to 1 unless γ depends on it, is not committed there).
	c.execAll(1)
	if c.replies[1].Len() > 0 && !bytes.Contains(c.replies[1].Bytes(), []byte("v15")) {
		t.Errorf("the scan of keys 0..1 returned without δ's value, after δ's reply")
	}
}

// TestPutDependsOnScanInRange: the converse order. Replica 1 commits γ = 1.0 (SCAN of keys 0..1)
// with 2 and 3; then replica 0 proposes δ = 0.0 (PUT k1), which must have γ in its deps or be in
// γ's.
func TestPutDependsOnScanInRange(t *testing.T) {
	c := newCluster(t, 5)
	for _, q := range []int32{0, 4} {
		c.r[1].Alive[q] = false
	}
	c.propose(1, scan(0, 1))
	c.settle(instOf(1, 0), among(1, 2, 3))
	if !committed(c.inst(1, 1, 0)) {
		t.Fatalf("setup: 1 did not commit 1.0: %s", instString(c.inst(1, 1, 0)))
	}
	c.drop(instOf(1, 0))
	c.propose(0, put(1, "a"))
	c.settle(instOf(0, 0))
	if !committed(c.inst(0, 0, 0)) {
		t.Fatalf("setup: 0 did not commit 0.0: %s", instString(c.inst(0, 0, 0)))
	}
	if e := c.depsError(); e != "" {
		t.Fatal(e)
	}
}
