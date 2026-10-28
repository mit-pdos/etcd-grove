package kvreconf

import (
	"testing"
	"time"

	"github.com/anishathalye/porcupine"
	"github.com/mit-pdos/etcd-grove/examples/lintest"
)

func TestEncode(t *testing.T) {
	id, kind, key, val, ok := decode(encode(7, opPut, "k", "v"))
	if !ok || id != 7 || kind != opPut || key != "k" || val != "v" {
		t.Fatalf("decode(encode) = %d %d %q %q %v", id, kind, key, val, ok)
	}
	if _, _, _, _, ok := decode(nil); ok {
		t.Fatal("decode(nil) ok")
	}
	r, seq, key, ok := decodeReadCtx(readCtx(3, 9, "x"))
	if !ok || r != 3 || seq != 9 || key != "x" {
		t.Fatalf("decodeReadCtx(readCtx) = %d %d %q %v", r, seq, key, ok)
	}
	if _, ok := decodeConfCtx(nil); ok {
		t.Fatal("decodeConfCtx(nil) ok")
	}
	kv := map[string]string{"a": "1", "b": ""}
	ops := map[string]string{string(encode(1, opGet, "a", "")): "1"}
	kv2, ops2, seq2, ok := decodeState(encodeState(kv, ops, 42))
	if !ok || seq2 != 42 || len(kv2) != 2 || kv2["a"] != "1" || len(ops2) != 1 {
		t.Fatalf("decodeState(encodeState) = %v %v %d %v", kv2, ops2, seq2, ok)
	}
}

// TestSingle checks that every change single chooses keeps the configuration within its
// bounds, from random configurations reached by its own changes.
func TestSingle(t *testing.T) {
	next := uint64(100)
	fresh := func() uint64 { next++; return next }
	cfg := config{voters: []uint64{1, 2, 3}}
	for i := 0; i < 10000; i++ {
		_, after, ok := single(cfg, nil, fresh)
		if !ok {
			t.Fatalf("no change from %v", cfg)
		}
		if len(after.voters) < 1 || len(after.voters) > maxVoters || len(after.voters)+len(after.learners) > maxMembers {
			t.Fatalf("%v -> %v out of bounds", cfg, after)
		}
		for _, id := range after.voters {
			if hasID(after.learners, id) {
				t.Fatalf("%v -> %v: %d both voter and learner", cfg, after, id)
			}
		}
		cfg = after
	}
}

func TestPutGetRead(t *testing.T) {
	c := StartCluster(Options{})
	defer c.Stop()
	if v := c.Get("k"); v != "" {
		t.Fatalf("initial Get = %q", v)
	}
	c.Put("k", "a")
	if v := c.Get("k"); v != "a" {
		t.Fatalf("Get after Put = %q", v)
	}
	if v := c.Read("k"); v != "a" {
		t.Fatalf("Read after Put = %q", v)
	}
}

// TestReconfigureQuiet reconfigures a cluster with no client traffic and no faults, then checks
// that the members converge.
func TestReconfigureQuiet(t *testing.T) {
	c := StartCluster(Options{})
	defer c.Stop()
	stop := make(chan struct{})
	done := make(chan struct{})
	go func() {
		for i := 0; i < 30; i++ {
			c.Put("k", string([]byte{byte('a' + i%26)}))
		}
		close(done)
	}()
	c.Reconfigure(20, time.Millisecond, stop)
	<-done
	if err := c.Converged(5 * time.Second); err != nil {
		t.Fatal(err)
	}
	t.Logf("%v", &c.Stats)
}

func TestMain_(t *testing.T) {
	Main()
}

// TestRounds runs several rounds of the full test.
func TestRounds(t *testing.T) {
	if testing.Short() {
		t.Skip("short")
	}
	for i := 0; i < 3; i++ {
		res, err, c := Run(DefaultConfig(), lintest.CounterClock())
		t.Logf("round %d: %v; %v", i+1, res, &c.Stats)
		if res != porcupine.Ok {
			t.Fatal("porcupine rejected the trace")
		}
		if err != nil {
			t.Fatal(err)
		}
	}
}
