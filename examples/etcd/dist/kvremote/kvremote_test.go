package kvremote

import (
	"fmt"
	"math/rand/v2"
	"os"
	"testing"
	"time"

	"github.com/anishathalye/porcupine"
	"go.uber.org/zap"

	"github.com/mit-pdos/etcd-grove/examples/lib/etcdstart"
	"github.com/mit-pdos/etcd-grove/examples/lib/txnwork"
	"github.com/mit-pdos/etcd-grove/examples/lib/walarea"
)

func randStr() string {
	return []string{"", "a", "k0", "a longer value", "\x00\xff"}[rand.IntN(5)]
}

func randVR() txnwork.VR {
	return txnwork.VR{Val: randStr(), Mod: rand.Int64() - rand.Int64(), Ver: rand.Int64N(10)}
}

func randTRes() txnwork.TRes {
	return txnwork.TRes{Kind: rand.IntN(3), Found: rand.IntN(2) == 0, R: randVR(), N: rand.Int64N(4) - 1}
}

func randOutput() txnwork.Output {
	return txnwork.Output{Err: rand.IntN(2) == 0, Rev: rand.Int64(), Found: rand.IntN(2) == 0, R: randVR(),
		N: rand.Int64N(3), Ok: rand.IntN(2) == 0, NRes: rand.IntN(5) - 1, Res0: randTRes(), Res1: randTRes(),
		Res2: randTRes(), NKVs: rand.IntN(5), KV0: txnwork.KV{Key: randStr(), R: randVR()},
		KV1: txnwork.KV{Key: randStr(), R: randVR()}, KV2: txnwork.KV{Key: randStr(), R: randVR()}}
}

// TestCodec: every input txnwork.Gen makes, and random outputs, decode to themselves; a truncated or
// extended encoding, and a bad bool byte, are refused.
func TestCodec(t *testing.T) {
	c := Codec()
	for n := 0; n < 20000; n++ {
		in := txnwork.Gen(0).(txnwork.Input)
		b := c.EncIn(in)
		got, ok := c.DecIn(b)
		if !ok || got.(txnwork.Input) != in {
			t.Fatalf("input %+v: decoded %+v, %v", in, got, ok)
		}
		if _, ok := c.DecIn(b[:rand.IntN(len(b))]); ok {
			t.Fatalf("a truncated input decoded")
		}
		if _, ok := c.DecIn(append(append([]byte(nil), b...), 0)); ok {
			t.Fatalf("an extended input decoded")
		}
		o := randOutput()
		ob := c.EncOut(o)
		got, ok = c.DecOut(ob)
		if !ok || got.(txnwork.Output) != o {
			t.Fatalf("output %+v: decoded %+v, %v", o, got, ok)
		}
		if _, ok := c.DecOut(ob[:rand.IntN(len(ob))]); ok {
			t.Fatalf("a truncated output decoded")
		}
		bad := append([]byte(nil), ob...)
		bad[0] = 2 // Err's byte
		if _, ok := c.DecOut(bad); ok {
			t.Fatalf("a bad bool decoded")
		}
		if c.IsUnknown(o) != o.Err || !c.IsUnknown(c.Unknown(in)) {
			t.Fatalf("IsUnknown")
		}
	}
}

// TestOneMember: an in-process member, three client nodes on loopback addresses (goroutines here;
// machines of their own in examples/etcd/dist (its test)) and the orchestrator; porcupine says Ok.
func TestOneMember(t *testing.T) {
	name := fmt.Sprintf("kvremote%d", os.Getpid()%100000)
	walarea.Reset(t, name)
	base := 21000 + 10*rand.IntN(1000)
	peer, cl := fmt.Sprintf("127.0.0.1:%d", base), fmt.Sprintf("127.0.0.1:%d", base+1)
	s, err := etcdstart.StartServer(name, peer, cl, zap.NewNop())
	if err != nil {
		t.Fatal(err)
	}
	defer s.Stop()
	if err := etcdstart.Serve(s, cl); err != nil {
		t.Fatal(err)
	}
	var nodes []string
	for c := 0; c < 3; c++ {
		a := fmt.Sprintf("127.0.0.1:%d", base+2+c)
		nodes = append(nodes, a)
		go Node(c, a, []string{cl})
	}
	time.Sleep(200 * time.Millisecond)
	if r := Orch(nodes, 30, time.Minute); r != porcupine.Ok {
		t.Fatalf("porcupine: %v", r)
	}
}
