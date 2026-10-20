package linkvtxn

import (
	"context"
	"testing"
	"time"

	"github.com/anishathalye/porcupine"
	clientv3 "go.etcd.io/etcd/client/v3"
	"go.uber.org/zap"
)

// TestMainRun runs Main for real: one member in a fresh data directory, 8 clients of 100
// operations each, and porcupine's verdict must be Ok; then it checks that writes took effect.
func TestMainRun(t *testing.T) {
	t.Chdir(t.TempDir())
	if r := Main(8, 100); r != porcupine.Ok {
		t.Fatalf("got %v", r)
	}
	cli, err := clientv3.New(clientv3.Config{Endpoints: []string{clientAddr}, Logger: zap.NewNop()})
	if err != nil {
		t.Fatal(err)
	}
	defer cli.Close()
	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()
	resp, err := cli.Get(ctx, "k", clientv3.WithPrefix())
	if err != nil {
		t.Fatal(err)
	}
	if resp.Header.Revision < 20 {
		t.Fatalf("Main's writes did not take effect: revision %d", resp.Header.Revision)
	}
	t.Logf("revision %d after Main, keys %d", resp.Header.Revision, len(resp.Kvs))
}

func op(client int, call, ret int64, in Input, out Output) porcupine.Operation {
	return porcupine.Operation{ClientId: client, Input: in, Call: call, Output: out, Return: ret}
}

// seq is a sequential history: each operation returns before the next is called.
func seq(ios ...any) []porcupine.Operation {
	ops := []porcupine.Operation{}
	for i := 0; i+1 < len(ios); i += 2 {
		t := int64(len(ops) * 2)
		ops = append(ops, op(0, t, t+1, ios[i].(Input), ios[i+1].(Output)))
	}
	return ops
}

func get(k string) Input     { return Input{Kind: KGet, Key: k} }
func putI(k, v string) Input { return Input{Kind: KPut, Key: k, Val: v} }
func del(k string) Input     { return Input{Kind: KDel, Key: k} }
func found(rev int64, v string, mod, ver int64) Output {
	return Output{Rev: rev, Found: true, R: VR{Val: v, Mod: mod, Ver: ver}}
}

func accepts(t *testing.T, name string, ops []porcupine.Operation) {
	t.Helper()
	if !porcupine.CheckOperations(Model(), ops) {
		t.Errorf("%s: rejected", name)
	}
}

func rejects(t *testing.T, name string, ops []porcupine.Operation) {
	t.Helper()
	if porcupine.CheckOperations(Model(), ops) {
		t.Errorf("%s: accepted", name)
	}
}

// TestModel checks the model on histories robustness's model accepts or rejects.
func TestModel(t *testing.T) {
	accepts(t, "put, get with revisions", seq(
		putI("k0", "a"), Output{Rev: 2},
		get("k0"), found(2, "a", 2, 1),
		putI("k0", "b"), Output{Rev: 3},
		get("k0"), found(3, "b", 3, 2)))
	rejects(t, "a get with the wrong version", seq(
		putI("k0", "a"), Output{Rev: 2},
		get("k0"), found(2, "a", 2, 2)))
	rejects(t, "a revision going backwards", seq(
		putI("k0", "a"), Output{Rev: 2},
		get("k1"), Output{Rev: 1}))
	accepts(t, "a delete of a missing key keeps the revision", seq(
		del("k0"), Output{Rev: 1, N: 0}))
	rejects(t, "a delete of a missing key counting one", seq(
		del("k0"), Output{Rev: 2, N: 1}))
	rejects(t, "a lost delete", seq(
		putI("k0", "a"), Output{Rev: 2},
		del("k0"), Output{Rev: 3, N: 1},
		get("k0"), found(3, "a", 2, 1)))
	accepts(t, "a deleted key's version restarts", seq(
		putI("k0", "a"), Output{Rev: 2},
		del("k0"), Output{Rev: 3, N: 1},
		putI("k0", "b"), Output{Rev: 4},
		get("k0"), found(4, "b", 4, 1)))
	cas := func(v string) Input {
		return Input{Kind: KTxn, Cmps: []Cmp{{Kind: CValue, Key: "k0", Val: v}},
			Then: []TOp{{Kind: TPut, Key: "k0", Val: "z"}}, Else: []TOp{{Kind: TGet, Key: "k0"}}}
	}
	accepts(t, "a compare-and-set that matches", seq(
		putI("k0", "a"), Output{Rev: 2},
		cas("a"), Output{Rev: 3, Ok: true, Res: []TRes{{Kind: TPut}}},
		get("k0"), found(3, "z", 3, 2)))
	accepts(t, "a compare-and-set that does not match", seq(
		putI("k0", "a"), Output{Rev: 2},
		cas("b"), Output{Rev: 2, Ok: false, Res: []TRes{{Kind: TGet, Found: true, R: VR{"a", 2, 1}}}}))
	rejects(t, "a transaction run in the wrong branch", seq(
		putI("k0", "a"), Output{Rev: 2},
		cas("b"), Output{Rev: 3, Ok: true, Res: []TRes{{Kind: TPut}}}))
	multi := Input{Kind: KTxn, Then: []TOp{{Kind: TPut, Key: "k0", Val: "a"}, {Kind: TGet, Key: "k0"},
		{Kind: TDel, Key: "k1"}}}
	accepts(t, "a transaction's get sees its own put, one revision", seq(
		multi, Output{Rev: 2, Ok: true, Res: []TRes{{Kind: TPut},
			{Kind: TGet, Found: true, R: VR{"a", 2, 1}}, {Kind: TDel, N: 0}}}))
	rejects(t, "a transaction's get missing its own put", seq(
		multi, Output{Rev: 2, Ok: true, Res: []TRes{{Kind: TPut},
			{Kind: TGet, Found: false}, {Kind: TDel, N: 0}}}))
	accepts(t, "a list", seq(
		putI("k1", "b"), Output{Rev: 2},
		putI("k0", "a"), Output{Rev: 3},
		Input{Kind: KList}, Output{Rev: 3, KVs: []KV{{"k0", VR{"a", 3, 1}}, {"k1", VR{"b", 2, 1}}}}))
	// failed writes
	accepts(t, "a failed put taking effect late", []porcupine.Operation{
		op(0, 0, 1, putI("k0", "a"), Output{Err: true}),
		op(1, 2, 3, get("k0"), Output{Rev: 1}),
		op(1, 4, 5, get("k0"), found(2, "a", 2, 1)),
	})
	accepts(t, "a failed put never taking effect", []porcupine.Operation{
		op(0, 0, 1, putI("k0", "a"), Output{Err: true}),
		op(1, 2, 3, get("k0"), Output{Rev: 1}),
	})
	rejects(t, "a failed put taking effect twice", []porcupine.Operation{
		op(0, 0, 1, putI("k0", "a"), Output{Err: true}),
		op(1, 2, 3, get("k0"), found(2, "a", 2, 1)),
		op(1, 4, 5, get("k0"), found(3, "a", 3, 2)),
	})
	accepts(t, "a failed read constrains nothing", []porcupine.Operation{
		op(0, 0, 1, get("k0"), Output{Err: true}),
		op(0, 2, 3, Input{Kind: KList}, Output{Err: true}),
	})
}
