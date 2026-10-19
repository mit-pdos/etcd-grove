package linkv

import (
	"context"
	"testing"
	"time"

	"github.com/anishathalye/porcupine"
	clientv3 "go.etcd.io/etcd/client/v3"
	"go.uber.org/zap"
)

// TestMainRun runs Main for real: one member in a fresh data directory (Main's DataDir is
// relative), 8 clients of 50 operations each, and porcupine's verdict must be Ok; then it asks the
// member Main left running whether the puts took effect (so that the history was not all errors).
func TestMainRun(t *testing.T) {
	t.Chdir(t.TempDir())
	if r := Main(8, 50); r != porcupine.Ok {
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
	if len(resp.Kvs) == 0 || resp.Header.Revision < 10 {
		t.Fatalf("Main's puts did not take effect: revision %d, %v", resp.Header.Revision, resp.Kvs)
	}
	t.Logf("revision %d after Main, keys %d", resp.Header.Revision, len(resp.Kvs))
}

func op(client int, call, ret int64, in Input, out Output) porcupine.Operation {
	return porcupine.Operation{ClientId: client, Input: in, Call: call, Output: out, Return: ret}
}

// TestModel checks the model on histories: a failed put that takes effect after its call
// returned is allowed (Model.lean's example), a get that reads a value never written is not, and
// neither is a get that misses a put that returned before it was called.
func TestModel(t *testing.T) {
	put := Input{Put: true, Key: "k", Val: "v"}
	get := Input{Key: "k"}
	late := []porcupine.Operation{
		op(0, 0, 1, put, Output{Err: true}),
		op(1, 2, 3, get, Output{}),
		op(1, 4, 5, get, Output{Found: true, Val: "v"}),
	}
	if r := porcupine.CheckOperations(Model(), late); !r {
		t.Fatalf("late effect of a failed put: rejected")
	}
	never := []porcupine.Operation{
		op(0, 0, 1, get, Output{Found: true, Val: "v"}),
	}
	if r := porcupine.CheckOperations(Model(), never); r {
		t.Fatalf("a get of a value never written: accepted")
	}
	stale := []porcupine.Operation{
		op(0, 0, 1, put, Output{}),
		op(1, 2, 3, get, Output{}),
	}
	if r := porcupine.CheckOperations(Model(), stale); r {
		t.Fatalf("a get missing a completed put: accepted")
	}
	twice := []porcupine.Operation{
		op(0, 0, 1, put, Output{Err: true}),
		op(1, 2, 3, Input{Put: true, Key: "k", Val: "w"}, Output{}),
		op(1, 4, 5, get, Output{Found: true, Val: "v"}),
		op(1, 6, 7, Input{Put: true, Key: "k", Val: "w"}, Output{}),
		op(1, 8, 9, get, Output{Found: true, Val: "v"}),
	}
	if r := porcupine.CheckOperations(Model(), twice); r {
		t.Fatalf("a failed put taking effect twice: accepted")
	}
}
