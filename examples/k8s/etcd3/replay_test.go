package etcd3

import (
	"testing"

	"github.com/anishathalye/porcupine"
	"go.uber.org/zap"

	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/client/v3/kubernetes"

	"k8s.io/apimachinery/pkg/runtime/schema"
	"k8s.io/apiserver/pkg/storage/etcd3"

	"github.com/mit-pdos/etcd-grove/examples/lib/etcdstart"
	"github.com/mit-pdos/etcd-grove/examples/lib/lintest"
)

// TestReplay (k8s etcd3 stage 7d's Go check; notes/k8s-7d-scope.md), in a process of its own: Main's
// member, client, seeds and store, then lintest.RunLin and the replay along porcupine's
// linearization, as Check runs them. The replay accepts the real history; it rejects the history
// with one non-consistent Get's answer replaced by a stale one (the key as a store below the Get's
// minimum resource version held it) or by one no store held; porcupine itself also rejects both
// (the driver's model checks a Get's contents at its linearization point, so for Gets the replay
// is implied by porcupine's verdict).
func TestReplay(t *testing.T) {
	inChild(t, "TestReplay", "", func(t *testing.T) {
		lg := zap.NewNop()
		srv, err := etcdstart.StartServer("k8setcd3", "127.0.0.1:23906", clientAddr, lg)
		if err != nil {
			t.Fatal(err)
		}
		if err := etcdstart.Serve(srv, clientAddr); err != nil {
			t.Fatal(err)
		}
		kc, err := kubernetes.New(clientv3.Config{Endpoints: []string{clientAddr}, Logger: lg, MaxUnaryRetries: 1})
		if err != nil {
			t.Fatal(err)
		}
		st0, ok := seed(kc.Client)
		if !ok {
			t.Fatal("seed failed")
		}
		s, err := etcd3.New(kc, noCompactor{}, codec{}, newObj, nil, nil, Prefix, ResourcePrefix,
			schema.GroupResource{Resource: "objs"}, identity{}, etcd3.NewDefaultLeaseManagerConfig(),
			decoder{}, versioner{})
		if err != nil {
			t.Fatal(err)
		}
		tbl := newCache()
		apply := func(input any) any { return Apply(s, tbl, input) }
		gen := func(id int) any { return Gen(tbl, id) }
		r, lin := lintest.RunLin(Model(st0), apply, gen, lintest.CounterClock(), 8, 250, 0)
		if r != porcupine.Ok || len(lin) != 8*250 {
			t.Fatalf("RunLin: %v, %d operations", r, len(lin))
		}
		if !replayOk(st0, lin) {
			t.Fatal("the replay rejected the real history")
		}
		rp, _ := newReplay(st0, lin)
		gets, checked, failedWrites := 0, 0, 0
		for _, op := range lin {
			in, out := op.Input.(Input), op.Output.(Output)
			if in.Kind == KGet {
				gets++
				if in.MinRV != "" && out.Err != EOther {
					checked++
				}
			} else if out.Err == EOther {
				failedWrites++
			}
		}
		t.Logf("%d operations, %d Gets, %d validated by the replay (minimum set, no error), %d failed writes, %d replay states",
			len(lin), gets, checked, failedWrites, len(rp.states))
		if checked == 0 {
			t.Fatal("no Get for the replay to validate")
		}

		// a stale answer: a non-consistent Get answered as a store below its minimum held the key,
		// an answer no store at or above the minimum gives
		stale := -1
		var staleOut Output
		for i, op := range lin {
			in, out := op.Input.(Input), op.Output.(Output)
			if in.Kind != KGet || in.MinRV == "" || out.Err == EOther {
				continue
			}
			req, _ := parseRV(in.MinRV)
			for _, st := range rp.states {
				if st.rv >= req {
					continue
				}
				plain := in
				plain.MinRV = ""
				o := mget(plain, st)
				if !outEqual(o, out) && !rp.validate(in, o) {
					stale, staleOut = i, o
					break
				}
			}
			if stale >= 0 {
				break
			}
		}
		if stale < 0 {
			t.Fatal("no Get with a stale answer to corrupt it to")
		}
		bad := append([]porcupine.Operation{}, lin...)
		bad[stale].Output = staleOut
		t.Logf("operation %d: %+v answered %+v, corrupted to the stale %+v",
			stale, lin[stale].Input, lin[stale].Output, staleOut)
		if replayOk(st0, bad) {
			t.Fatal("the replay accepted a stale answer")
		}
		if porcupine.CheckOperations(Model(st0), bad) {
			t.Fatal("porcupine accepted a stale answer")
		}

		// an answer no store held: the object with a value never written
		bad = append([]porcupine.Operation{}, lin...)
		for i, op := range lin {
			in, out := op.Input.(Input), op.Output.(Output)
			if in.Kind == KGet && in.MinRV != "" && out.Err == ENone && out.Name != "" {
				out.Value = "never"
				bad[i].Output = out
				break
			}
		}
		if replayOk(st0, bad) {
			t.Fatal("the replay accepted an answer no store held")
		}
		if porcupine.CheckOperations(Model(st0), bad) {
			t.Fatal("porcupine accepted an answer no store held")
		}
	})
}
