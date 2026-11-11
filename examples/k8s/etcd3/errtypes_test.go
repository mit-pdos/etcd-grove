package etcd3

import (
	"context"
	"fmt"
	"math/rand"
	"sort"
	"sync"
	"testing"
	"time"

	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/client/v3/credentials"
	"go.etcd.io/etcd/client/v3/kubernetes"
	"go.uber.org/zap"

	"github.com/mit-pdos/etcd-grove/examples/lib/cluster3"
	"github.com/mit-pdos/etcd-grove/examples/lib/etcdstart"
)

// clientErrTys are the dynamic types (%T) of the errors etcd's client returns, as k8s 7e-1's
// clientErrTys states them (notes/k8s-7e-1-draft.md §4): grpc's status errors, rpctypes.EtcdError,
// errors.New values (context.Canceled, io.EOF) and context.DeadlineExceeded's type.
var clientErrTys = map[string]bool{
	"*status.Error":                 true,
	"rpctypes.EtcdError":            true,
	"*errors.errorString":           true,
	"context.deadlineExceededError": true,
}

// errTypes records the dynamic types of the errors seen, per operation.
type errTypes struct {
	mu   sync.Mutex
	seen map[string]int // "op %T" -> count
	ok   map[string]int // op -> successes
	msgs map[string]string
}

func (e *errTypes) add(op string, err error) {
	e.mu.Lock()
	defer e.mu.Unlock()
	if err == nil {
		e.ok[op]++
		return
	}
	k := fmt.Sprintf("%s %T", op, err)
	e.seen[k]++
	if _, ok := e.msgs[k]; !ok {
		e.msgs[k] = err.Error()
	}
}

// ops runs one random call of each kind through kc with the context mk returns.
func errTypesOps(kc *kubernetes.Client, rng *rand.Rand, mk func() (context.Context, context.CancelFunc), et *errTypes) {
	key := fmt.Sprintf("/errtypes/k%d", rng.Intn(8))
	ctx, cancel := mk()
	defer cancel()
	switch rng.Intn(5) {
	case 0:
		_, err := kc.Get(ctx, key, kubernetes.GetOptions{})
		et.add("Get", err)
	case 1:
		// a revision: the latest, a past one, or a future one (ErrFutureRev)
		rev := []int64{0, 1, 1 << 40}[rng.Intn(3)]
		_, err := kc.List(ctx, "/errtypes/", kubernetes.ListOptions{Revision: rev, Limit: int64(rng.Intn(3))})
		et.add("List", err)
	case 2:
		_, err := kc.Get(ctx, key, kubernetes.GetOptions{Revision: []int64{1, 1 << 40}[rng.Intn(2)]})
		et.add("Get", err)
	case 3:
		_, err := kc.OptimisticPut(ctx, key, []byte("v"), int64(rng.Intn(3)), kubernetes.PutOptions{})
		et.add("OptimisticPut", err)
	default:
		_, err := kc.OptimisticDelete(ctx, key, int64(rng.Intn(3)), kubernetes.DeleteOptions{})
		et.add("OptimisticDelete", err)
	}
}

// TestClientErrorTypes (k8s 7e-1, the evidence for clientErrTys, the condition of decision 3 of the
// Draft review): every error kubernetes.Client's Get, List, OptimisticPut and OptimisticDelete
// return has one of clientErrTys' four dynamic types, over a three-member cluster under each
// partition schedule (with the Background context, as the driver's calls), with short deadlines,
// and on a closed client. Each schedule runs in a process of its own (inChild). The claim is about
// every run, so this is evidence, not proof.
func TestClientErrorTypes(t *testing.T) {
	for name, sched := range partitionSchedules() {
		t.Run(name, func(t *testing.T) {
			inChild(t, "TestClientErrorTypes", name, func(t *testing.T) { clientErrorTypes(t, sched) })
		})
	}
}

func clientErrorTypes(t *testing.T, sched []cluster3.Step) {
	lg := zap.NewNop()
	cfg := clusterConfig()
	srvs, brs, ok := cluster3.StartCluster(cfg, lg)
	if !ok {
		t.Fatal("StartCluster failed")
	}
	kc, err := kubernetes.New(clientv3.Config{
		Endpoints:            []string{cfg.Bridge1, cfg.Bridge2, cfg.Bridge3},
		DialTimeout:          etcdstart.DialTimeout,
		DialKeepAliveTime:    etcdstart.KeepAliveTime,
		DialKeepAliveTimeout: etcdstart.KeepAliveTimeout,
		Logger:               lg,
	})
	if err != nil {
		t.Fatal(err)
	}
	et := &errTypes{seen: map[string]int{}, ok: map[string]int{}, msgs: map[string]string{}}
	var total time.Duration
	for _, s := range sched {
		total += s.Delay
	}
	go cluster3.Partitioner(srvs, brs, sched)
	end := time.Now().Add(total + 2*time.Second)
	var wg sync.WaitGroup
	for w := 0; w < 6; w++ {
		wg.Add(1)
		go func(w int) {
			defer wg.Done()
			rng := rand.New(rand.NewSource(int64(w)))
			for time.Now().Before(end) {
				mk := func() (context.Context, context.CancelFunc) { return context.Background(), func() {} }
				if w >= 4 {
					// short deadlines and cancellations: context errors
					d := time.Duration(rng.Intn(20)) * time.Millisecond
					if w == 5 {
						mk = func() (context.Context, context.CancelFunc) {
							ctx, cancel := context.WithCancel(context.Background())
							time.AfterFunc(d, cancel)
							return ctx, cancel
						}
					} else {
						mk = func() (context.Context, context.CancelFunc) {
							return context.WithTimeout(context.Background(), d)
						}
					}
				}
				errTypesOps(kc, rng, mk, et)
			}
		}(w)
	}
	wg.Wait()
	// a closed client
	kc.Close()
	rng := rand.New(rand.NewSource(99))
	for i := 0; i < 40; i++ {
		errTypesOps(kc, rng, func() (context.Context, context.CancelFunc) { return context.Background(), func() {} }, et)
	}
	var ks []string
	for k := range et.seen {
		ks = append(ks, k)
	}
	sort.Strings(ks)
	for op, n := range et.ok {
		t.Logf("%s: %d ok", op, n)
	}
	bad := false
	for _, k := range ks {
		var op, ty string
		fmt.Sscanf(k, "%s %s", &op, &ty)
		t.Logf("%s: %d (%q)", k, et.seen[k], et.msgs[k])
		if !clientErrTys[ty] {
			bad = true
			t.Errorf("an error of type %s, outside clientErrTys: %s: %q", ty, k, et.msgs[k])
		}
	}
	if bad {
		t.Fatal("a fifth error type")
	}
}

// TestCredentialNilError (k8s 7e-1, the soundness fix of perRPCCredsOk, decided by etcd-grove-81):
// etcd's per-RPC credential's GetRequestMetadata returns a nil error, with no token, with a token,
// and on a cancelled context. grpc-go returns a credentials error that carries a status (or wraps
// one) unchanged as the attempt's, so the trusted perRPCCredsOk admits only credentials that never
// err.
func TestCredentialNilError(t *testing.T) {
	b := credentials.NewPerRPCCredentialBundle()
	cancelled, cancel := context.WithCancel(context.Background())
	cancel()
	for _, tok := range []string{"", "tok", ""} {
		b.UpdateAuthToken(tok)
		for _, ctx := range []context.Context{context.Background(), cancelled} {
			if _, err := b.PerRPCCredentials().GetRequestMetadata(ctx, "uri"); err != nil {
				t.Fatalf("GetRequestMetadata with token %q: %v", tok, err)
			}
		}
	}
}
