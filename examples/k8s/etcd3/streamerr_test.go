package etcd3

import (
	"context"
	"errors"
	"fmt"
	"io"
	"math/rand"
	"sort"
	"sync"
	"testing"
	"time"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	clientv3 "go.etcd.io/etcd/client/v3"
	"go.uber.org/zap"
	"google.golang.org/grpc"

	"github.com/mit-pdos/etcd-grove/examples/lib/cluster3"
	"github.com/mit-pdos/etcd-grove/examples/lib/etcdstart"
)

// streamErrCell is "" when err has the shape the trusted cliStreamErr promises (T-CE, k8s 7f-5,
// approved by etcd-grove-81 2026-11-16): one of clientErrTys' dynamic types, and, if an
// *errors.errorString, io.EOF's or context.Canceled's very value (so its cell holds "EOF" or
// "context canceled" for good: errCellOk); otherwise what is wrong.
func streamErrCell(err error) string {
	ty := fmt.Sprintf("%T", err)
	if !clientErrTys[ty] {
		return "type " + ty + " outside clientErrTys"
	}
	if ty == "*errors.errorString" && err != io.EOF && err != context.Canceled {
		return fmt.Sprintf("an *errors.errorString that is neither io.EOF nor context.Canceled: %q", err.Error())
	}
	return ""
}

type streamErrs struct {
	mu   sync.Mutex
	seen map[string]int
	msgs map[string]string
	bad  []string
}

func (s *streamErrs) add(op string, err error) {
	if err == nil {
		return
	}
	s.mu.Lock()
	defer s.mu.Unlock()
	k := fmt.Sprintf("%s %T", op, err)
	s.seen[k]++
	if _, ok := s.msgs[k]; !ok {
		s.msgs[k] = err.Error()
	}
	if why := streamErrCell(err); why != "" {
		s.bad = append(s.bad, op+": "+why)
	}
}

// streamOps opens one grpc client stream through the client's connection (etcd's stream
// interceptor included), a Watch or a LeaseKeepAlive stream, and runs Send, Recv and CloseSend on
// it until it fails or a few responses arrived, recording every error.
func streamOps(conn *grpc.ClientConn, rng *rand.Rand, ctx context.Context, se *streamErrs) {
	if rng.Intn(4) == 0 {
		ctx = clientv3.WithRequireLeader(ctx)
	}
	if rng.Intn(2) == 0 {
		st, err := pb.NewWatchClient(conn).Watch(ctx)
		se.add("Watch.NewStream", err)
		if err != nil {
			return
		}
		key := fmt.Sprintf("/streamerr/k%d", rng.Intn(4))
		err = st.Send(&pb.WatchRequest{RequestUnion: &pb.WatchRequest_CreateRequest{
			CreateRequest: &pb.WatchCreateRequest{Key: []byte(key), ProgressNotify: true}}})
		se.add("Watch.Send", err)
		if rng.Intn(3) == 0 {
			se.add("Watch.CloseSend", st.CloseSend())
		}
		for i := 0; i < 3; i++ {
			_, err := st.Recv()
			se.add("Watch.Recv", err)
			if err != nil {
				return
			}
			if rng.Intn(2) == 0 {
				err = st.Send(&pb.WatchRequest{RequestUnion: &pb.WatchRequest_ProgressRequest{
					ProgressRequest: &pb.WatchProgressRequest{}}})
				se.add("Watch.Send", err)
			}
		}
		return
	}
	st, err := pb.NewLeaseClient(conn).LeaseKeepAlive(ctx)
	se.add("LeaseKeepAlive.NewStream", err)
	if err != nil {
		return
	}
	for i := 0; i < 3; i++ {
		se.add("LeaseKeepAlive.Send", st.Send(&pb.LeaseKeepAliveRequest{ID: int64(rng.Intn(5) + 1)}))
		if rng.Intn(4) == 0 {
			se.add("LeaseKeepAlive.CloseSend", st.CloseSend())
		}
		_, err := st.Recv()
		se.add("LeaseKeepAlive.Recv", err)
		if err != nil {
			return
		}
	}
}

// TestStreamErrorCells (k8s 7f-5, the evidence for T-CE, decided by etcd-grove-81 2026-11-16): every
// error a grpc client stream of etcd's client connection returns (NewStream, Send, Recv,
// CloseSend; Watch and LeaseKeepAlive streams) has one of clientErrTys' types, and an
// *errors.errorString one is io.EOF or context.Canceled itself (errCellOk), over a three-member
// cluster under each partition schedule (client connections blackholed and dropped, peers cut),
// with cancellations and short deadlines, after the members are stopped, and on a closed client.
// Each schedule runs in a process of its own (inChild). Evidence, not proof.
func TestStreamErrorCells(t *testing.T) {
	for name, sched := range partitionSchedules() {
		t.Run(name, func(t *testing.T) {
			inChild(t, "TestStreamErrorCells", name, func(t *testing.T) { streamErrorCells(t, sched) })
		})
	}
}

func streamErrorCells(t *testing.T, sched []cluster3.Step) {
	lg := zap.NewNop()
	cfg := clusterConfig()
	srvs, brs, ok := cluster3.StartCluster(cfg, lg)
	if !ok {
		t.Fatal("StartCluster failed")
	}
	cli, err := clientv3.New(clientv3.Config{
		Endpoints:            []string{cfg.Bridge1, cfg.Bridge2, cfg.Bridge3},
		DialTimeout:          etcdstart.DialTimeout,
		DialKeepAliveTime:    etcdstart.KeepAliveTime,
		DialKeepAliveTimeout: etcdstart.KeepAliveTimeout,
		Logger:               lg,
	})
	if err != nil {
		t.Fatal(err)
	}
	conn := cli.ActiveConnection()
	se := &streamErrs{seen: map[string]int{}, msgs: map[string]string{}}
	var total time.Duration
	for _, s := range sched {
		total += s.Delay
	}
	go cluster3.Partitioner(srvs, brs, sched)
	run := func(end time.Time, seed int64) {
		var wg sync.WaitGroup
		for w := 0; w < 6; w++ {
			wg.Add(1)
			go func(w int) {
				defer wg.Done()
				rng := rand.New(rand.NewSource(seed + int64(w)))
				for time.Now().Before(end) {
					d := time.Duration(rng.Intn(30)) * time.Millisecond
					var ctx context.Context
					var cancel context.CancelFunc
					switch {
					case w >= 4 && w%2 == 0:
						ctx, cancel = context.WithTimeout(context.Background(), d)
					case w >= 4:
						ctx, cancel = context.WithCancel(context.Background())
						time.AfterFunc(d, cancel)
					default:
						// a stream that does not end by itself: a deadline bounds it
						ctx, cancel = context.WithTimeout(context.Background(), 300*time.Millisecond)
					}
					streamOps(conn, rng, ctx, se)
					cancel()
				}
			}(w)
		}
		wg.Wait()
	}
	run(time.Now().Add(total+2*time.Second), 0)
	// the members stopped: the connections refused
	for _, s := range srvs {
		s.Stop()
	}
	run(time.Now().Add(time.Second), 100)
	// a closed client
	cli.Close()
	rng := rand.New(rand.NewSource(99))
	for i := 0; i < 40; i++ {
		ctx, cancel := context.WithTimeout(context.Background(), 100*time.Millisecond)
		streamOps(conn, rng, ctx, se)
		cancel()
	}
	var ks []string
	for k := range se.seen {
		ks = append(ks, k)
	}
	sort.Strings(ks)
	for _, k := range ks {
		t.Logf("%s: %d (%q)", k, se.seen[k], se.msgs[k])
	}
	if len(se.bad) > 0 {
		for _, b := range se.bad[:min(len(se.bad), 20)] {
			t.Error(b)
		}
		t.Fatal(errors.New("a stream error outside cliStreamErr's shape"))
	}
	if len(ks) == 0 {
		t.Fatal("no stream error seen")
	}
}
