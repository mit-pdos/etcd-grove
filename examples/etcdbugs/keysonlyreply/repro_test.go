// Package keysonlyreply reproduces issues/etcd-txn-keysonly-reply-alloc-panic.md: a client Txn
// built from nested transactions of keys-only whole-range reads makes a member produce a reply
// whose protobuf encoding exceeds 2^48 bytes, and the gRPC codec's proto.Marshal allocates that
// many bytes with make() before any size check, so Go panics with "makeslice: cap out of range"
// in the gRPC server's goroutine. Nothing recovers it: the member process exits.
//
// Why it is cheap on the server. The leaf reads are keys-only ranges over all keys. The keys-only
// path returns the index's own key slices (mvcc/index.go Range, mvcc/kvstore_txn.go rangeKeys'
// FastKeysOnly branch), so every one of the (leaves x keys) KeyValues of the reply re-references
// the same few key buffers. The reply's heap is only (leaves x keys x ~136 B per KeyValue struct
// + the few key buffers), while its *encoded* size is (leaves x keys x key-bytes): a few GB of
// heap encodes to > 2^48 bytes. checkTxnRequest (v3rpc/key.go) budgets maxTxnOps *per nesting
// level*, so nesting multiplies the leaf count: a tree of fan-outs summing to <= maxTxnOps (128)
// has (product of the fan-outs) leaves.
//
// What the member actually does with it. A *nested* Txn is not recognised as read-only
// (txn.IsTxnReadonly inspects only the top level, whose ops are RequestTxn, not RequestRange), so
// it is proposed through raft, committed to the WAL, and the *apply loop* runs txn.Txn/executeTxn
// to build the reply on every member. The gRPC handler waits for the apply result under the
// server's ReqTimeout (= 5s + 2 * election-timeout). The makeslice panic fires when the handler
// receives the result and marshals it for the wire. With etcd's default timing (election 1s,
// ReqTimeout 7s) a reply large enough to exceed 2^48 takes longer than 7s to build, so the client
// times out first and the handler never marshals -- the apply loop still builds (and discards)
// the multi-GB reply on every member, and replays it on every restart. To observe the crash this
// test widens the election timeout (KEYSONLY_TICKMS, KEYSONLY_ELECTION) so ReqTimeout exceeds the
// build time; a value well within etcd's allowed range for high-latency deployments.
//
// The member runs in a subprocess (this test binary, re-executed with KEYSONLY_SERVER set), so
// that its panic does not take the test down; the test is the client, and checks the member's
// exit and output for the panic. It is opt-in (it needs about 11 GiB of memory and a minute):
//
//	KEYSONLY_REPRO=1 go test -v -run TestKeysOnlyReplyPanic -timeout 20m .
//
// KEYSONLY_MAXREQ overrides the member's --max-request-bytes (default 32 MiB), KEYSONLY_FANOUT the
// nesting fan-outs (comma-separated, summing to <= 128), KEYSONLY_TICKMS/KEYSONLY_ELECTION the
// member's raft tick and election ticks (default 500 ms x 30 = a 15 s election timeout, so
// ReqTimeout is 35 s), KEYSONLY_LOG=1 turns on the member's production logger.
package keysonlyreply

import (
	"bufio"
	"context"
	"fmt"
	"io"
	"math"
	"math/bits"
	"net"
	"os"
	"os/exec"
	"strconv"
	"strings"
	"sync"
	"syscall"
	"testing"
	"time"

	"go.uber.org/zap"

	"go.etcd.io/etcd/client/pkg/v3/types"
	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/server/v3/config"
	"go.etcd.io/etcd/server/v3/etcdserver"
	"go.etcd.io/etcd/server/v3/etcdserver/api/v3rpc"
	"go.etcd.io/etcd/server/v3/features"
)

const (
	peerAddr   = "127.0.0.1:23901"
	clientAddr = "127.0.0.1:23902"
	// grpcOverheadBytes of server/config/config.go: the server's gRPC receive limit is
	// MaxRequestBytes plus this.
	grpcOverhead = 512 * 1024
	nKeys        = 4
)

func envUint(name string, def uint) uint {
	if v := os.Getenv(name); v != "" {
		n, err := strconv.ParseUint(v, 10, 64)
		if err != nil {
			panic(err)
		}
		return uint(n)
	}
	return def
}

func maxRequestBytes() uint { return envUint("KEYSONLY_MAXREQ", 32<<20) }

// TestKeysOnlyReplyServer is the member's process: one member of a new cluster, configured as
// examples/common's newServer but for MaxRequestBytes and the raft timing, its gRPC API served by
// v3rpc.Server as etcd's embed does (no TLS, no extra interceptor). It prints READY and serves
// until it dies.
func TestKeysOnlyReplyServer(t *testing.T) {
	if os.Getenv("KEYSONLY_SERVER") == "" {
		t.Skip("the member's process, run by TestKeysOnlyReplyPanic")
	}
	lg := zap.NewNop()
	if os.Getenv("KEYSONLY_LOG") != "" {
		lg, _ = zap.NewProduction()
	}
	name := "m"
	peer := types.URLs{{Scheme: "http", Host: peerAddr}}
	cfg := config.ServerConfig{
		Name:                name,
		DataDir:             os.Getenv("KEYSONLY_DATADIR"),
		InitialPeerURLsMap:  types.URLsMap{name: peer},
		PeerURLs:            peer,
		ClientURLs:          types.URLs{{Scheme: "http", Host: clientAddr}},
		InitialClusterToken: name,
		NewCluster:          true,
		// a wide election timeout so the handler's ReqTimeout (5s + 2*election) exceeds the time
		// the apply loop takes to build the reply; see the package comment
		TickMs:        envUint("KEYSONLY_TICKMS", 500),
		ElectionTicks: int(envUint("KEYSONLY_ELECTION", 30)),
		SnapshotCount: etcdserver.DefaultSnapshotCount,
		// etcd's defaults (embed.DefaultMaxTxnOps, embed's warning duration)
		MaxTxnOps:            128,
		MaxRequestBytes:      maxRequestBytes(),
		WarningApplyDuration: 100 * time.Millisecond,
		Logger:               lg,
		ServerFeatureGate:    features.NewDefaultServerFeatureGate(name, lg),
	}
	s, err := etcdserver.NewServer(cfg)
	if err != nil {
		t.Fatal(err)
	}
	s.Start()
	gs := v3rpc.Server(s, nil, nil)
	l, err := net.Listen("tcp", clientAddr)
	if err != nil {
		t.Fatal(err)
	}
	<-s.ReadyNotify()
	fmt.Println("READY")
	gs.Serve(l)
}

// leafOp is the one leaf read: every key, keys only (["\x00", <from key>): from "\x00" on).
func leafOp() clientv3.Op {
	return clientv3.OpGet("\x00", clientv3.WithFromKey(), clientv3.WithKeysOnly())
}

// tree is a transaction whose levels have the given fan-outs: the top level's Then holds fanout[0]
// transactions, ..., the last level fanout[len-1] leaf reads. checkTxnRequest gives each level the
// budget maxTxnOps minus its ancestors' widths, so the sum of the fan-outs must be at most
// maxTxnOps (128); the number of leaves is their product.
func tree(fanout []int) []clientv3.Op {
	if len(fanout) == 1 {
		ops := make([]clientv3.Op, fanout[0])
		for i := range ops {
			ops[i] = leafOp()
		}
		return ops
	}
	sub := tree(fanout[1:])
	ops := make([]clientv3.Op, fanout[0])
	for i := range ops {
		// the subtree's ops are shared (clientv3 copies nothing; the request encodes every copy)
		ops[i] = clientv3.OpTxn(nil, sub, nil)
	}
	return ops
}

func TestKeysOnlyReplyPanic(t *testing.T) {
	if os.Getenv("KEYSONLY_REPRO") == "" {
		t.Skip("set KEYSONLY_REPRO=1: needs about 11 GiB of memory and a minute")
	}
	maxReq := maxRequestBytes()
	// keys as long as a Put's raft request allows (MaxRequestBytes bounds the marshalled
	// InternalRaftRequest, which adds a few dozen bytes)
	keyLen := int(maxReq) - 1024
	// leaves: enough that nKeys * keyLen * leaves > 2^48 with a little margin
	fanout := []int{20, 20, 20, 20, 16} // sum 96 <= 128, 2,560,000 leaves
	if f := os.Getenv("KEYSONLY_FANOUT"); f != "" {
		fanout = nil
		for _, x := range strings.Split(f, ",") {
			n, _ := strconv.Atoi(x)
			fanout = append(fanout, n)
		}
	}
	leaves, sum := 1, 0
	for _, f := range fanout {
		leaves *= f
		sum += f
	}
	hi, lo := bits.Mul64(uint64(leaves), uint64(nKeys*keyLen))
	t.Logf("max-request-bytes %d, %d keys of %d bytes, fan-outs %v (sum %d), %d leaves: reply key bytes >= %d (hi %d) ~ 2^%.2f",
		maxReq, nKeys, keyLen, fanout, sum, leaves, lo, hi, math.Log2(float64(leaves)*float64(nKeys*keyLen)))

	dataDir := t.TempDir() + "/m.etcd"
	cmd := exec.Command(os.Args[0], "-test.run", "^TestKeysOnlyReplyServer$", "-test.v")
	cmd.Env = append(os.Environ(), "KEYSONLY_SERVER=1", "KEYSONLY_DATADIR="+dataDir)
	stdout, err := cmd.StdoutPipe()
	if err != nil {
		t.Fatal(err)
	}
	var mu sync.Mutex
	var stderr strings.Builder
	var sink io.Writer = &stderr
	if d := os.Getenv("KEYSONLY_DUMP"); d != "" {
		f, ferr := os.Create(d)
		if ferr != nil {
			t.Fatal(ferr)
		}
		defer f.Close()
		sink = io.MultiWriter(&stderr, f)
	}
	cmd.Stderr = writerFunc(func(p []byte) (int, error) {
		mu.Lock()
		defer mu.Unlock()
		return sink.Write(p)
	})
	if err := cmd.Start(); err != nil {
		t.Fatal(err)
	}
	ready := make(chan struct{})
	var out strings.Builder
	outDone := make(chan struct{})
	go func() {
		sc := bufio.NewScanner(stdout)
		sc.Buffer(make([]byte, 1<<20), 1<<30)
		for sc.Scan() {
			line := sc.Text()
			out.WriteString(line + "\n")
			if line == "READY" {
				close(ready)
			}
		}
		io.Copy(io.Discard, stdout)
		close(outDone)
	}()
	select {
	case <-ready:
	case <-time.After(90 * time.Second):
		cmd.Process.Kill()
		t.Fatal("the member did not start")
	}

	cli, err := clientv3.New(clientv3.Config{
		Endpoints:          []string{clientAddr},
		DialTimeout:        5 * time.Second,
		Logger:             zap.NewNop(),
		MaxCallSendMsgSize: int(maxReq) + grpcOverhead,
		MaxCallRecvMsgSize: 1 << 30,
	})
	if err != nil {
		t.Fatal(err)
	}
	defer cli.Close()

	for i := 0; i < nKeys; i++ {
		key := make([]byte, keyLen)
		key[0] = byte('a' + i)
		var perr error
		for attempt := 0; attempt < 4; attempt++ {
			ctx, cancel := context.WithTimeout(context.Background(), 60*time.Second)
			_, perr = cli.Put(ctx, string(key), "")
			cancel()
			if perr == nil {
				break
			}
			t.Logf("put %d attempt %d: %v", i, attempt, perr)
			time.Sleep(time.Second)
		}
		if perr != nil {
			t.Fatalf("put %d: %v", i, perr)
		}
	}
	t.Logf("put %d keys of %d bytes", nKeys, keyLen)

	ops := tree(fanout)
	ctx, cancel := context.WithTimeout(context.Background(), 10*time.Minute)
	start := time.Now()
	resp, err := cli.Txn(ctx).Then(ops...).Commit()
	cancel()
	t.Logf("Txn returned after %v: resp=%v err=%v", time.Since(start), resp != nil, err)

	waitErr := make(chan error, 1)
	go func() { waitErr <- cmd.Wait() }()
	var werr error
	select {
	case werr = <-waitErr:
	case <-time.After(60 * time.Second):
		cmd.Process.Signal(syscall.SIGQUIT) // a goroutine dump, then kill it
		select {
		case werr = <-waitErr:
		case <-time.After(10 * time.Second):
			cmd.Process.Kill()
			werr = <-waitErr
		}
		t.Logf("the member was still running; killed")
	}
	<-outDone
	if ru, ok := cmd.ProcessState.SysUsage().(*syscall.Rusage); ok {
		t.Logf("member's peak RSS: %.2f GiB", float64(ru.Maxrss)/(1<<20))
	}
	mu.Lock()
	se := stderr.String()
	mu.Unlock()
	t.Logf("member exited: %v", werr)
	t.Logf("member's output (first 3000 bytes of stderr):\n%s", head(se, 3000))
	if !strings.Contains(se, "makeslice") {
		t.Fatalf("no makeslice panic in the member's output; the member did not crash on the reply")
	}
	t.Logf("the member crashed marshalling the reply (makeslice), as expected")
}

type writerFunc func([]byte) (int, error)

func (f writerFunc) Write(p []byte) (int, error) { return f(p) }

func head(s string, n int) string {
	if len(s) <= n {
		return s
	}
	return s[:n] + "\n..."
}
