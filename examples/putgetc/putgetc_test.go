package putgetc

import (
	"context"
	"errors"
	"testing"
	"time"

	"go.etcd.io/etcd/api/v3/v3rpc/rpctypes"
	clientv3 "go.etcd.io/etcd/client/v3"
	"go.uber.org/zap"
)

// TestPutGetC runs Main once, in a fresh data directory (the member's DataDir is relative). Main
// returns without its check if a step fails, so the test then asks the member Main left running
// whether the Put took effect.
func TestPutGetC(t *testing.T) {
	t.Chdir(t.TempDir())
	Main()

	cli, err := clientv3.New(clientv3.Config{Endpoints: []string{clientAddr}, Logger: zap.NewNop()})
	if err != nil {
		t.Fatal(err)
	}
	defer cli.Close()
	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()
	resp, err := cli.Get(ctx, "k")
	if err != nil {
		t.Fatal(err)
	}
	if len(resp.Kvs) != 1 || string(resp.Kvs[0].Value) != "v" {
		t.Fatalf("Main's Put did not take effect: %v", resp.Kvs)
	}
	// the compactor runs: within a few periods it compacts the Put's revision (the store's
	// revision a period before), so a read at the revision before it fails with ErrCompacted
	deadline := time.Now().Add(5 * time.Second)
	for {
		rctx, rcancel := context.WithTimeout(context.Background(), 5*time.Second)
		_, err := cli.Get(rctx, "k", clientv3.WithRev(resp.Header.Revision-1))
		rcancel()
		if errors.Is(err, rpctypes.ErrCompacted) {
			break
		}
		if err != nil {
			t.Fatal(err)
		}
		if time.Now().After(deadline) {
			t.Fatal("the periodic compactor did not compact within 5s")
		}
		time.Sleep(10 * time.Millisecond)
	}
}
