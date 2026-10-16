// Reproduction of issues/etcd-election-campaign-error-orphan-key.md.
//
// Package concurrency_test, file client/v3/concurrency/campaign_error_key_test.go of
// go.etcd.io/etcd (module go.etcd.io/etcd/client/v3), at the etcd pin of etc/goose.py: 107edf7e4
// (branch goose-lean of upamanyus/etcd).
//
// Run, in client/v3:
//
//	GOTOOLCHAIN=go1.27.1 go test ./concurrency -run '^TestCampaignErrorLeavesKeyResignNoop$' -count=1
//
// Fails at the pin (shows the bug): "key map[/el/10:true] left in etcd; Resign issued 0 txns;
// Key()="/el/10"".
package concurrency_test

import (
	"context"
	"errors"
	"testing"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/client/v3/concurrency"
)

// fakeLease: KeepAlive returns a channel that stays open (the session is alive).
type fakeLease struct{ clientv3.Lease }

func (fakeLease) KeepAlive(ctx context.Context, id clientv3.LeaseID) (<-chan *clientv3.LeaseKeepAliveResponse, error) {
	ch := make(chan *clientv3.LeaseKeepAliveResponse)
	go func() { <-ctx.Done(); close(ch) }()
	return ch, nil
}

// fakeKV: a store of key names. Transactions apply their Then ops; Get (waitDeletes' first
// call) fails with a non-context error, as a compaction error would.
type fakeKV struct {
	clientv3.KV
	keys map[string]bool
	txns int
}

type fakeTxn struct {
	kv  *fakeKV
	ops []clientv3.Op
}

func (kv *fakeKV) Txn(context.Context) clientv3.Txn { return &fakeTxn{kv: kv} }
func (kv *fakeKV) Get(context.Context, string, ...clientv3.OpOption) (*clientv3.GetResponse, error) {
	return nil, errors.New("injected: mvcc: required revision has been compacted")
}
func (t *fakeTxn) If(...clientv3.Cmp) clientv3.Txn       { return t }
func (t *fakeTxn) Then(ops ...clientv3.Op) clientv3.Txn { t.ops = ops; return t }
func (t *fakeTxn) Else(...clientv3.Op) clientv3.Txn     { return t }
func (t *fakeTxn) Commit() (*clientv3.TxnResponse, error) {
	t.kv.txns++
	for _, op := range t.ops {
		if op.IsPut() {
			t.kv.keys[string(op.KeyBytes())] = true
		} else if op.IsDelete() {
			delete(t.kv.keys, string(op.KeyBytes()))
		}
	}
	return &clientv3.TxnResponse{Header: &pb.ResponseHeader{Revision: 5}, Succeeded: true}, nil
}

func TestCampaignErrorLeavesKeyResignNoop(t *testing.T) {
	kv := &fakeKV{keys: map[string]bool{}}
	cli := clientv3.NewCtxClient(context.Background())
	cli.KV, cli.Lease = kv, fakeLease{}
	s, err := concurrency.NewSession(cli, concurrency.WithLease(0x10))
	if err != nil {
		t.Fatal(err)
	}
	defer func() { s.Orphan(); <-s.Done() }()
	e := concurrency.NewElection(s, "/el")
	err = e.Campaign(context.Background(), "v")
	t.Logf("Campaign: %v; keys after Campaign: %v", err, kv.keys)
	if err == nil {
		t.Fatal("expected an error")
	}
	n := kv.txns
	if err := e.Resign(context.Background()); err != nil {
		t.Fatal(err)
	}
	if len(kv.keys) != 0 {
		t.Errorf("key %v left in etcd; Resign issued %d txns; Key()=%q", kv.keys, kv.txns-n, e.Key())
	}
}
