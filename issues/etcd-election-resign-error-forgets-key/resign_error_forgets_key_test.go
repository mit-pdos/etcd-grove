// Reproduction of issues/etcd-election-resign-error-forgets-key.md (etcd-io/etcd#22123).
//
// Package concurrency_test, file client/v3/concurrency/resign_error_forgets_key_test.go of
// go.etcd.io/etcd (module go.etcd.io/etcd/client/v3), at the etcd pin of etc/goose.py: 107edf7e4
// (branch goose-lean of upamanyus/etcd).
//
// Run, in client/v3:
//
//	GOTOOLCHAIN=go1.27.1 go test ./concurrency -run '^TestResignErrorForgetsKey$' -count=1 -v
//
// Fails at the pin (shows the bug): the first Resign fails and leaves the key in etcd, Key() is
// then empty and a second Resign returns nil without issuing a transaction.
package concurrency_test

import (
	"context"
	"errors"
	"testing"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/client/v3/concurrency"
)

// resignLease: KeepAlive returns a channel that stays open (the session is alive).
type resignLease struct{ clientv3.Lease }

func (resignLease) KeepAlive(ctx context.Context, id clientv3.LeaseID) (<-chan *clientv3.LeaseKeepAliveResponse, error) {
	ch := make(chan *clientv3.LeaseKeepAliveResponse)
	go func() { <-ctx.Done(); close(ch) }()
	return ch, nil
}

// resignKV: a store of key names. Transactions apply their Then ops, unless failNext is set: then
// the next Commit fails without reaching the store (as a request whose context is canceled, or a
// connection error, would). Get (Campaign's waitDeletes) finds no older candidate.
type resignKV struct {
	clientv3.KV
	keys     map[string]bool
	txns     int
	failNext bool
}

type resignTxn struct {
	kv  *resignKV
	ops []clientv3.Op
}

func (kv *resignKV) Txn(context.Context) clientv3.Txn { return &resignTxn{kv: kv} }
func (kv *resignKV) Get(context.Context, string, ...clientv3.OpOption) (*clientv3.GetResponse, error) {
	return &clientv3.GetResponse{Header: &pb.ResponseHeader{Revision: 5}}, nil
}
func (t *resignTxn) If(...clientv3.Cmp) clientv3.Txn       { return t }
func (t *resignTxn) Then(ops ...clientv3.Op) clientv3.Txn { t.ops = ops; return t }
func (t *resignTxn) Else(...clientv3.Op) clientv3.Txn     { return t }
func (t *resignTxn) Commit() (*clientv3.TxnResponse, error) {
	t.kv.txns++
	if t.kv.failNext {
		t.kv.failNext = false
		return nil, errors.New("injected: request failed before reaching etcd")
	}
	for _, op := range t.ops {
		if op.IsPut() {
			t.kv.keys[string(op.KeyBytes())] = true
		} else if op.IsDelete() {
			delete(t.kv.keys, string(op.KeyBytes()))
		}
	}
	return &clientv3.TxnResponse{Header: &pb.ResponseHeader{Revision: 5}, Succeeded: true}, nil
}

func TestResignErrorForgetsKey(t *testing.T) {
	kv := &resignKV{keys: map[string]bool{}}
	cli := clientv3.NewCtxClient(context.Background())
	cli.KV, cli.Lease = kv, resignLease{}
	s, err := concurrency.NewSession(cli, concurrency.WithLease(0x10))
	if err != nil {
		t.Fatal(err)
	}
	defer func() { s.Orphan(); <-s.Done() }()
	e := concurrency.NewElection(s, "/el")
	if err := e.Campaign(context.Background(), "v"); err != nil {
		t.Fatal(err)
	}
	key := e.Key()
	t.Logf("leader: Key()=%q; keys: %v", key, kv.keys)

	kv.failNext = true
	err = e.Resign(context.Background())
	t.Logf("first Resign: %v; keys: %v; Key()=%q", err, kv.keys, e.Key())
	if err == nil {
		t.Fatal("expected the injected error")
	}

	n := kv.txns
	err = e.Resign(context.Background()) // the retry the caller would make
	t.Logf("second Resign: %v; txns issued: %d; keys: %v", err, kv.txns-n, kv.keys)
	if err != nil {
		t.Fatal(err)
	}
	if kv.keys[key] {
		t.Errorf("leader key %q left in etcd after a failed Resign and a retry (retry issued %d txns; Key()=%q)",
			key, kv.txns-n, e.Key())
	}
}
