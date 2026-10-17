// Review probe for etcd-io/etcd#21574 (not part of the PR): is `ForceCommit`
// safe on a closed backend, as the persistent contract
// `srvBackendCommits` ({{True}} ForceCommit {{True}}) claims? With a
// pre-commit hook that writes (the server's hook saves the consistent index
// at every commit), it is not.
package backend_test

import (
	"testing"

	"go.uber.org/zap"
	"go.uber.org/zap/zapcore"

	"go.etcd.io/etcd/server/v3/storage/backend"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
	"go.etcd.io/etcd/server/v3/storage/schema"
)

func TestReviewForceCommitAfterClose(t *testing.T) {
	cfg := backend.DefaultBackendConfig(zap.NewNop())
	// lg.Fatal panics instead of exiting, so the test can observe it
	cfg.Logger = zap.New(zapcore.NewNopCore(), zap.WithFatalHook(zapcore.WriteThenPanic))
	cfg.Hooks = backend.NewHooks(func(tx backend.UnsafeReadWriter) {
		tx.UnsafePut(schema.Test, []byte("ci"), []byte("x"))
	})
	be, _ := betesting.NewTmpBackendFromCfg(t, cfg)
	tx := be.BatchTx()
	tx.Lock()
	tx.UnsafeCreateBucket(schema.Test)
	tx.Unlock()
	be.ForceCommit() // open: fine

	if err := be.Close(); err != nil {
		t.Fatal(err)
	}
	defer func() {
		r := recover()
		t.Logf("ForceCommit after Close: recovered %v", r)
		if r == nil {
			t.Log("ForceCommit after Close returned normally")
		} else {
			t.Error("ForceCommit after Close does not return (Fatal/panic): {{True}} ForceCommit {{True}} is false of a closed backend")
		}
	}()
	be.ForceCommit()
}
