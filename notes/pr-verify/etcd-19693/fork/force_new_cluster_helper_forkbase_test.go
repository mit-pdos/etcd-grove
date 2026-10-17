package etcdserver

import (
	"testing"

	"go.etcd.io/etcd/server/v3/config"
)

func bootstrapWALForTest(t *testing.T, cfg config.ServerConfig) *bootstrappedWAL {
	be, err := bootstrapBackend(cfg, true)
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(be.Close)
	bwal := bootstrapWALFromSnapshot(cfg, be.snapshot, be.ci)
	t.Cleanup(func() { bwal.w.Close() })
	return bwal
}
