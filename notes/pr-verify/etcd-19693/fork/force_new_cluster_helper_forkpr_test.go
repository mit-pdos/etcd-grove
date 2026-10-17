package etcdserver

import (
	"testing"

	"go.etcd.io/etcd/server/v3/config"
)

func bootstrapWALForTest(t *testing.T, cfg config.ServerConfig) *bootstrappedWAL {
	be, err := bootstrapBackend(cfg)
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(be.Close)
	bwal := bootstrapWALFromBackend(cfg, be.be)
	t.Cleanup(func() { bwal.w.Close() })
	return bwal
}
