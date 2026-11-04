package etcd3

import (
	"context"
	"testing"

	"k8s.io/apiserver/pkg/storage/etcd3/testserver"
)

// TestCompactMissingKey: a compactor's round after compact_rev_key disappeared. The first round
// (expected version 0) writes the key; the key is then deleted (etcd wiped, restored without it,
// or the key removed); the next round, which expects the version it wrote, must not panic.
func TestCompactMissingKey(t *testing.T) {
	client := testserver.RunEtcd(t).Client
	ctx := context.Background()

	version, rev, _, err := Compact(ctx, client, 0, 0)
	if err != nil {
		t.Fatalf("first round: %v", err)
	}
	if _, err := client.Delete(ctx, compactRevKey); err != nil {
		t.Fatalf("Delete: %v", err)
	}

	defer func() {
		if p := recover(); p != nil {
			t.Fatalf("Compact panicked once %s was deleted: %v", compactRevKey, p)
		}
	}()
	if _, _, _, err := Compact(ctx, client, version, rev); err != nil {
		t.Logf("second round: %v", err)
	}
}
