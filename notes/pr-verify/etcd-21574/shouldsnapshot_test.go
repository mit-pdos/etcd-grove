// Probe for etcd-io/etcd#21574 (verification, not part of the PR).

package etcdserver

import (
	"testing"

	"go.etcd.io/etcd/server/v3/config"
)

// TestShouldSnapshotToDiskSnapshotCount checks that without a forced snapshot
// a disk snapshot is due only once more than SnapshotCount entries have been
// applied since the last one.
func TestShouldSnapshotToDiskSnapshotCount(t *testing.T) {
	s := &EtcdServer{Cfg: config.ServerConfig{SnapshotCount: 10000}}
	for _, tc := range []struct {
		appliedi, disk uint64
		want           bool
	}{
		{0, 0, false},
		{1, 0, false},
		{10000, 0, false},
		{10001, 0, true},
		{20001, 10001, false},
		{20002, 10001, true},
	} {
		ep := &etcdProgress{appliedi: tc.appliedi, diskSnapshotIndex: tc.disk}
		if got := s.shouldSnapshotToDisk(ep); got != tc.want {
			t.Errorf("appliedi=%d diskSnapshotIndex=%d: shouldSnapshotToDisk=%v, want %v", tc.appliedi, tc.disk, got, tc.want)
		}
	}
}
