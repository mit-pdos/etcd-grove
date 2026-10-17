// Review probe for etcd-io/etcd#21574 (not part of the PR).
//
// After a cluster-version downgrade, which WAL entries would a member restarted
// on the older binary replay? It replays every entry after the latest WAL
// snapshot record, and the older binary's RaftCluster.SetVersion panics
// (MustDetectDowngrade) on a ClusterVersionSet entry naming the newer version,
// whatever shouldApplyV3 is; the storage-version downgrade
// (schema.UnsafeMigrate) also checks MinimalEtcdVersion of exactly those
// entries. The old code forced a disk snapshot at the downgrade entry, so the
// newer-version ClusterVersionSet entry is before the latest snapshot record.
//
// The test is written against both the gogoproto (upstream PR head) and the
// protobuf-go v2 (fork) WAL types, through reflection.
package embed

import (
	"bytes"
	"context"
	"fmt"
	"net/url"
	"os"
	"path/filepath"
	"reflect"
	"testing"
	"time"

	"github.com/stretchr/testify/require"
	"go.uber.org/zap/zaptest"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/api/v3/version"
	"go.etcd.io/etcd/server/v3/storage/wal"
)

func reviewField(v any, name string) reflect.Value {
	rv := reflect.Indirect(reflect.ValueOf(v))
	f := rv.FieldByName(name)
	if f.Kind() == reflect.Ptr {
		f = f.Elem()
	}
	return f
}

func TestReviewDowngradeWALReplay(t *testing.T) {
	cfg := NewConfig()
	var urls []url.URL
	for i := 0; i < 2; i++ {
		u, _ := url.Parse(fmt.Sprintf("unix://localhost:%d%06d", os.Getpid(), 7100+i))
		urls = append(urls, *u)
	}
	cfg.ListenClientUrls, cfg.AdvertiseClientUrls = urls[:1], urls[:1]
	cfg.ListenPeerUrls, cfg.AdvertisePeerUrls = urls[1:], urls[1:]
	cfg.InitialCluster = "default=" + urls[1].String()
	cfg.Dir = t.TempDir()

	e, err := StartEtcd(cfg)
	require.NoError(t, err)
	closed := false
	defer func() {
		if !closed {
			e.Close()
		}
	}()
	<-e.Server.ReadyNotify()

	cur := version.Cluster(version.Version) // "3.8" on the fork, "3.7" on the PR head
	var major, minor int
	fmt.Sscanf(cur, "%d.%d", &major, &minor)
	target := fmt.Sprintf("%d.%d.0", major, minor-1)
	curFull := fmt.Sprintf("%d.%d.0", major, minor)

	deadline := time.Now().Add(20 * time.Second)
	for e.Server.ClusterVersion() == nil || version.Cluster(e.Server.ClusterVersion().String()) != cur {
		require.True(t, time.Now().Before(deadline), "cluster version never reached %s", cur)
		time.Sleep(100 * time.Millisecond)
	}
	ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
	defer cancel()
	_, err = e.Server.Downgrade(ctx, &pb.DowngradeRequest{Action: pb.DowngradeRequest_ENABLE, Version: target})
	require.NoError(t, err)
	deadline = time.Now().Add(30 * time.Second)
	for version.Cluster(e.Server.ClusterVersion().String()) != version.Cluster(target) {
		require.True(t, time.Now().Before(deadline), "cluster version never downgraded to %s", target)
		time.Sleep(100 * time.Millisecond)
	}
	// a few batches after the downgrade
	for i := 0; i < 3; i++ {
		_, err := e.Server.Put(ctx, &pb.PutRequest{Key: []byte("k"), Value: []byte{byte(i)}})
		require.NoError(t, err)
	}
	e.Close()
	closed = true

	lg := zaptest.NewLogger(t)
	waldir := filepath.Join(cfg.Dir, "member", "wal")
	snaps, err := wal.ValidSnapshotEntries(lg, waldir)
	require.NoError(t, err)
	sv := reflect.ValueOf(snaps)
	last := sv.Index(sv.Len() - 1).Interface()
	lastIdx := reviewField(last, "Index").Uint()

	// open the WAL from the beginning (a zero snapshot of OpenForRead's type)
	openT := reflect.TypeOf(wal.OpenForRead).In(2)
	var zero reflect.Value
	if openT.Kind() == reflect.Ptr {
		zero = reflect.New(openT.Elem())
	} else {
		zero = reflect.Zero(openT)
	}
	out := reflect.ValueOf(wal.OpenForRead).Call([]reflect.Value{reflect.ValueOf(lg), reflect.ValueOf(waldir), zero})
	require.Nil(t, out[1].Interface())
	w := out[0].Interface().(*wal.WAL)
	defer w.Close()
	_, _, ents, err := w.ReadAll()
	require.NoError(t, err)

	ev := reflect.ValueOf(ents)
	var newerAfter, newerBefore []uint64
	var downgradeIdx uint64
	for i := 0; i < ev.Len(); i++ {
		ent := ev.Index(i)
		if ent.Kind() != reflect.Ptr {
			ent = ent.Addr()
		}
		idx := reviewField(ent.Interface(), "Index").Uint()
		data := reviewField(ent.Interface(), "Data").Bytes()
		// a ClusterVersionSet{Ver: curFull} entry; DowngradeInfoSet/ClusterVersionSet of the target name target
		if bytes.Contains(data, []byte(curFull)) {
			if idx > lastIdx {
				newerAfter = append(newerAfter, idx)
			} else {
				newerBefore = append(newerBefore, idx)
			}
		}
		if bytes.Contains(data, []byte(target)) {
			downgradeIdx = idx
		}
	}
	t.Logf("version %s -> %s; WAL snapshot records %d, latest at index %d; last entry naming %s at %d; entries naming %s before it: %v, after it (replayed on restart): %v",
		cur, target, sv.Len(), lastIdx, target, downgradeIdx, curFull, newerBefore, newerAfter)
	require.Empty(t, newerAfter, "a member restarted on the %s binary replays ClusterVersionSet{%s} (MustDetectDowngrade panics), and the storage-version downgrade sees it in the WAL", target, curFull)
}
