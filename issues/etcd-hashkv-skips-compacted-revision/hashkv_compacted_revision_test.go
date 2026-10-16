// Reproduction of issues/etcd-hashkv-skips-compacted-revision.md.
//
// Package mvcc, file server/storage/mvcc/hashkv_compacted_revision_test.go of go.etcd.io/etcd
// (module go.etcd.io/etcd/server/v3), at the etcd pin of etc/goose.py: 107edf7e4 (branch
// goose-lean of upamanyus/etcd).
//
// Run, in server/:
//
//	GOTOOLCHAIN=go1.27.1 go test ./storage/mvcc -run '^TestHashKVSkipsCompactedRevision$' -count=1
//
// Fails at the pin (shows the finding): HashByRev(7) is the hash of revisions 6..7, not 5..7,
// while a read at revision 5 returns "5".
package mvcc

import (
	"hash/crc32"
	"testing"

	"github.com/stretchr/testify/require"
	"go.uber.org/zap/zaptest"

	"go.etcd.io/etcd/pkg/v3/traceutil"
	"go.etcd.io/etcd/server/v3/lease"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
	"go.etcd.io/etcd/server/v3/storage/schema"
)

func TestHashKVSkipsCompactedRevision(t *testing.T) {
	b, _ := betesting.NewDefaultTmpBackend(t)
	s := NewStore(zaptest.NewLogger(t), b, &lease.FakeLessor{}, StoreConfig{})
	defer cleanup(s, b)
	put := func(v string) { s.Put([]byte("foo"), []byte(v), lease.NoLease) }
	del := func() { s.DeleteRange([]byte("foo"), nil) }
	put("2")
	put("3")
	del() // revisions 2, 3, 4 (tombstone)
	put("5")
	put("6")
	put("7")
	del() // revisions 5, 6, 7, 8 (tombstone)
	put("9")
	done, err := s.Compact(traceutil.TODO(), 5)
	require.NoError(t, err)
	<-done
	r, err := s.Range(t.Context(), []byte("foo"), nil, RangeOptions{Rev: 5})
	require.NoError(t, err)
	require.Equal(t, "5", string(r.KVs[0].Value)) // revision 5 is stored and readable
	got, _, err := s.HashStorage().HashByRev(7)
	require.NoError(t, err)
	hashOf := func(mains map[int64]bool) uint32 { // kvHasher's encoding, no filter
		h := crc32.New(crc32.MakeTable(crc32.Castagnoli))
		h.Write(schema.Key.Name())
		tx := b.ReadTx()
		tx.RLock()
		defer tx.RUnlock()
		tx.UnsafeForEach(schema.Key, func(k, v []byte) error {
			if mains[BytesToRev(k).Main] {
				h.Write(k)
				h.Write(v)
			}
			return nil
		})
		return h.Sum32()
	}
	t.Logf("HashByRev(7) = %d; hash of 5..7 = %d; hash of 6..7 = %d", got.Hash,
		hashOf(map[int64]bool{5: true, 6: true, 7: true}), hashOf(map[int64]bool{6: true, 7: true}))
	require.Equal(t, hashOf(map[int64]bool{5: true, 6: true, 7: true}), got.Hash)
}
