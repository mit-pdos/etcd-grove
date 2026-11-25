// Package memberslearner is the Go evidence for `membership.membersOf_decode`'s learner flag
// (route B, 2026-11-25; Proof/go_etcd_io/etcd/server/v3/etcdserver/InvRest.lean): a member saved
// as `MustSaveMemberToBackend` saves it (`json.Marshal` of the `*Member` under
// `BackendMemberKey(m.ID)`) reads back through the real `snapshotmeta.ReadMembers` (what
// `readMembersFromBackend` calls) with the same id and `IsLearner`, also when its peer URL is not
// valid UTF-8 (which `json.Marshal` coerces, so the peer URL alone reads back changed).
package memberslearner

import (
	"bytes"
	"encoding/json"
	"testing"

	"go.etcd.io/etcd/client/pkg/v3/types"
	"go.etcd.io/etcd/server/v3/etcdserver/api/membership"
	"go.etcd.io/etcd/server/v3/storage/backend"
	"go.etcd.io/etcd/server/v3/storage/schema"
	"go.etcd.io/etcd/server/v3/storage/schema/snapshotmeta"
	"go.uber.org/zap"
)

// bucketReader is a `backend.UnsafeReader` over one bucket's records, in order.
type bucketReader struct {
	keys, vals [][]byte
}

func (r *bucketReader) UnsafeRange(_ backend.Bucket, key, _ []byte, _ int64) ([][]byte, [][]byte) {
	for i, k := range r.keys {
		if bytes.Equal(k, key) {
			return [][]byte{k}, [][]byte{r.vals[i]}
		}
	}
	return nil, nil
}

func (r *bucketReader) UnsafeForEach(_ backend.Bucket, visitor func(k, v []byte) error) error {
	for i := range r.keys {
		if err := visitor(r.keys[i], r.vals[i]); err != nil {
			return err
		}
	}
	return nil
}

func TestLearnerFlagRoundTrip(t *testing.T) {
	saved := []*membership.Member{
		{ID: types.ID(7), RaftAttributes: membership.RaftAttributes{PeerURLs: []string{"http://a:2380"}, IsLearner: true}},
		{ID: types.ID(8), RaftAttributes: membership.RaftAttributes{PeerURLs: []string{"http://b:2380"}}},
		{ID: types.ID(9), RaftAttributes: membership.RaftAttributes{PeerURLs: []string{"http://\xff:2380"}, IsLearner: true}},
		{ID: types.ID(10), RaftAttributes: membership.RaftAttributes{PeerURLs: []string{"http://\xfe:2380"}}},
	}
	r := &bucketReader{}
	for _, m := range saved {
		v, err := json.Marshal(m) // MustSaveMemberToBackend's value
		if err != nil {
			t.Fatal(err)
		}
		r.keys = append(r.keys, schema.BackendMemberKey(m.ID))
		r.vals = append(r.vals, v)
	}
	read, err := snapshotmeta.ReadMembers(zap.NewNop(), r, schema.Members)
	if err != nil {
		t.Fatal(err)
	}
	if len(read) != len(saved) {
		t.Fatalf("read %d members, saved %d", len(read), len(saved))
	}
	for _, m := range saved {
		got, ok := read[m.ID]
		if !ok || got == nil {
			t.Fatalf("member %v not read back", m.ID)
		}
		if got.ID != m.ID || got.IsLearner != m.IsLearner {
			t.Fatalf("member %v: saved (id %v, learner %v), read (id %v, learner %v)",
				m.ID, m.ID, m.IsLearner, got.ID, got.IsLearner)
		}
		t.Logf("member %v: learner %v read back; peer URL %q read back as %q",
			m.ID, got.IsLearner, m.PeerURLs[0], got.PeerURLs[0])
	}
}
