package mvcc

import (
	"context"
	"errors"

	"go.etcd.io/etcd/pkg/v3/traceutil"
	smvcc "go.etcd.io/etcd/server/v3/storage/mvcc"
)

// REQ mvcc/compact: a compaction at a revision above the compaction revision and at most the
// current one succeeds; afterwards reads report it as the first revision, a read below it fails
// with ErrCompacted, at it succeeds; waiting on the channel (a physical compaction) does not panic.
// Users: server/etcdserver/apply/backend.go:66-80 (applierV3backend.Compaction: Compact, then the
// header's revision by a Range), apply/uber_applier.go:97 (ErrCompacted is a success),
// server/etcdserver/v3_server.go (Compact's physical wait on the channel), examples/etcd/putgetc's
// auto-compactor.
// Assumes: the caller holds the store's open token (compactions are not concurrent: etcd compacts
// from its apply thread); crev < rev ≤ cur where crev, cur are the store's (the caller's invariant
// holds the state); rev ≥ 1.
// Specs: store.Compact.spec (KV.Compact.contract: the hook and the commit, compactChanOk),
// store.FirstRev.spec, store.Range.spec.
func ReqCompact(kv smvcc.KV, rev int64, key []byte) {
	ch, err := kv.Compact(traceutil.TODO(), rev)
	if err != nil {
		panic("compact: a compaction in range failed")
	}
	<-ch
	if kv.FirstRev() != rev {
		panic("compact: the first revision is not the compaction's")
	}
	if rev > 1 {
		if _, err := kv.Range(context.TODO(), key, nil, smvcc.RangeOptions{Rev: rev - 1}); !errors.Is(err, smvcc.ErrCompacted) {
			panic("compact: a read below the compaction did not fail")
		}
	}
	if _, err := kv.Range(context.TODO(), key, nil, smvcc.RangeOptions{Rev: rev}); err != nil {
		panic("compact: a read at the compaction revision failed")
	}
}

// REQ mvcc/compact-errors: a compaction at or below the compaction revision fails with
// ErrCompacted (and a channel the caller may wait on), one past the current revision with
// ErrFutureRev and no channel; neither changes the store.
// Users: apply/uber_applier.go:97, api/v3compactor/{periodic,revision}.go (errors.Is(err,
// mvcc.ErrCompacted)), server/etcdserver/v3_server.go (the server's Compact returns the error).
// Assumes: the open token; the store's compaction revision crev ≥ 1 and current revision cur, no
// write meanwhile.
// Specs: store.Compact.spec (its error arms), init.
func ReqCompactErrors(kv smvcc.KV, crev, cur int64) {
	ch, err := kv.Compact(traceutil.TODO(), crev)
	if !errors.Is(err, smvcc.ErrCompacted) || ch == nil {
		panic("compact-errors: a compaction at the compaction revision")
	}
	ch, err = kv.Compact(traceutil.TODO(), cur+1)
	if !errors.Is(err, smvcc.ErrFutureRev) || ch != nil {
		panic("compact-errors: a compaction past the current revision")
	}
	if kv.FirstRev() != crev || kv.Rev() != cur {
		panic("compact-errors: a failed compaction changed the store")
	}
}
