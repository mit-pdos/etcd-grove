package etcdserverboot

import (
	"context"
	"time"

	"go.uber.org/zap"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/server/v3/etcdserver/api/v3compactor"
)

type fakeRev struct{}

func (fakeRev) Rev() int64 { return 100 }

type fakeCompactable struct{}

func (fakeCompactable) Compact(ctx context.Context, r *pb.CompactionRequest) (*pb.CompactionResponse, error) {
	return nil, ctx.Err()
}

// REQ etcdserverboot/compactor-lifecycle: the server's compactor is built (or the mode refused with
// an error), run once by start, paused and resumed by leadership changes from the raft loop, stopped
// by Cleanup (twice is harmless), and its loop may call Compact after the stop.
// Users: NewServer (v3compactor.New at a non-zero retention), start (Run), run's ready handler
// (Pause/Resume), Cleanup (Stop).
// Assumes: in periodic mode the retention is at least 10ns in absolute value (V3compactor.bootCfg).
// Specs: compactable_intro, revGetter_intro (the fakes' methods), v3compactor.New.spec, Periodic.Run/Pause/Resume/Stop.spec, Revision.*.spec; laws:
// isCompactor_periodic, isCompactor_revision.
func ReqCompactorLifecycle(lg *zap.Logger) {
	if _, err := v3compactor.New(lg, "bogus", time.Hour, fakeRev{}, fakeCompactable{}); err == nil {
		panic("compactor: an unknown mode accepted")
	}
	for _, mode := range []string{v3compactor.ModePeriodic, v3compactor.ModeRevision} {
		c, err := v3compactor.New(lg, mode, time.Hour, fakeRev{}, fakeCompactable{})
		if err != nil {
			panic("compactor: a known mode refused")
		}
		c.Run()
		c.Pause()
		c.Resume()
		c.Stop()
		c.Stop()
	}
}
