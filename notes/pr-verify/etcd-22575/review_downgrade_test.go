package etcdserver

import (
	"errors"
	"testing"

	"github.com/Masterminds/semver/v3"
	"go.uber.org/zap"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	errorspkg "go.etcd.io/etcd/server/v3/etcdserver/errors"
)

// Ordering: malformed target with no cluster version.
func TestReviewMalformedNilVersionOrdering(t *testing.T) {
	for _, act := range []pb.DowngradeRequest_DowngradeAction{pb.DowngradeRequest_VALIDATE, pb.DowngradeRequest_ENABLE} {
		s := newDowngradeTestServer(t, false)
		resp, err, p := downgradeNoPanic(t, s, &pb.DowngradeRequest{Action: act, Version: "not-a-version"})
		t.Logf("%v malformed, nil cv: resp=%v err=%v panic=%v", act, resp, err, p)
		if p != nil {
			t.Fatalf("panic")
		}
		_ = errors.Is(err, errorspkg.ErrClusterVersionUnavailable)
	}
}

// Masterminds' Minor() is uint64: allowedDowngradeVersion(3.0) = 3.18446744073709551615.0, so a
// cluster at the bootstrap MinClusterVersion 3.0 accepts that absurd downgrade target.
func TestReviewDowngradeTargetUnderflow(t *testing.T) {
	s := newDowngradeTestServer(t, false)
	s.cluster.SetVersion(semver.MustParse("3.0.0"), func(*zap.Logger, *semver.Version) {}, false)
	for _, v := range []string{"3.18446744073709551615", "2.9"} {
		resp, err, p := downgradeNoPanic(t, s, &pb.DowngradeRequest{Action: pb.DowngradeRequest_VALIDATE, Version: v})
		t.Logf("VALIDATE %q at cluster 3.0: resp=%v err=%v panic=%v", v, resp, err, p)
	}
}
