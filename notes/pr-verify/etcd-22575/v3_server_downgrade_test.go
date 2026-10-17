// Copyright 2026 The etcd Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

package etcdserver

import (
	"context"
	"errors"
	"sync"
	"testing"
	"time"

	"github.com/Masterminds/semver/v3"
	"go.uber.org/zap"
	"go.uber.org/zap/zaptest"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/api/v3/version"
	"go.etcd.io/etcd/pkg/v3/idutil"
	"go.etcd.io/etcd/pkg/v3/notify"
	"go.etcd.io/etcd/pkg/v3/wait"
	"go.etcd.io/etcd/server/v3/config"
	"go.etcd.io/etcd/server/v3/etcdserver/api/membership"
	errorspkg "go.etcd.io/etcd/server/v3/etcdserver/errors"
	"go.etcd.io/etcd/server/v3/etcdserver/read"
	serverversion "go.etcd.io/etcd/server/v3/etcdserver/version"
	"go.etcd.io/raft/v3"
)

// readIndexAnswerer answers every ReadIndex at index 0 at once, so that the
// linearizable read loop confirms every read immediately.
type readIndexAnswerer struct{ c chan raft.ReadState }

func (r *readIndexAnswerer) ReadState() <-chan raft.ReadState { return r.c }
func (r *readIndexAnswerer) ReadIndex(_ context.Context, rctx []byte) error {
	r.c <- raft.ReadState{Index: 0, RequestCtx: rctx}
	return nil
}

// newDowngradeTestServer returns a server whose linearizable reads succeed and
// whose cluster has no version yet (the bootstrap window) unless setVersion.
func newDowngradeTestServer(t *testing.T, setVersion bool) *EtcdServer {
	lg := zaptest.NewLogger(t)
	cl := membership.NewCluster(lg)
	if setVersion {
		// the server's own minor version: a downgrade target one minor below is allowed
		sv := semver.MustParse(version.Version)
		cv := semver.New(sv.Major(), sv.Minor(), 0, "", "")
		cl.SetVersion(cv, func(*zap.Logger, *semver.Version) {}, false)
	}
	s := &EtcdServer{
		lgMu:              new(sync.RWMutex),
		lg:                lg,
		Cfg:               config.ServerConfig{Logger: lg, TickMs: 100, ElectionTicks: 10},
		cluster:           cl,
		done:              make(chan struct{}),
		stopping:          make(chan struct{}),
		leaderChanged:     notify.NewNotifier(),
		firstCommitInTerm: notify.NewNotifier(),
		reqIDGen:          idutil.NewGenerator(0, time.Time{}),
		applyWait:         wait.NewTimeList(),
	}
	s.read = read.NewRead(s, &readIndexAnswerer{c: make(chan raft.ReadState, 16)})
	go s.read.LinearizableReadLoop()
	t.Cleanup(func() { close(s.stopping) })
	return s
}

func downgradeNoPanic(t *testing.T, s *EtcdServer, r *pb.DowngradeRequest) (resp *pb.DowngradeResponse, err error, panicked any) {
	defer func() { panicked = recover() }()
	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()
	resp, err = s.Downgrade(ctx, r)
	return resp, err, nil
}

// TestDowngradeClusterVersionUnavailable: during the bootstrap window (no
// cluster version yet) every downgrade action must return
// ErrClusterVersionUnavailable, not panic (etcd-io/etcd#22574).
func TestDowngradeClusterVersionUnavailable(t *testing.T) {
	for _, tc := range []struct {
		name string
		r    *pb.DowngradeRequest
	}{
		{"VALIDATE", &pb.DowngradeRequest{Action: pb.DowngradeRequest_VALIDATE, Version: "3.5"}},
		{"ENABLE", &pb.DowngradeRequest{Action: pb.DowngradeRequest_ENABLE, Version: "3.5"}},
		{"CANCEL", &pb.DowngradeRequest{Action: pb.DowngradeRequest_CANCEL}},
	} {
		t.Run(tc.name, func(t *testing.T) {
			s := newDowngradeTestServer(t, false)
			resp, err, p := downgradeNoPanic(t, s, tc.r)
			if p != nil {
				t.Fatalf("Downgrade(%s) panicked: %v", tc.name, p)
			}
			if resp != nil || !errors.Is(err, errorspkg.ErrClusterVersionUnavailable) {
				t.Fatalf("Downgrade(%s) = %v, %v; want nil, ErrClusterVersionUnavailable", tc.name, resp, err)
			}
		})
	}
}

// TestDowngradeCancelWithoutDowngradeReportsError: cancelling when no
// downgrade is in progress must fail with ErrNoInflightDowngrade (as before
// e47c3c22d, and as the gRPC error map and etcdctl expect); since e47c3c22d the
// error is only logged and the call succeeds.
func TestDowngradeCancelWithoutDowngradeReportsError(t *testing.T) {
	s := newDowngradeTestServer(t, true)
	resp, err, p := downgradeNoPanic(t, s, &pb.DowngradeRequest{Action: pb.DowngradeRequest_CANCEL})
	if p != nil {
		t.Fatalf("Downgrade(CANCEL) panicked: %v", p)
	}
	if !errors.Is(err, serverversion.ErrNoInflightDowngrade) {
		t.Fatalf("Downgrade(CANCEL) with no downgrade in progress = %v, %v; want ErrNoInflightDowngrade", resp, err)
	}
}
