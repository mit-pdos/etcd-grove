// Package leasettlrow holds the Go checks of the axiom review of EtcdServer.leaseTimeToLive.spec's
// E2 revision 5 (notes/axiom-review/lease-ttl-row.md): tests only, no Goose project. Each test
// starts one member of a new single-member cluster as examples/lib/etcdstart's NewMember does (its
// peer URL served by the member's raft handler only, so /leases/internal answers 404), in a fresh
// directory, and calls (*EtcdServer).LeaseTimeToLive, which calls leaseTimeToLive.
package leasettlrow

import (
	"context"
	"errors"
	"fmt"
	"sync"
	"sync/atomic"
	"testing"
	"time"

	"go.uber.org/zap"
	"google.golang.org/protobuf/proto"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/client/pkg/v3/types"
	"go.etcd.io/etcd/server/v3/etcdserver"
	"go.etcd.io/etcd/server/v3/lease"
	"go.etcd.io/raft/v3/raftpb"

	"github.com/mit-pdos/etcd-grove/examples/lib/etcdstart"
)

// The client URL (not served) and the peer ports: one per member, since NewMember never closes
// its peer listener.
const (
	clientAddr = "127.0.0.1:23992"
	peerPort0  = 23993 // 23993-23999
)

// newMember builds (not starts) the one member of a new cluster, in a fresh directory.
func newMember(t *testing.T, name string, port int) *etcdserver.EtcdServer {
	t.Chdir(t.TempDir())
	peerAddr := fmt.Sprintf("127.0.0.1:%d", port)
	peer := types.URLs{{Scheme: "http", Host: peerAddr}}
	s, err := etcdstart.NewMember(name, peer, peerAddr, clientAddr, types.URLsMap{name: peer}, name,
		etcdstart.NoSnapCount, etcdstart.NoSnapCatchUp, zap.NewNop())
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(s.Stop)
	return s
}

func waitLeader(t *testing.T, s *etcdserver.EtcdServer) {
	for i := 0; i < 1000; i++ {
		if s.Leader() == s.MemberID() {
			return
		}
		time.Sleep(10 * time.Millisecond)
	}
	t.Fatal("no leader")
}

func ttl(s *etcdserver.EtcdServer, id int64) (*pb.LeaseTimeToLiveResponse, error) {
	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()
	return s.LeaseTimeToLive(ctx, &pb.LeaseTimeToLiveRequest{ID: id})
}

// TestStartupWindow: TimeToLive called before the member is leader (the forwarded path) while a
// lease is granted as soon as the member is leader. The row's argument: a forwarded call saw the
// lessor empty at its isLeader() read. Checked: no call that began after the grant returned
// answers not found or a GrantedTTL other than the grant's.
func TestStartupWindow(t *testing.T) {
	for round := 0; round < 5; round++ {
		t.Run("", func(t *testing.T) {
			s := newMember(t, "ttlwin", peerPort0+round)
			const id = 7
			var granted atomic.Bool
			var bad, fwdNotFound, total atomic.Int64
			var wg sync.WaitGroup
			s.Start()
			for g := 0; g < 8; g++ {
				wg.Add(1)
				go func() {
					defer wg.Done()
					for i := 0; i < 40; i++ {
						after := granted.Load()
						r, err := ttl(s, id)
						total.Add(1)
						if errors.Is(err, lease.ErrLeaseNotFound) {
							if after {
								bad.Add(1)
								t.Errorf("not found for a live lease granted before the call")
							} else {
								fwdNotFound.Add(1)
							}
						} else if err == nil && after && r.GrantedTTL != 60 {
							bad.Add(1)
							t.Errorf("GrantedTTL %d, want 60", r.GrantedTTL)
						}
						time.Sleep(5 * time.Millisecond)
					}
				}()
			}
			waitLeader(t, s)
			ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
			_, err := s.LeaseGrant(ctx, &pb.LeaseGrantRequest{ID: id, TTL: 60})
			cancel()
			if err != nil {
				t.Fatal(err)
			}
			granted.Store(true)
			wg.Wait()
			t.Logf("calls %d, not found before the grant %d, violations %d", total.Load(), fwdNotFound.Load(), bad.Load())
		})
	}
}

// TestSelfMoveLeader: MoveLeader to itself (the one member, which MoveLeader's member check
// admits) and to a non-member, concurrently with TimeToLive of a live lease: the sole voter keeps
// its leadership; no not-found answer.
func TestSelfMoveLeader(t *testing.T) {
	s := newMember(t, "ttlmove", peerPort0+5)
	s.Start()
	waitLeader(t, s)
	const id = 9
	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()
	if _, err := s.LeaseGrant(ctx, &pb.LeaseGrantRequest{ID: id, TTL: 60}); err != nil {
		t.Fatal(err)
	}
	stop := make(chan struct{})
	go func() {
		for {
			select {
			case <-stop:
				return
			default:
			}
			mctx, mcancel := context.WithTimeout(context.Background(), 200*time.Millisecond)
			_ = s.MoveLeader(mctx, uint64(s.MemberID()), uint64(s.MemberID()))
			_ = s.MoveLeader(mctx, uint64(s.MemberID()), 0xdead)
			mcancel()
		}
	}()
	for i := 0; i < 2000; i++ {
		r, err := ttl(s, id)
		if err != nil || r.GrantedTTL != 60 {
			t.Fatalf("call %d: %v %v", i, r, err)
		}
	}
	close(stop)
}

// TestOutsiderDeposes: the margin the row's docstring names (the trusted transport contract,
// decisions.md D21b (A)), made concrete. A higher-term MsgApp from a non-member id, handed to the
// member's Process (what its raft handler does with any POST to /raft carrying the cluster id and
// a compatible version: http.go's pipelineHandler), makes the sole voter a follower; a TimeToLive
// called then forwards, and after the member re-elects itself it asks its own peer URL, whose 404
// it reads as ErrLeaseNotFound -- for a lease that is live. Not a refutation of the spec (the
// contract excludes the message); evidence that the contract is load-bearing.
func TestOutsiderDeposes(t *testing.T) {
	s := newMember(t, "ttlout", peerPort0+6)
	s.Start()
	waitLeader(t, s)
	const id = 11
	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()
	if _, err := s.LeaseGrant(ctx, &pb.LeaseGrantRequest{ID: id, TTL: 60}); err != nil {
		t.Fatal(err)
	}
	m := &raftpb.Message{
		Type: raftpb.MessageType_MsgApp.Enum(),
		To:   proto.Uint64(uint64(s.MemberID())),
		From: proto.Uint64(0xdead),
		Term: proto.Uint64(1000),
	}
	if err := s.Process(context.TODO(), m); err != nil {
		t.Fatal(err)
	}
	for s.Leader() == s.MemberID() {
		time.Sleep(time.Millisecond)
	}
	_, err := ttl(s, id)
	lctx, lcancel := context.WithTimeout(context.Background(), 5*time.Second)
	ls, lerr := s.LeaseLeases(lctx, &pb.LeaseLeasesRequest{})
	lcancel()
	live := false
	if lerr == nil {
		for _, l := range ls.Leases {
			live = live || l.ID == id
		}
	}
	t.Logf("TimeToLive after the outsider's message: err=%v; lease in the lessor: %v", err, live)
	if errors.Is(err, lease.ErrLeaseNotFound) && live {
		t.Logf("not found for a live lease: the contract excludes this run")
	}
}
