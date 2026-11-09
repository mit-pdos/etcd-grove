// Package etcdserverboot holds the requirement snippets of batch 2e (a member's lifecycle:
// NewServer, Start, Stop/HardStop, restart, join; the WAL, the snapshotter, the membership view,
// the alarms, the compactor): one function per usage pattern, each panicking where a caller
// relies on the specs (notes/specs-only/README.md, "Requirement snippets").
package etcdserverboot

import (
	"context"
	"time"

	"go.uber.org/zap"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/client/pkg/v3/types"
	"go.etcd.io/etcd/server/v3/config"
	"go.etcd.io/etcd/server/v3/etcdserver"
	"go.etcd.io/etcd/server/v3/etcdserver/api/membership"
	"go.etcd.io/etcd/server/v3/features"
)

// memberConfig is the configuration this repository's starters build (examples/lib/etcdstart's
// newServerMode): every field a premise of NewServer.spec reads is set inside its slot, by the
// slots' introduction laws (ApiBoot.lean): raftNodeBootCfg_intro (ElectionTicks > 1, a
// non-negative heartbeat), v3rpcBootCfg_intro (MaxTxnOps <= 4999, MaxRequestBytes <= 10 MiB),
// mvccBootCfg_intro (CompactionBatchLimit 0), backendBootRes_intro (the default quota; ETCD_VERIFY
// unset: backendEnvOk), authBootRes_intro (AuthToken "simple": set below), leaseBootRes_intro (leases
// may expire), V3compactor.bootCfg_off (retention 0); Config.cfgHeap_intro (the URL literals).
func memberConfig(name string, peer types.URLs, client string, cluster types.URLsMap, token string,
	newCluster bool, lg *zap.Logger) config.ServerConfig {
	return config.ServerConfig{
		Name:                    name,
		DataDir:                 name + ".etcd",
		InitialPeerURLsMap:      cluster,
		PeerURLs:                peer,
		ClientURLs:              types.URLs{{Scheme: "http", Host: client}},
		InitialClusterToken:     token,
		NewCluster:              newCluster,
		TickMs:                  100,
		ElectionTicks:           10,
		SnapshotCount:           etcdserver.DefaultSnapshotCount,
		SnapshotCatchUpEntries:  etcdserver.DefaultSnapshotCatchUpEntries,
		MaxTxnOps:               128,
		MaxRequestBytes:         1536 * 1024,
		AutoCompactionMode:      "revision",
		AutoCompactionRetention: 0,
		AuthToken:               "simple",
		Logger:                  lg,
		ServerFeatureGate:       features.NewDefaultServerFeatureGate(name, lg),
	}
}

func put(s *etcdserver.EtcdServer, k, v string) error {
	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()
	_, err := s.Put(ctx, &pb.PutRequest{Key: []byte(k), Value: []byte(v)})
	return err
}

func get(s *etcdserver.EtcdServer, k string) (*pb.RangeResponse, error) {
	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()
	return s.Range(ctx, &pb.RangeRequest{Key: []byte(k)})
}

// REQ etcdserverboot/start-one: a member of a new one-member cluster is built, started, and is
// member id of the cluster it was allocated in (MemberID is its id, never 0).
// Users: examples/lib/etcdstart.StartServer (putget, txnlin, watch, lease, auth, compacted, ...),
// embed.StartEtcd.
// Assumes: the program allocated the cluster (cluster_alloc: the member computed from this
// configuration, Membership.initialMembers; peerAddr's address reserved), made the disk of the fresh
// directory name+".etcd" (disk_new) and keeps its diskState in its crash invariant (diskAcc); a
// thread token for Start.
// Specs: NewServer.spec (disk_new, memberStart_disk; its post's 0 < id < 2^64, srvMember_id),
// EtcdServer.Start.spec, EtcdServer.MemberID.spec.
func ReqStartOne(name, peerAddr, clientAddr string, lg *zap.Logger) *etcdserver.EtcdServer {
	peer := types.URLs{{Scheme: "http", Host: peerAddr}}
	s, err := etcdserver.NewServer(memberConfig(name, peer, clientAddr, types.URLsMap{name: peer},
		name, true, lg))
	if err != nil {
		return nil
	}
	s.Start()
	if s.MemberID() == 0 {
		panic("start-one: member id 0")
	}
	return s
}

// REQ etcdserverboot/start-three: three members of one new cluster, each from its own fresh
// directory and the same initial-cluster map and token; each member's raft handler is served
// before the member starts (a peer may dial it at once).
// Users: examples/lib/etcdstart.NewMember/StartMember, examples/lib/cluster3.StartCluster,
// examples/etcd/putget3, examples/etcd/partition.
// Assumes: cluster_alloc of the three members; each name+".etcd" fresh; the peer handlers served
// by the caller (raftHandler, http.Serve: 2f's).
// Specs: NewServer.spec, EtcdServer.RaftHandler.spec, EtcdServer.Start.spec; laws:
// srvBuilt_excl (two servers of one member id cannot be built), srvMember_agree.
func ReqStartThree(names [3]string, peers [3]types.URLs, clients [3]string, token string,
	lg *zap.Logger) []*etcdserver.EtcdServer {
	cluster := types.URLsMap{names[0]: peers[0], names[1]: peers[1], names[2]: peers[2]}
	var srvs []*etcdserver.EtcdServer
	for i := 0; i < 3; i++ {
		s, err := etcdserver.NewServer(memberConfig(names[i], peers[i], clients[i], cluster, token,
			true, lg))
		if err != nil {
			return nil
		}
		_ = s.RaftHandler() // served on the member's peer listener by the caller
		srvs = append(srvs, s)
	}
	for _, s := range srvs {
		s.Start()
	}
	ids := map[types.ID]bool{}
	for _, s := range srvs {
		if ids[s.MemberID()] {
			panic("start-three: two members with one id")
		}
		ids[s.MemberID()] = true
	}
	return srvs
}

// REQ etcdserverboot/restart: a member stopped and started again on its data directory continues
// the cluster's history: a write acknowledged before the stop is read after the restart (here, a
// one-member cluster: the restarted member's own linearizable read).
// Users: examples/etcd/restart (restart3: a follower stopped, writes made while it is down, the
// member started again, a Get through it checked), etcd's own restarts (embed: same data dir).
// Assumes: the member was started by ReqStartOne's path (its start right); no other writer of k;
// the configuration of the restart is the first one's (only its directories matter); no request
// is in flight at the stop (this goroutine made them all, and they returned: the gate, srvGate).
// Specs: EtcdServer.HardStop.spec (memberDisk: the disk idle; the whole srvGate), memberStart_disk,
// NewServer.spec, Start, and the request path's Put/Range (2c, each holding a share of srvGate).
func ReqRestart(name, peerAddr, clientAddr string, lg *zap.Logger) {
	s := ReqStartOne(name, peerAddr, clientAddr, lg)
	if s == nil {
		return
	}
	if err := put(s, "k", "v1"); err != nil {
		s.HardStop()
		return
	}
	s.HardStop()

	peer := types.URLs{{Scheme: "http", Host: peerAddr}}
	s2, err := etcdserver.NewServer(memberConfig(name, peer, clientAddr, types.URLsMap{name: peer},
		name, true, lg))
	if err != nil {
		return
	}
	s2.Start()
	defer s2.HardStop()
	resp, err := get(s2, "k")
	if err != nil {
		return
	}
	if len(resp.Kvs) != 1 || string(resp.Kvs[0].Value) != "v1" {
		panic("restart: an acknowledged write lost across the restart")
	}
}

// REQ etcdserverboot/join: a member added by MemberAdd joins from a fresh directory, with
// NewCluster false and the initial-cluster map listing it under its peer URLs: it runs as the id
// the cluster has for those URLs.
// Users: etcd's documented runtime reconfiguration (etcdctl member add; then a start with
// --initial-cluster-state existing); the integration framework's AddMember.
// Assumes: the program reserved peer2's addresses (urls_reserve: urlsRight, which AddMember takes,
// and memberJoin, which the start takes) and holds name2+".etcd" fresh. With this repository's
// starters, s1's peer address serves only the raft handler, which answers bootstrap's GET /members
// with 404: NewServer then returns an error (the trusted bootstrap's join case; etcd's own peer
// handler, etcdhttp.NewPeerHandler, has no spec yet: batch-2e.md Q8), so the panic below is checked
// only on a deployment serving that handler.
// Specs: EtcdServer.AddMember.spec, membership.NewMember.spec, disk_join, memberStart_disk, NewServer.spec,
// Start; laws: srvBuilt_excl.
func ReqJoin(s1 *etcdserver.EtcdServer, name1 string, peer1 types.URLs, name2 string,
	peer2 types.URLs, client2 string, token string, lg *zap.Logger) {
	now := time.Now()
	m := membership.NewMember(name2, peer2, token, &now)
	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	_, err := s1.AddMember(ctx, *m)
	cancel()
	if err != nil {
		return
	}
	cluster := types.URLsMap{name1: peer1, name2: peer2}
	s2, err := etcdserver.NewServer(memberConfig(name2, peer2, client2, cluster, token, false, lg))
	if err != nil {
		return
	}
	s2.Start()
	if s2.MemberID() == s1.MemberID() {
		panic("join: the joiner runs as an existing member")
	}
}

// REQ etcdserverboot/partition: cutting and mending the link to a peer, from any goroutine, at any
// time after the build, never panics.
// Users: examples/lib/cluster3.PeerStep (as etcd's integration tests' InjectPartition); the
// integration framework's Member.Pause/Resume (tests/framework/integration/cluster.go:1166-1172).
// Assumes: s and t are members of one cluster.
// Specs: EtcdServer.CutPeer.spec, EtcdServer.MendPeer.spec, EtcdServer.PauseSending.spec,
// EtcdServer.ResumeSending.spec (each with a thread token, given back), EtcdServer.MemberID.spec;
// law: srvMember_agree (s and t are distinct members).
func ReqPartition(s, t *etcdserver.EtcdServer) {
	s.CutPeer(t.MemberID())
	t.CutPeer(s.MemberID())
	s.MendPeer(t.MemberID())
	t.MendPeer(s.MemberID())
	s.PauseSending()
	s.ResumeSending()
}

// REQ etcdserverboot/ready-or-stop: a started member's ready and stop channels can be waited on
// from any goroutine, never blocking forever on both once the member publishes or stops.
// Users: embed/serve.go:134-136 (StoppingNotify/ReadyNotify), etcdmain/etcd.go:187-188
// (ReadyNotify/StopNotify), examples' tests (<-s.ReadyNotify()).
// Assumes: s was started (isServer).
// Specs: EtcdServer.ReadyNotify.spec (readyCh), EtcdServer.StopNotify.spec (doneCh),
// EtcdServer.StoppingNotify.spec (stoppingCh): receives give nothing.
func ReqReadyOrStop(s *etcdserver.EtcdServer) bool {
	select {
	case <-s.ReadyNotify():
		return true
	case <-s.StoppingNotify():
		return false
	case <-s.StopNotify():
		return false
	}
}

// REQ etcdserverboot/member-list-after-add: a linearizable member list after an acknowledged
// MemberAdd lists the added member (the list is the cluster's, up to order).
// Users: api/v3rpc/member.go:93 (ClusterServer.MemberList; the client's MemberList, Client.Sync).
// Assumes: s was started; the caller holds urlsRight for urls; no other client removes members.
// Specs: EtcdServer.AddMember.spec, EtcdServer.MemberList.spec (srvStep's memberList: the members
// up to permutation when linearizable); laws: etcdState_lb, etcdLb_ord.
func ReqMemberListAfterAdd(ctx context.Context, s *etcdserver.EtcdServer, m membership.Member) {
	if _, err := s.AddMember(ctx, m); err != nil {
		return
	}
	ms, err := s.MemberList(ctx, &pb.MemberListRequest{Linearizable: true})
	if err != nil {
		return
	}
	for _, x := range ms {
		if x.ID == m.ID {
			return
		}
	}
	panic("member-list: added member missing")
}

// REQ etcdserverboot/getters: the status getters a maintenance handler reads never panic.
// Users: api/v3rpc/maintenance.go (Status: CommittedIndex, Backend, Config, ClusterVersion,
// AppliedIndex, Term, Leader), api/v3rpc/quota.go (newBackendQuota: Backend), the health server
// (FeatureEnabled), the auth handlers (AuthStore).
// Assumes: s was started.
// Specs: EtcdServer.{CommittedIndex,Backend,Config,ClusterVersion,AppliedIndex,AuthStore,
// FeatureEnabled}.spec.
func ReqGetters(s *etcdserver.EtcdServer) uint64 {
	_ = s.Backend()
	_ = s.Config()
	_ = s.ClusterVersion()
	_ = s.AuthStore()
	_ = s.FeatureEnabled(features.StopGRPCServiceOnDefrag)
	return s.CommittedIndex() + s.AppliedIndex()
}

// REQ etcdserverboot/stop-after-error: HardStop returns when the server already stopped on its own
// (a transport error ends run: errorc), and the directory can then be restarted.
// Users: embed.Etcd.Close after a server error; examples/etcd/restart's stop.
// Assumes: s was started (srvRunning).
// Specs: EtcdServer.StopNotify.spec (doneCh: a receive gives nothing), EtcdServer.HardStop.spec
// (the done channel's deposit).
func ReqStopAfterError(s *etcdserver.EtcdServer) {
	<-s.StopNotify() // run returned on its own (or never: then the caller does not get here)
	s.HardStop()
}

// REQ etcdserverboot/cleanup-before-start: a built server that is never started is cleaned up
// (embed's error path between NewServer and Start) without a panic.
// Users: embed.StartEtcd (embed/etcd.go:277).
// Assumes: s was built and not started; Cleanup is called once.
// Specs: EtcdServer.Cleanup.spec, srvBuilt_closers.
func ReqCleanupBeforeStart(s *etcdserver.EtcdServer) {
	s.Cleanup()
}

// REQ etcdserverboot/stop-drained: a request in flight when the member is stopped is answered before
// the stop (here, the program waits for it), never one reading a closed backend: HardStop takes the
// whole gate (srvGate s 1), which every request-path call holds a share of.
// Users: embed.Etcd.Close (it stops the gRPC servers gracefully first; its forced fallback,
// grpc.Stop, does not drain: issues/etcd-read-after-backend-close-panic.md), examples/etcd/restart
// (the stopped member serves no gRPC).
// Assumes: s was started by this program and serves no gRPC server of its own.
// Specs: srvGate_fractional, the request path's Range (2c: a share held per call),
// EtcdServer.HardStop.spec.
func ReqStopDrained(s *etcdserver.EtcdServer) {
	done := make(chan struct{})
	go func() {
		_, _ = get(s, "k") // a share of the gate for the call
		close(done)
	}()
	<-done // the share back: no request in flight
	s.HardStop()
}

// REQ etcdserverboot/crash-restart: after a crash of the process at any point (outside the scope
// crashOutOfScope names), the member restarted on its directory continues the cluster's history: a
// write acknowledged before the crash is read after the restart. Not runnable in-process (a crash is
// the adequacy theorem's crash rule: the restart below is the recovery procedure's body).
// Users: every etcd deployment (systemd restarts after a kill); examples/etcd/restart's crash variant.
// Assumes: the recovery runs after a crash of the process that ran the member on name+".etcd" (the
// crash rule's crashGone), unless crashOutOfScope (R1's confAboveOk at the crash, no crash during a
// snapshot-carrying write: batch-2e.md Q2), and the program's crash invariant holds diskState; k was
// put before the crash by a client that got an answer.
// Specs: disk_crash, diskIdle_agree, memberStart_disk, NewServer.spec, EtcdServer.Start.spec, the
// request path's Range (2c).
func ReqCrashRecover(name, peerAddr, clientAddr string, lg *zap.Logger) {
	peer := types.URLs{{Scheme: "http", Host: peerAddr}}
	s, err := etcdserver.NewServer(memberConfig(name, peer, clientAddr, types.URLsMap{name: peer},
		name, true, lg))
	if err != nil {
		return
	}
	s.Start()
	resp, err := get(s, "k")
	if err != nil {
		return
	}
	if len(resp.Kvs) != 1 {
		panic("crash-restart: an acknowledged write lost across the crash")
	}
}
