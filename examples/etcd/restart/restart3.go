// Package restart is the three-member restart example (restart3, notes/restart3-scope.md §4): three
// etcd members started in-process, N1 Puts of distinct keys through member 1's own API
// ((*EtcdServer).Put, the call v3rpc's kvServer.Put makes; member 1 may be a follower, which
// forwards the proposal), a follower other than member 1 stopped gracefully (HardStop, in the same
// process), N2 more Puts of distinct keys through member 1 while it is down (the other two keep the
// quorum), the stopped member started again on its data directory -- same name, addresses and
// settings -- and one linearizable Range of the keys through the restarted member's own API, checked
// exactly: every acknowledged Put's key with its value, at version 1 (applied once), the response's
// revision 1 + N1 + N2 (the store's first revision and one per Put), and nothing else in the range.
// A restart that lost an acknowledged write (one made before the stop, or one made while the member
// was down), applied one twice (its version 2, the revision higher) or invented one fails the check.
// The check does not compare the keys' create and mod revisions.
//
// The members take a disk snapshot every applied entry and compact raft's log to one entry below it
// (SnapCount = SnapCatchUp = 1), so that the restarted member's WAL holds a snapshot record (the
// restart replays the WAL past it) and the leader compacts past the stopped member's last index
// while it is down (the restarted member may then be caught up by a merged snapshot, which the
// verified fork defers while its sender is inside its own replay window).
//
// Each member's peer address is served by one listener for the whole run, through the example's own
// handler (raftSwap), which forwards each request to the current incarnation's raft handler and is
// swapped to the restarted incarnation's under a mutex before it starts (D-R3-4; each incarnation is
// built before its handler is served or swapped in, so the handler is never unset): the address is
// never closed or listened on again. A request that reached the stopped incarnation's handler before
// the swap may still run in it; it finds that incarnation stopped.
//
// Before the Range, the driver waits until the restarted member knows a leader (restart1's: a
// linearizable read begun earlier can fail with ErrLeaderChanged). A liveness wait, as stop's wait on
// AppliedIndex().
//
// "Restart" here is a graceful stop in one process: not a kill, a SIGKILL or a power loss.
//
// Main panics if the check fails; the adequacy theorem to prove is that it does not. An error from
// any step ends Main without a check, as in putget3.
package restart

import (
	"context"
	"net"
	"net/http"
	"sync"
	"time"

	"go.uber.org/zap"

	"go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/client/pkg/v3/types"
	"go.etcd.io/etcd/server/v3/etcdserver"

	"github.com/mit-pdos/etcd-grove/examples/lib/etcdstart"
)

// The members' peer and client addresses (each member's one peer URL is http://<peer addr>, served by
// its raftSwap; its client URL http://<client addr> is not served: the program serves no gRPC). Not
// another example's, so that the examples' tests can run at once.
const (
	peerAddr1   = "127.0.0.1:23861"
	peerAddr2   = "127.0.0.1:23862"
	peerAddr3   = "127.0.0.1:23863"
	clientAddr1 = "127.0.0.1:23864"
	clientAddr2 = "127.0.0.1:23865"
	clientAddr3 = "127.0.0.1:23866"
)

// The members' names, and the cluster's token.
const (
	name1 = "restart3-1"
	name2 = "restart3-2"
	name3 = "restart3-3"
	token = "restart3"
)

// The members' snapshot settings (etcdstart.BuildServer): a disk snapshot every SnapCount applied
// entries, raft's log then compacted to SnapCatchUp entries below it.
const (
	SnapCount   uint64 = 1
	SnapCatchUp uint64 = 1
)

// NBoot is the number of the cluster's bootstrap entries: one configuration change per member.
const NBoot = 3

// N1 is the number of Puts before the stop, N2 the number while the member is down (N1 + N2 at most
// 256: key i is "k" followed by the byte i). Any N2 >= 1 lets the leader compact past the stopped
// member at SnapCatchUp = 1.
const (
	N1 = 5
	N2 = 20
)

// key is the i-th Put's key, "k" followed by the byte i (i < 256): the keys are distinct, in the
// order of i, and all in [RangeKey, RangeEnd).
func key(i int) []byte {
	return []byte{'k', byte(i)}
}

// value is the i-th Put's value, "v" followed by the byte i.
func value(i int) []byte {
	return []byte{'v', byte(i)}
}

// The Range after the restart: every key that begins with "k".
const (
	RangeKey = "k"
	RangeEnd = "l"
)

// raftSwap is a member's peer handler: it forwards each request to the handler h of the member's
// current incarnation, which set replaces under mu.
type raftSwap struct {
	mu *sync.Mutex
	h  http.Handler
}

// ServeHTTP serves r with the current incarnation's handler.
func (sw *raftSwap) ServeHTTP(w http.ResponseWriter, r *http.Request) {
	sw.mu.Lock()
	h := sw.h
	sw.mu.Unlock()
	h.ServeHTTP(w, r)
}

// set makes h the handler of the member's current incarnation.
func (sw *raftSwap) set(h http.Handler) {
	sw.mu.Lock()
	sw.h = h
	sw.mu.Unlock()
}

// A member: its peer handler, served at its peer address for the whole run, and its name, peer URLs
// and client address, for its restart.
type member struct {
	sw     *raftSwap
	name   string
	peer   types.URLs
	client string
}

// build builds an incarnation of member name of the cluster cluster, with peer URLs peer and client
// URL http://client (etcdstart.BuildServer, at the snapshot settings), not yet started. Building a
// member that was stopped finds its data directory (the member's name + ".etcd"): etcd restarts it
// from its WAL.
func build(name string, peer types.URLs, client string, cluster types.URLsMap,
	lg *zap.Logger) (*etcdserver.EtcdServer, error) {
	return etcdstart.BuildServer(name, peer, client, cluster, token, SnapCount, SnapCatchUp, lg)
}

// newMember serves member name's peer handler on a listener at peerAddr, forwarding to the built
// first incarnation s's raft handler, and starts s.
func newMember(s *etcdserver.EtcdServer, name string, peer types.URLs, peerAddr string,
	client string) (*member, error) {
	pl, err := net.Listen("tcp", peerAddr)
	if err != nil {
		return nil, err
	}
	sw := &raftSwap{mu: new(sync.Mutex), h: s.RaftHandler()}
	go http.Serve(pl, sw)
	s.Start()
	return &member{sw: sw, name: name, peer: peer, client: client}, nil
}

// restartMember builds a new incarnation of the stopped member m (on its data directory, at its
// addresses), swaps m's peer handler to its raft handler, and starts it.
func restartMember(m *member, cluster types.URLsMap, lg *zap.Logger) (*etcdserver.EtcdServer, error) {
	s, err := build(m.name, m.peer, m.client, cluster, lg)
	if err != nil {
		return nil, err
	}
	m.sw.set(s.RaftHandler())
	s.Start()
	return s, nil
}

// put puts key(i) with value value(i) through s's own API, in a context with the request timeout,
// cancelled after the call.
func put(s *etcdserver.EtcdServer, i int) error {
	ctx, cancel := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)
	_, err := s.Put(ctx, &etcdserverpb.PutRequest{Key: key(i), Value: value(i)})
	cancel()
	return err
}

// stop stops the incarnation s: it waits until s has applied the cluster's bootstrap entries (one per
// member), so that its data directory holds the cluster's members when it is started again, then
// stops it (HardStop: no leadership transfer; run's deferred shutdown stops the raft node and the
// transport and calls Cleanup, which closes the lessor, the KV store, the auth store and the backend,
// so that the data directory can be opened again).
func stop(s *etcdserver.EtcdServer) {
	for s.AppliedIndex() < NBoot {
		time.Sleep(time.Millisecond)
	}
	s.HardStop()
}

// check waits until s knows a leader, then reads every key in [RangeKey, RangeEnd) through s's own API
// (a linearizable Range, in a context with the request timeout, cancelled after the call) and panics
// unless it returns exactly the N1 + N2 Puts' keys, in order, each with its value at version 1, at the
// response revision 1 + N1 + N2. It reports whether the check ran: false if the Range failed.
func check(s *etcdserver.EtcdServer) bool {
	for s.Leader() == 0 {
		time.Sleep(time.Millisecond)
	}
	ctx, cancel := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)
	resp, err := s.Range(ctx, &etcdserverpb.RangeRequest{Key: []byte(RangeKey),
		RangeEnd: []byte(RangeEnd)})
	cancel()
	if err != nil {
		return false
	}
	if resp.Header.Revision != 1+N1+N2 {
		panic("restart3: the restarted member's Range is not at revision 1 + N1 + N2")
	}
	if len(resp.Kvs) != N1+N2 {
		panic("restart3: the restarted member's Range did not return every Put")
	}
	for i := 0; i < N1+N2; i++ {
		kv := resp.Kvs[i]
		if string(kv.Key) != string(key(i)) || string(kv.Value) != string(value(i)) ||
			kv.Version != 1 {
			panic("restart3: the restarted member's Range returned a wrong pair")
		}
	}
	return true
}

// Run is Main with the logger lg, so that a test can count what the members log. It reports whether
// the check ran (and passed): false if a step failed first. It leaves the members running.
func Run(lg *zap.Logger) bool {
	peer1 := types.URLs{{Scheme: "http", Host: peerAddr1}}
	peer2 := types.URLs{{Scheme: "http", Host: peerAddr2}}
	peer3 := types.URLs{{Scheme: "http", Host: peerAddr3}}
	cluster := types.URLsMap{name1: peer1, name2: peer2, name3: peer3}

	s1, err := build(name1, peer1, clientAddr1, cluster, lg)
	if err != nil {
		return false
	}
	s2, err := build(name2, peer2, clientAddr2, cluster, lg)
	if err != nil {
		return false
	}
	s3, err := build(name3, peer3, clientAddr3, cluster, lg)
	if err != nil {
		return false
	}
	_, err = newMember(s1, name1, peer1, peerAddr1, clientAddr1)
	if err != nil {
		return false
	}
	m2, err := newMember(s2, name2, peer2, peerAddr2, clientAddr2)
	if err != nil {
		return false
	}
	m3, err := newMember(s3, name3, peer3, peerAddr3, clientAddr3)
	if err != nil {
		return false
	}

	for i := 0; i < N1; i++ {
		if err := put(s1, i); err != nil {
			return false
		}
	}

	// a follower other than member 1 stopped and started again (no election forced): member 3, or
	// member 2 if member 3 leads; the other two keep the quorum
	m, s := m3, s3
	if s3.Leader() == s3.MemberID() {
		m, s = m2, s2
	}
	stop(s)
	for i := N1; i < N1+N2; i++ {
		if err := put(s1, i); err != nil {
			return false
		}
	}

	// the stopped member started again on its data directory, at its addresses
	sR, err := restartMember(m, cluster, lg)
	if err != nil {
		return false
	}
	return check(sR)
}

// Main runs the example with no logging (Run).
func Main() {
	Run(zap.NewNop())
}
