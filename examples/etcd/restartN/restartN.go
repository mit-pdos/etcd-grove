// Package restartN is the restart example (examples/etcd/restart, restart3) with any number of members
// (notes/restartN-plan.md): k >= 2 etcd members started in-process, N1 Puts of distinct keys through
// member 0's own API ((*EtcdServer).Put, the call v3rpc's kvServer.Put makes; member 0 may be a
// follower, which forwards the proposal), a follower other than member 0 stopped gracefully (HardStop,
// in the same process), N2 more Puts of distinct keys through member 0 while it is down, the stopped
// member started again on its data directory -- same name, addresses and settings -- and one
// linearizable Range of the keys through the restarted member's own API, checked exactly: every
// acknowledged Put's key with its value, at version 1 (applied once), the response's revision
// 1 + N1 + N2 (the store's first revision and one per Put), and nothing else in the range. A restart
// that lost an acknowledged write (one made before the stop, or one made while the member was down),
// applied one twice (its version 2, the revision higher) or invented one fails the check. The check
// does not compare the keys' create and mod revisions.
//
// The members are etcdstart.Members' (member i, from 0, is named restartN-i, its peer address
// 127.0.0.1:(PeerBase+i), its client address 127.0.0.1:(ClientBase+i)), started in order as
// etcdstart.StartMembers starts them (the initial cluster's map, then per member the server built and
// served on its peer address, and started), except that every member is built before any is served
// (so that no first boot's GET /members finds a listener: startMembers) and each member's peer
// address is served through the example's own handler (raftSwap) instead of its raft handler
// directly: the handler forwards each
// request to the current incarnation's raft handler and is swapped to the restarted incarnation's under
// a mutex before it starts, so that the address is never closed or listened on again (restart3's
// D-R3-4; each incarnation is built before its handler is served or swapped in, so the handler is never
// unset). A request that reached the stopped incarnation's handler before the swap may still run in
// it; it finds that incarnation stopped.
//
// The member stopped is the last, k-1, or k-2 if k > 2 and member k-1 sees itself as leader. With
// k = 2 the stopped member is member 1 whatever the leader (there is no other follower than member 0);
// the remaining member is then not a quorum, and the Puts while it is down fail (Run returns without
// its check).
//
// The members take a disk snapshot every applied entry and compact raft's log to one entry below it
// (SnapCount = SnapCatchUp = 1), so that the restarted member's WAL holds a snapshot record (the
// restart replays the WAL past it) and the leader compacts past the stopped member's last index
// while it is down (the restarted member may then be caught up by a merged snapshot, which the
// verified fork defers while its sender is inside its own replay window).
//
// Before the Range, the driver waits until the restarted member knows a leader (restart3's: a
// linearizable read begun earlier can fail with ErrLeaderChanged). A liveness wait, as stop's wait on
// AppliedIndex().
//
// "Restart" here is a graceful stop in one process: not a kill, a SIGKILL or a power loss.
//
// Main panics if the check fails; the adequacy theorem to prove is that it does not, for every member
// count 2 <= k <= 1000. An error from any step ends Main without a check, as in restart3. Main(k) for
// k < 2 does nothing (k = 1 is restart1's case, examples/etcd/restart1).
package restartN

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

// The members' address ranges: member i's peer address is 127.0.0.1:(PeerBase+i), its client address
// 127.0.0.1:(ClientBase+i) (not served: the program serves no gRPC). Not another example's, so that
// the examples' tests, and examples/etcd/all's parts, can run at once (until 2026-11-21 29000 and
// 30000, authN's).
const (
	PeerBase   uint64 = 14000
	ClientBase uint64 = 15000
)

// Token is the cluster's token (etcd's --initial-cluster-token), from which, with its peer URL, etcd
// computes each member's id. The theorem's premise on the ids (their 16 low bits distinct and not 0)
// fails for some k <= 1000 at most tokens (putgetN's Token); this token is the first "restartN-<i>" at
// which it holds for every k <= 300, also from the ids of examples/etcd/all's other clusters
// (etcd_safe's Hlow; TestMemberIDs here and there). Above 300 members the ids are not checked:
// etcd_restartN_safe's premise on them may be false there.
const Token = "restartN-11208"

// The members' snapshot settings (etcdstart.BuildServer): a disk snapshot every SnapCount applied
// entries, raft's log then compacted to SnapCatchUp entries below it.
const (
	SnapCount   uint64 = 1
	SnapCatchUp uint64 = 1
)

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
// URL http://client (etcdstart.BuildServer, at the token and the snapshot settings), not yet started.
// Building a member that was stopped finds its data directory (the member's name + ".etcd"): etcd
// restarts it from its WAL.
func build(name string, peer types.URLs, client string, cluster types.URLsMap,
	lg *zap.Logger) (*etcdserver.EtcdServer, error) {
	return etcdstart.BuildServer(name, peer, client, cluster, Token, SnapCount, SnapCatchUp, lg)
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

// startMembers starts the members ms of a new cluster (etcdstart.StartMembers' steps, each member's
// peer address served through its raftSwap): the initial cluster's map (each member's name to its one
// peer URL http://Peer), then every member built, in order, and only then, for each member in order,
// newMember. Every member's first boot (bootstrap, inside build) thus runs while no member's peer
// address is listened on: its GET of each other member's /members (isMemberBootstrapped) finds no
// listener, and the boot goes on as a new member. It returns the started servers and the members'
// records, in the members' order, and the cluster's map, or the first error (the members built or
// started before it are left as they are).
func startMembers(ms []etcdstart.Member, lg *zap.Logger) ([]*etcdserver.EtcdServer, []*member,
	types.URLsMap, error) {
	cluster := types.URLsMap{}
	for _, m := range ms {
		cluster[m.Name] = types.URLs{{Scheme: "http", Host: m.Peer}}
	}
	srvs := make([]*etcdserver.EtcdServer, len(ms))
	mems := make([]*member, len(ms))
	for j, m := range ms {
		s, err := build(m.Name, cluster[m.Name], m.Client, cluster, lg)
		if err != nil {
			return nil, nil, nil, err
		}
		srvs[j] = s
	}
	for j, m := range ms {
		mem, err := newMember(srvs[j], m.Name, cluster[m.Name], m.Peer, m.Client)
		if err != nil {
			return nil, nil, nil, err
		}
		mems[j] = mem
	}
	return srvs, mems, cluster, nil
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

// stop stops the incarnation s of a member of a cluster of k members: it waits until s has applied the
// cluster's bootstrap entries (one per member, k), so that its data directory holds the cluster's
// members when it is started again, then stops it (HardStop: no leadership transfer; run's deferred
// shutdown stops the raft node and the transport and calls Cleanup, which closes the lessor, the KV
// store, the auth store and the backend, so that the data directory can be opened again).
func stop(s *etcdserver.EtcdServer, k uint64) {
	for s.AppliedIndex() < k {
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
		panic("restartN: the restarted member's Range is not at revision 1 + N1 + N2")
	}
	if len(resp.Kvs) != N1+N2 {
		panic("restartN: the restarted member's Range did not return every Put")
	}
	for i := 0; i < N1+N2; i++ {
		kv := resp.Kvs[i]
		if string(kv.Key) != string(key(i)) || string(kv.Value) != string(value(i)) ||
			kv.Version != 1 {
			panic("restartN: the restarted member's Range returned a wrong pair")
		}
	}
	return true
}

// Run is Main(k) with the logger lg, so that a test can count what the members log. It reports whether
// the check ran (and passed): false if a step failed first, or if k < 2. It leaves the members running.
func Run(k uint64, lg *zap.Logger) bool {
	if k < 2 {
		return false
	}
	ms := etcdstart.Members("restartN", k, PeerBase, ClientBase)
	srvs, mems, cluster, err := startMembers(ms, lg)
	if err != nil {
		return false
	}

	for i := 0; i < N1; i++ {
		if err := put(srvs[0], i); err != nil {
			return false
		}
	}

	// a follower other than member 0 stopped and started again (no election forced): member k-1, or
	// member k-2 if k > 2 and member k-1 leads
	j := k - 1
	if k > 2 && srvs[j].Leader() == srvs[j].MemberID() {
		j = k - 2
	}
	stop(srvs[j], k)
	for i := N1; i < N1+N2; i++ {
		if err := put(srvs[0], i); err != nil {
			return false
		}
	}

	// the stopped member started again on its data directory, at its addresses
	sR, err := restartMember(mems[j], cluster, lg)
	if err != nil {
		return false
	}
	return check(sR)
}

// Main runs the example with k members and no logging (Run).
func Main(k uint64) {
	Run(k, zap.NewNop())
}
