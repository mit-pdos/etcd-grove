// Package restart1 is the one-member restart example (restart S7, notes/restart-s7-scope.md): one
// etcd member started in-process, NPuts Puts of distinct keys through the server's own API
// ((*EtcdServer).Put, the call v3rpc's kvServer.Put makes), the member stopped gracefully
// (HardStop, in the same process), started again on its data directory -- same name, addresses and
// settings -- and one linearizable Range of the keys through the restarted member's own API, checked
// exactly: every acknowledged Put's key with its value, and nothing else. A restart that lost an
// acknowledged write, applied one twice or invented one fails the check.
//
// The member takes a disk snapshot every other applied entry (SnapCount), so that the WAL the
// restart reads holds a snapshot record and the backend is opened at a consistent index above it:
// the restart replays the WAL past the snapshot, skips the entries at or below the backend's
// consistent index, and restarts the raft node from the WAL's hard state. The cluster has no other
// member, so no peer listener is served and no snapshot is ever sent; no gRPC is served either.
//
// "Restart" here is a graceful stop in one process: not a kill, a SIGKILL or a power loss.
//
// Main panics if the check fails; the adequacy theorem to prove is that it does not. An error from
// any step ends Main without a check, as in putget.
package restart1

import (
	"context"
	"time"

	"go.uber.org/zap"

	"go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/client/pkg/v3/types"
	"go.etcd.io/etcd/server/v3/etcdserver"

	"github.com/mit-pdos/etcd-grove/examples/lib/etcdstart"
)

// The member's name (its data directory is name + ".etcd", its cluster token its name), its peer
// address (its one peer URL is http://peerAddr, not served: the cluster has no other member) and
// its client address (its one client URL http://clientAddr, not served). Not another example's.
const (
	name       = "restart1"
	peerAddr   = "127.0.0.1:23811"
	clientAddr = "127.0.0.1:23812"
)

// The snapshot settings (etcdstart.BuildServer): a disk snapshot every SnapCount applied entries,
// raft's log then compacted to SnapCatchUp entries below it.
const (
	SnapCount   uint64 = 1
	SnapCatchUp uint64 = 1
)

// NBoot is the number of the cluster's bootstrap entries: one configuration change per member.
const NBoot = 1

// NPuts is the number of Puts before the stop (at most 256: key i is "k" followed by the byte i).
// Eleven: the WAL then usually ends one entry above its last snapshot record (a disk snapshot is
// taken when two entries were applied since the last, and the run's entries are applied mostly one
// at a time), so that the restart replays an entry past the snapshot and skips it, at the backend's
// consistent index (restart1_test.go logs whether it did: 19 runs out of 20, 2026-11-14).
const NPuts = 11

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

// startMember builds the member (etcdstart.BuildServer, at the snapshot settings) and starts it.
// Starting it again after it was stopped finds its data directory: etcd restarts it from its WAL.
func startMember(lg *zap.Logger) (*etcdserver.EtcdServer, error) {
	peer := types.URLs{{Scheme: "http", Host: peerAddr}}
	s, err := etcdstart.BuildServer(name, peer, clientAddr, types.URLsMap{name: peer}, name,
		SnapCount, SnapCatchUp, lg)
	if err != nil {
		return nil, err
	}
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

// stop stops the member s: it waits until s has applied the cluster's bootstrap entries, so that
// its data directory holds the cluster's member when it is started again, then stops it (HardStop:
// run's deferred shutdown stops the raft node and calls Cleanup, which closes the lessor, the KV
// store, the auth store and the backend, so that the data directory can be opened again).
func stop(s *etcdserver.EtcdServer) {
	for s.AppliedIndex() < NBoot {
		time.Sleep(time.Millisecond)
	}
	s.HardStop()
}

// check waits until s knows a leader (the restarted member elects itself; a linearizable read begun
// before that fails with ErrLeaderChanged when it does), then reads every key in [RangeKey, RangeEnd)
// through s's own API (a linearizable Range, in a context with the request timeout, cancelled after
// the call) and panics unless it returns exactly
// the NPuts Puts' keys, in order, each with its value. It reports whether the check ran: false if
// the Range failed.
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
	if len(resp.Kvs) != NPuts {
		panic("restart1: the restarted member's Range did not return every Put")
	}
	for i := 0; i < NPuts; i++ {
		kv := resp.Kvs[i]
		if string(kv.Key) != string(key(i)) || string(kv.Value) != string(value(i)) {
			panic("restart1: the restarted member's Range returned a wrong pair")
		}
	}
	return true
}

// Run is Main with the logger lg, so that a test can count what the member logs. It reports
// whether the check ran (and passed): false if a step failed first. It leaves the restarted member
// running.
func Run(lg *zap.Logger) bool {
	s, err := startMember(lg)
	if err != nil {
		return false
	}
	for i := 0; i < NPuts; i++ {
		if err := put(s, i); err != nil {
			return false
		}
	}
	stop(s)

	// the stopped member started again on its data directory
	sR, err := startMember(lg)
	if err != nil {
		return false
	}
	return check(sR)
}

// Main runs the example with no logging (Run).
func Main() {
	Run(zap.NewNop())
}
