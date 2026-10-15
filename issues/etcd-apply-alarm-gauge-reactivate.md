# server/etcdserver/apply: the alarm gauge counts an alarm activated twice twice

- **Status**: open (a wrong metric value; not filed).
- **Where**: `server/etcdserver/apply/backend.go` at bc8b52a50 (`etc/goose.py`'s etcd pin),
  `applierV3backend.Alarm` (`backend.go:116-132`): on `ACTIVATE` it increments the gauge
  `etcd_debugging_server_alarms{server_id, alarm_type}` (`metrics.go:19-28`) whenever
  `AlarmStore.Activate` returns a member, on `DEACTIVATE` it decrements it whenever
  `Deactivate` does. But `AlarmStore.Activate` (`api/v3alarm/alarms.go:53-64`) returns the
  *existing* member, without writing, when the alarm is already set (`addToMap` returns it), so
  a second activation of the same alarm increments the gauge again, while the store keeps one
  alarm; one deactivation removes it and decrements once.
- **Reachable**: an `ACTIVATE` comes from the Maintenance API's `Alarm` (`v3_server.go:805`,
  any action, an admin request) and from the apply loop: `applyEntryNormal`
  (`server.go:1976-1996`) proposes a `NOSPACE` activation for every applied request that
  failed with `ErrNoSpace` while no `NOSPACE` alarm is set *at its apply*; several such
  requests applied before the first activation entry applies propose several activations.
- **What happens**: the gauge reads 2 for one alarm, and 1 after it is disarmed (it never
  returns to 0 while the member runs). Reproduction (`server/etcdserver/apply/`, next to
  `uber_applier_test.go`'s `defaultUberApplier`; it passes, asserting the drift):

  ```go
  package apply
  
  import (
  	"testing"
  
  	"github.com/prometheus/client_golang/prometheus/testutil"
  	"github.com/stretchr/testify/require"
  
  	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
  	"go.etcd.io/etcd/client/pkg/v3/types"
  	"go.etcd.io/etcd/server/v3/etcdserver/api/membership"
  )
  
  // An alarm activated twice (the alarm store keeps one member) counts twice in the
  // `etcd_debugging_server_alarms` gauge; deactivated once, it is gone but the gauge says 1.
  func TestAlarmGaugeReactivate(t *testing.T) {
  	ua := defaultUberApplier(t)
  	alarm := func(action pb.AlarmRequest_AlarmAction) {
  		result := ua.Apply(&InternalRaftRequestWrapper{InternalRaftRequest: &pb.InternalRaftRequest{
  			Header: &pb.RequestHeader{},
  			Alarm:  &pb.AlarmRequest{Action: action, MemberID: memberID, Alarm: pb.AlarmType_NOSPACE},
  		}}, membership.ApplyBoth)
  		require.NotNil(t, result)
  		require.NoError(t, result.Err)
  	}
  	gauge := alarms.WithLabelValues(types.ID(memberID).String(), pb.AlarmType_NOSPACE.String())
  	before := testutil.ToFloat64(gauge)
  	alarm(pb.AlarmRequest_ACTIVATE)
  	alarm(pb.AlarmRequest_ACTIVATE)
  	require.Equal(t, before+2, testutil.ToFloat64(gauge), "the second activation counts again")
  	alarm(pb.AlarmRequest_DEACTIVATE)
  	got := ua.Apply(&InternalRaftRequestWrapper{InternalRaftRequest: &pb.InternalRaftRequest{
  		Header: &pb.RequestHeader{},
  		Alarm:  &pb.AlarmRequest{Action: pb.AlarmRequest_GET, Alarm: pb.AlarmType_NOSPACE},
  	}}, membership.ApplyBoth)
  	require.Empty(t, got.Resp.(*pb.AlarmResponse).Alarms, "no alarm left")
  	require.Equal(t, before+1, testutil.ToFloat64(gauge), "but the gauge still counts one")
  }
  ```
- **Expected**: the gauge counts the alarms the store holds (its help text: "Alarms for every
  member in cluster"): 1 while the alarm is set, 0 after it is disarmed.
- **How the proof handles it**: not a premise: the gauge is a metric (`alarms`, a package
  fact of `apply/Base.lean`; its `Inc`/`Dec` return, mvcc's `gaugeSpec`), which no
  statement of the apply package models; the finding is from reading the code for the alarm
  store's contract (`isAlarmStore`, `Proof/go_etcd_io/etcd/server/v3/etcdserver/apply/
  Contracts.lean`: `Activate` returns a member whether it wrote or not).
- **Possible fixes**: count only a new alarm: `Activate` could report whether it added the
  member (or the applier compares the returned member with a fresh one, as `Activate` does
  internally), and `Deactivate` likewise; or set the gauge from the store (`Set(1)` on
  activation, `Set(0)` on deactivation, per label).
- **Found**: 2026-10-12, apply unit 0 (the alarm store's contract), reproduced with the test
  above at bc8b52a50.
