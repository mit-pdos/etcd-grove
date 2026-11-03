package apply

import (
	"testing"

	"github.com/prometheus/client_golang/prometheus/testutil"
	"github.com/stretchr/testify/require"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/client/pkg/v3/types"
	"go.etcd.io/etcd/server/v3/etcdserver/api/membership"
)

// TestAlarmGaugeReactivate ensures that the etcd_debugging_server_alarms gauge
// counts the alarms the store holds: an alarm activated twice (the store keeps
// one) counts once, and is back to the initial value once disarmed. Uses
// defaultUberApplier and memberID from uber_applier_test.go.
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
	got := ua.Apply(&InternalRaftRequestWrapper{InternalRaftRequest: &pb.InternalRaftRequest{
		Header: &pb.RequestHeader{},
		Alarm:  &pb.AlarmRequest{Action: pb.AlarmRequest_GET, Alarm: pb.AlarmType_NOSPACE},
	}}, membership.ApplyBoth)
	require.Len(t, got.Resp.(*pb.AlarmResponse).Alarms, 1, "one alarm after two activations")
	require.Equal(t, before+1, testutil.ToFloat64(gauge), "the gauge should count the one alarm once")

	alarm(pb.AlarmRequest_DEACTIVATE)
	require.Equal(t, before, testutil.ToFloat64(gauge), "the gauge should be back once the alarm is disarmed")
}
