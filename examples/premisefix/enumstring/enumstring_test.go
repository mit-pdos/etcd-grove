// Package enumstring is the Go evidence of the trusted models of two protoc-gen-go enum String
// methods (etcd-grove#39, 2026-11-23): etcdserverpb's AlarmType.String and mvccpb's
// Event_EventType.String (TrustedCode/go_etcd_io/etcd/api/v3/{etcdserverpb,mvccpb}.lean). The
// generated method is protoimpl.X.EnumStringOf(x.Descriptor(), protoreflect.EnumNumber(x)); each
// model is the lookup of the value in the enum's generated name table (AlarmType_name,
// Event_EventType_name), else strconv.Itoa of the value, as raftpb's MessageType.String
// (examples/raft/tracecheck/msgtype_string_test.go).
//
//   - TestModelIsString: for every key of the table and for unknown, negative and extreme values, the
//     real method, by value and through a pointer (the call the verified code makes, through a field's
//     address), equals the model;
//   - TestTableIsDescriptor: the table and the enum's descriptor have the same numbers and names (no
//     aliases: one name per number).
//
// healthstatus_test.go does the same for grpc's HealthCheckResponse_ServingStatus.String, whose model
// is the grpc model's switch on the four values (models/grpc).
//
// Run: GOWORK=off go test ./premisefix/enumstring/ (from examples/).
package enumstring

import (
	"math"
	"strconv"
	"testing"

	"go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/api/v3/mvccpb"
)

func modelAlarm(x etcdserverpb.AlarmType) string {
	if s, ok := etcdserverpb.AlarmType_name[int32(x)]; ok {
		return s
	}
	return strconv.Itoa(int(x))
}

func modelEvent(x mvccpb.Event_EventType) string {
	if s, ok := mvccpb.Event_EventType_name[int32(x)]; ok {
		return s
	}
	return strconv.Itoa(int(x))
}

var extra = []int32{3, 7, 100, -1, -2, math.MaxInt32, math.MinInt32, 1 << 30}

func TestModelIsString(t *testing.T) {
	var as []etcdserverpb.AlarmType
	for k := range etcdserverpb.AlarmType_name {
		as = append(as, etcdserverpb.AlarmType(k))
	}
	var es []mvccpb.Event_EventType
	for k := range mvccpb.Event_EventType_name {
		es = append(es, mvccpb.Event_EventType(k))
	}
	for _, v := range extra {
		as = append(as, etcdserverpb.AlarmType(v))
		es = append(es, mvccpb.Event_EventType(v))
	}
	for _, a := range as {
		m := &etcdserverpb.AlarmMember{Alarm: a}
		if got, want := a.String(), modelAlarm(a); got != want {
			t.Errorf("AlarmType(%d).String() = %q, model %q", int32(a), got, want)
		}
		if got, want := (&m.Alarm).String(), modelAlarm(a); got != want {
			t.Errorf("(&AlarmType(%d)).String() = %q, model %q", int32(a), got, want)
		}
	}
	for _, e := range es {
		ev := &mvccpb.Event{Type: e}
		if got, want := e.String(), modelEvent(e); got != want {
			t.Errorf("Event_EventType(%d).String() = %q, model %q", int32(e), got, want)
		}
		if got, want := (&ev.Type).String(), modelEvent(e); got != want {
			t.Errorf("(&Event_EventType(%d)).String() = %q, model %q", int32(e), got, want)
		}
	}
}

func TestTableIsDescriptor(t *testing.T) {
	ad := etcdserverpb.AlarmType(0).Descriptor().Values()
	if ad.Len() != len(etcdserverpb.AlarmType_name) {
		t.Errorf("AlarmType: %d descriptor values, %d table entries", ad.Len(), len(etcdserverpb.AlarmType_name))
	}
	for i := 0; i < ad.Len(); i++ {
		v := ad.Get(i)
		if s, ok := etcdserverpb.AlarmType_name[int32(v.Number())]; !ok || s != string(v.Name()) {
			t.Errorf("AlarmType: descriptor value %d %q, table %q %v", v.Number(), v.Name(), s, ok)
		}
	}
	ed := mvccpb.Event_EventType(0).Descriptor().Values()
	if ed.Len() != len(mvccpb.Event_EventType_name) {
		t.Errorf("Event_EventType: %d descriptor values, %d table entries", ed.Len(), len(mvccpb.Event_EventType_name))
	}
	for i := 0; i < ed.Len(); i++ {
		v := ed.Get(i)
		if s, ok := mvccpb.Event_EventType_name[int32(v.Number())]; !ok || s != string(v.Name()) {
			t.Errorf("Event_EventType: descriptor value %d %q, table %q %v", v.Number(), v.Name(), s, ok)
		}
	}
}
