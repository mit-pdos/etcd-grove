// Package latencytracker checks the premises of the trust-boundary specs of the etcd3 store's
// pre-materialized metrics (prove-metrics, 2026-11-21;
// Spec/k8s_io/apiserver/pkg/storage/etcd3/metrics/{NewEtcdMetricsTracker,OperationLatencyTracker__Record}.lean),
// at apiserver 9c4ec15b8038 (metrics.go:360-398).
//
// (*OperationLatencyTracker).Record's spec returned for every non-nil t and every err; it panics
// on a tracker NewOperationLatencyTracker did not build (a zero tracker's latency is a nil
// interface: t.latency.Observe dereferences it) and, for any tracker, on an err whose
// errorReason panics (a typed-nil *status.Error: status.FromError calls its GRPCStatus, which
// dereferences nil), whether the metrics are registered or not. The spec now takes the tracker's
// abstract origin (metrics.latencyTrackerOk, from NewEtcdMetricsTracker's post) and
// statusErrOk err, as RecordEtcdRequest's (recordetcdrequest).
//
// NewEtcdMetricsTracker(gr)'s spec returned for every gr; once the metrics are registered
// (etcd3/metrics.Register, which the apiserver runs), it panics on a group or resource that is not
// valid UTF-8 (NewOperationLatencyTracker's WithLabelValues). The spec now takes utf8Valid of both,
// as the recorders' (nonissues/k8s-apiserver-metrics-negative-or-non-utf8-panic.md).
package latencytracker

import (
	"reflect"
	"testing"
	"time"

	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/status"
	"k8s.io/apimachinery/pkg/runtime/schema"
	"k8s.io/apiserver/pkg/storage/etcd3/metrics"
)

var gr = schema.GroupResource{Group: "", Resource: "pods"}

func panics(f func()) (r any) {
	defer func() { r = recover() }()
	f()
	return nil
}

func typedNilStatusError(t *testing.T) error {
	t.Helper()
	ty := reflect.TypeOf(status.Error(codes.Internal, "x"))
	err, ok := reflect.Zero(ty).Interface().(error)
	if !ok || err == nil || ty.Kind() != reflect.Pointer {
		t.Fatalf("expected a non-nil error holding a nil %v", ty)
	}
	return err
}

// The tests run in order in one process: unregistered first, then registered.

func TestRecordUnregistered(t *testing.T) {
	mt := metrics.NewEtcdMetricsTracker(gr)
	cases := []struct {
		name  string
		f     func()
		panic bool
	}{
		{"built tracker, nil err", func() { mt.Get.Record(nil, time.Now()) }, false},
		{"built tracker, status error", func() { mt.Get.Record(status.Error(codes.Unavailable, "x"), time.Now()) }, false},
		{"built tracker, conflict", func() { mt.Get.Record(metrics.ErrTransactionConflict, time.Now()) }, false},
		{"built tracker, typed-nil *status.Error", func() { mt.Get.Record(typedNilStatusError(t), time.Now()) }, true},
		{"zero tracker", func() { (&metrics.OperationLatencyTracker{}).Record(nil, time.Now()) }, true},
		{"unregistered, invalid UTF-8 group", func() { metrics.NewEtcdMetricsTracker(schema.GroupResource{Group: "\xff"}) }, false},
	}
	for _, c := range cases {
		r := panics(c.f)
		t.Logf("%-40s panic: %v", c.name, r)
		if (r != nil) != c.panic {
			t.Errorf("%s: expected panic %v, got %v", c.name, c.panic, r)
		}
	}
}

func TestNewEtcdMetricsTrackerRegistered(t *testing.T) {
	metrics.Register()
	bad := []schema.GroupResource{{Group: "\xff", Resource: "pods"}, {Group: "", Resource: "\xff"}}
	for _, b := range bad {
		if r := panics(func() { metrics.NewEtcdMetricsTracker(b) }); r == nil {
			t.Errorf("NewEtcdMetricsTracker(%q) after Register: expected a panic", b)
		} else {
			t.Logf("NewEtcdMetricsTracker(%q): %v", b, r)
		}
	}
	mt := metrics.NewEtcdMetricsTracker(gr)
	if r := panics(func() { mt.Get.Record(status.Error(codes.Unavailable, "x"), time.Now()) }); r != nil {
		t.Errorf("registered, valid labels: Record panicked: %v", r)
	}
}
