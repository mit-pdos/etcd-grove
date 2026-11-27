// The Go evidence of the grpc model's HealthCheckResponse_ServingStatus.String (prove-healthstr,
// 2026-11-27, etcd-grove#24 7225943254; models/grpc/health/grpc_health_v1/health.pb.go, a MODEL:
// switch). grpc-go's generated method (health.pb.go:72) is protoimpl.X.EnumStringOf(x.Descriptor(),
// protoreflect.EnumNumber(x)); the model is a switch on the value with the enum's four names, else
// strconv.Itoa of the value. This test runs against the real grpc-go (examples/go.mod).
//
//   - TestHealthModelIsString: for 0-3 and for unknown, negative and extreme values, the real method,
//     by value and through a pointer, equals the model;
//   - TestHealthModelIsDescriptor: the enum's descriptor has exactly the model's four numbers and
//     names (and the generated table agrees).

package enumstring

import (
	"strconv"
	"testing"

	"google.golang.org/grpc/health/grpc_health_v1"
)

func modelHealth(x grpc_health_v1.HealthCheckResponse_ServingStatus) string {
	switch x {
	case 0:
		return "UNKNOWN"
	case 1:
		return "SERVING"
	case 2:
		return "NOT_SERVING"
	case 3:
		return "SERVICE_UNKNOWN"
	}
	return strconv.Itoa(int(x))
}

var healthNames = map[int32]string{0: "UNKNOWN", 1: "SERVING", 2: "NOT_SERVING", 3: "SERVICE_UNKNOWN"}

func TestHealthModelIsString(t *testing.T) {
	vs := []int32{0, 1, 2, 3, 4}
	vs = append(vs, extra...)
	for _, v := range vs {
		x := grpc_health_v1.HealthCheckResponse_ServingStatus(v)
		r := &grpc_health_v1.HealthCheckResponse{Status: x}
		if got, want := x.String(), modelHealth(x); got != want {
			t.Errorf("ServingStatus(%d).String() = %q, model %q", v, got, want)
		}
		if got, want := (&r.Status).String(), modelHealth(x); got != want {
			t.Errorf("(&ServingStatus(%d)).String() = %q, model %q", v, got, want)
		}
	}
}

func TestHealthModelIsDescriptor(t *testing.T) {
	d := grpc_health_v1.HealthCheckResponse_ServingStatus(0).Descriptor().Values()
	if d.Len() != len(healthNames) {
		t.Errorf("ServingStatus: %d descriptor values, model %d", d.Len(), len(healthNames))
	}
	for i := 0; i < d.Len(); i++ {
		v := d.Get(i)
		if s, ok := healthNames[int32(v.Number())]; !ok || s != string(v.Name()) {
			t.Errorf("ServingStatus: descriptor value %d %q, model %q %v", v.Number(), v.Name(), s, ok)
		}
	}
	if len(grpc_health_v1.HealthCheckResponse_ServingStatus_name) != len(healthNames) {
		t.Errorf("ServingStatus_name has %d entries", len(grpc_health_v1.HealthCheckResponse_ServingStatus_name))
	}
	for k, s := range grpc_health_v1.HealthCheckResponse_ServingStatus_name {
		if healthNames[k] != s {
			t.Errorf("ServingStatus_name[%d] = %q, model %q", k, s, healthNames[k])
		}
	}
}
