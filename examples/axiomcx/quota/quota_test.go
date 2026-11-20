// These are counterexamples to the former NewBackendQuota and BackendQuota.Cost specifications.
package quota_test

import (
	"testing"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/server/v3/storage"
	"go.uber.org/zap"
)

func TestQuotaPremises(t *testing.T) {
	q := storage.NewBackendQuota(zap.NewNop(), 0, nil, "test")
	for name, run := range map[string]func(){
		"nil put":     func() { q.Cost((*pb.PutRequest)(nil)) },
		"nil backend": func() { q.Available(&pb.LeaseGrantRequest{}) },
		"nil oneof wrapper": func() {
			q.Cost(&pb.TxnRequest{Success: []*pb.RequestOp{{Request: (*pb.RequestOp_RequestPut)(nil)}}})
		},
	} {
		t.Run(name, func(t *testing.T) {
			defer func() {
				if recover() == nil {
					t.Fatal("expected a panic")
				}
			}()
			run()
		})
	}
}
