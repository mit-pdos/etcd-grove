// Copyright 2026 The etcd Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

package v3rpc

import (
	"testing"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/api/v3/v3rpc/rpctypes"
)

// TestCheckIntervalsFromKeyDelete is the finding's unit test
// (issues/etcd-txn-delete-then-ignore-put.md, fork branch txn-delete-then-ignore-put
// d9ba0e03c), as a file of its own. getError is key_test.go's.
func TestCheckIntervalsFromKeyDelete(t *testing.T) {
	// a DeleteRange with RangeEnd "\x00" deletes every key from Key on
	// (clientv3.WithFromKey)
	delFromKey := func(key string) *pb.RequestOp {
		return &pb.RequestOp{Request: &pb.RequestOp_RequestDeleteRange{
			RequestDeleteRange: &pb.DeleteRangeRequest{Key: []byte(key), RangeEnd: []byte{0}},
		}}
	}
	put := func(key string) *pb.RequestOp {
		return &pb.RequestOp{Request: &pb.RequestOp_RequestPut{
			RequestPut: &pb.PutRequest{Key: []byte(key), IgnoreValue: true},
		}}
	}
	nested := func(ops ...*pb.RequestOp) *pb.RequestOp {
		return &pb.RequestOp{Request: &pb.RequestOp_RequestTxn{
			RequestTxn: &pb.TxnRequest{Success: ops},
		}}
	}

	tests := []struct {
		name string
		reqs []*pb.RequestOp
		werr error
	}{
		{"put of the key", []*pb.RequestOp{delFromKey("a"), put("a")}, rpctypes.ErrGRPCDuplicateKey},
		{"put of a greater key", []*pb.RequestOp{delFromKey("a"), put("zzz")}, rpctypes.ErrGRPCDuplicateKey},
		{"put before the delete", []*pb.RequestOp{put("a"), delFromKey("a")}, rpctypes.ErrGRPCDuplicateKey},
		{"put in a nested txn", []*pb.RequestOp{delFromKey("a"), nested(put("b"))}, rpctypes.ErrGRPCDuplicateKey},
		{"delete in a nested txn", []*pb.RequestOp{nested(delFromKey("a")), put("b")}, rpctypes.ErrGRPCDuplicateKey},
		{"delete of every key", []*pb.RequestOp{delFromKey("\x00"), put("a")}, rpctypes.ErrGRPCDuplicateKey},
		{"put of a smaller key", []*pb.RequestOp{delFromKey("b"), put("a")}, nil},
		{"put of a smaller key in a nested txn", []*pb.RequestOp{delFromKey("b"), nested(put("a"))}, nil},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			_, _, err := checkIntervals(tt.reqs)
			if getError(err) != getError(tt.werr) {
				t.Errorf("checkIntervals: got %v, want %v", err, tt.werr)
			}
		})
	}
}

// TestCheckIntervalsClearAndReseed: the "clear and re-seed" txn
// Then(OpDelete("", WithPrefix()), OpPut("cfg", v)), which clientv3 sends as a delete with
// Key = RangeEnd = "\x00". With etcd#22395 it is rejected as a duplicate key; upstream main
// accepts it (this test then fails with "got <nil>").
func TestCheckIntervalsClearAndReseed(t *testing.T) {
	reqs := []*pb.RequestOp{
		{Request: &pb.RequestOp_RequestDeleteRange{RequestDeleteRange: &pb.DeleteRangeRequest{Key: []byte{0}, RangeEnd: []byte{0}}}},
		{Request: &pb.RequestOp_RequestPut{RequestPut: &pb.PutRequest{Key: []byte("cfg"), Value: []byte("v")}}},
	}
	_, _, err := checkIntervals(reqs)
	if getError(err) != getError(rpctypes.ErrGRPCDuplicateKey) {
		t.Errorf("checkIntervals(delete all, put cfg): got %v, want %v", err, rpctypes.ErrGRPCDuplicateKey)
	}
}
