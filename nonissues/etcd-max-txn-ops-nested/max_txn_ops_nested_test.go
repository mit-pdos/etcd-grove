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
)

func mtoPutOp(k string) *pb.RequestOp {
	return &pb.RequestOp{Request: &pb.RequestOp_RequestPut{RequestPut: &pb.PutRequest{Key: []byte(k)}}}
}

func mtoTxnOp(then ...*pb.RequestOp) *pb.RequestOp {
	return &pb.RequestOp{Request: &pb.RequestOp_RequestTxn{RequestTxn: &pb.TxnRequest{Success: then}}}
}

// TestMaxTxnOpsNested: --max-txn-ops ("Maximum number of operations permitted
// in a transaction") bounds each level of nesting, not the transaction.
func TestMaxTxnOpsNested(t *testing.T) {
	n := 0
	var mk func(d int) *pb.RequestOp
	mk = func(d int) *pb.RequestOp {
		n++
		if d == 0 {
			return mtoPutOp("k")
		}
		return mtoTxnOp(mk(d-1), mk(d-1), mk(d-1))
	}
	top := &pb.TxnRequest{Success: []*pb.RequestOp{mk(2), mk(2), mk(2)}}
	if err := checkTxnRequest(top, 9); err == nil && n > 9 {
		t.Errorf("a transaction with %d operations passes maxTxnOps=9", n)
	}
}
