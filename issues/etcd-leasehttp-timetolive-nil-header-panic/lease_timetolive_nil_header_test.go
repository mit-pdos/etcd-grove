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
	"context"
	"net/http"
	"net/http/httptest"
	"testing"

	"go.uber.org/zap"
	"google.golang.org/protobuf/proto"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/server/v3/etcdserver"
	"go.etcd.io/etcd/server/v3/lease"
	"go.etcd.io/etcd/server/v3/lease/leasehttp"
	"go.etcd.io/etcd/server/v3/lease/leasepb"
)

// forwardingLessor answers LeaseTimeToLive as EtcdServer.leaseTimeToLive does
// on a follower: it forwards the request to the leader's peer URL with
// leasehttp.TimeToLiveHTTP and returns the reply's LeaseTimeToLiveResponse.
type forwardingLessor struct {
	etcdserver.Lessor
	url string
}

func (l forwardingLessor) LeaseTimeToLive(ctx context.Context, r *pb.LeaseTimeToLiveRequest) (*pb.LeaseTimeToLiveResponse, error) {
	resp, err := leasehttp.TimeToLiveHTTP(ctx, lease.LeaseID(r.ID), r.Keys, l.url+leasehttp.LeaseInternalPrefix, http.DefaultTransport)
	if err != nil {
		return nil, err
	}
	return resp.LeaseTimeToLiveResponse, nil
}

// TestLeaseTimeToLiveForwardedReplyWithoutHeader: a peer URL answers the
// forwarded TimeToLive with 200 and a LeaseTimeToLiveResponse for the asked
// ID but without a Header. The gRPC handler should return an error, not panic.
func TestLeaseTimeToLiveForwardedReplyWithoutHeader(t *testing.T) {
	body, err := proto.Marshal(&leasepb.LeaseInternalResponse{
		LeaseTimeToLiveResponse: &pb.LeaseTimeToLiveResponse{ID: 1},
	})
	if err != nil {
		t.Fatal(err)
	}
	ts := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		w.WriteHeader(http.StatusOK)
		w.Write(body)
	}))
	defer ts.Close()

	ls := &LeaseServer{lg: zap.NewNop(), le: forwardingLessor{url: ts.URL}, hdr: header{rev: func() int64 { return 1 }}}
	defer func() {
		if r := recover(); r != nil {
			t.Fatalf("LeaseTimeToLive panicked: %v", r)
		}
	}()
	if _, err := ls.LeaseTimeToLive(context.Background(), &pb.LeaseTimeToLiveRequest{ID: 1}); err == nil {
		t.Fatal("LeaseTimeToLive accepted a forwarded reply without a header")
	}
}
