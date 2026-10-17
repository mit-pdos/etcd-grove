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

package cache

import (
	"testing"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
)

// A cached from-key range (RangeEnd "\x00", clientv3.WithFromKey) must be invalidated by a
// write of a key in it, and a from-key delete must invalidate the cached ranges it overlaps
// (issues/etcd-grpcproxy-cache-from-key.md). Both subtests fail on upstream main and with
// etcd#22395, which leaves store.go alone.
func TestCacheFromKeyInvalidate(t *testing.T) {
	t.Run("cached from-key range, put of a key in it", func(t *testing.T) {
		c := NewCache(DefaultMaxEntries)
		req := &pb.RangeRequest{Key: []byte("a"), RangeEnd: []byte{0}}
		c.Add(req, &pb.RangeResponse{})
		c.Invalidate([]byte("b"), nil) // what the proxy's Put("b") does
		if _, err := c.Get(req); err == nil {
			t.Errorf("cached range [a, +inf) still served after a put of b")
		}
	})
	t.Run("cached range, from-key delete over it", func(t *testing.T) {
		c := NewCache(DefaultMaxEntries)
		req := &pb.RangeRequest{Key: []byte("b"), RangeEnd: []byte("z")}
		c.Add(req, &pb.RangeResponse{})
		c.Invalidate([]byte("a"), []byte{0}) // what the proxy's DeleteRange("a", WithFromKey()) does
		if _, err := c.Get(req); err == nil {
			t.Errorf("cached range [b, z) still served after a delete of [a, +inf)")
		}
	})
}
