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
	"testing/synctest"
	"time"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	clientv3 "go.etcd.io/etcd/client/v3"
)

// TestCacheReadyAfterCompactionResync ensures that the cache becomes ready again
// once it has resynced after a compaction canceled its watch.
func TestCacheReadyAfterCompactionResync(t *testing.T) {
	synctest.Test(t, func(t *testing.T) {
		mw := newMockWatcher(16)
		fakeClient := &clientv3.Client{
			Watcher: mw,
			KV: newKVStub(
				&clientv3.GetResponse{Header: &pb.ResponseHeader{Revision: 5}},
				&clientv3.GetResponse{Header: &pb.ResponseHeader{Revision: 10}},
			),
		}
		cache, err := New(fakeClient, "")
		if err != nil {
			t.Fatalf("New cache: %v", err)
		}
		defer cache.Close()

		// The watch from revision 6 is created.
		mw.triggerCreatedNotify()
		synctest.Wait()
		if !cache.Ready() {
			t.Fatal("cache not ready after the first watch")
		}

		// A compaction at revision 10 cancels the watch. After the retry's back-off,
		// the cache resyncs at revision 10, and its watch from revision 11 is created.
		mw.errorCompacted(10)
		mw.triggerCreatedNotify()
		time.Sleep(time.Second)
		synctest.Wait()
		if !cache.Ready() {
			t.Fatal("cache not ready after the resync")
		}
	})
}
