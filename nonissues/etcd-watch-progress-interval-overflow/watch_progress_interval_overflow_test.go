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

package watch

import (
	"context"
	"testing"
	"time"

	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/tests/v3/framework/integration"
)

// TestWatchHugeProgressNotifyInterval: a member configured with
// --watch-progress-notify-interval=2562047h (a duration time.ParseDuration accepts, about
// 47 minutes below the largest time.Duration) should serve watches. The jitter added to the
// interval overflows it to a negative duration, and the stream's time.NewTicker panics.
func TestWatchHugeProgressNotifyInterval(t *testing.T) {
	integration.BeforeTest(t)
	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 1, WatchProgressNotifyInterval: 2562047 * time.Hour})
	defer clus.Terminate(t)
	ctx, cancel := context.WithTimeout(t.Context(), 10*time.Second)
	defer cancel()
	wch := clus.Client(0).Watch(ctx, "k", clientv3.WithCreatedNotify())
	if resp, ok := <-wch; !ok || !resp.Created {
		t.Fatalf("watch not created: %v, %v", resp, ok)
	}
}
