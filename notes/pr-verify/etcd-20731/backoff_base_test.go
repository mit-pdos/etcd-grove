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

package clientv3

import (
	"sync"
	"testing"
	"time"

	"go.uber.org/zap"
)

// Before PR #20731 (its base, 374dd8087): a BackoffWaitBetween of 10s gives a
// 10s backoff (jitter 0).
func TestBaseLargeWaitBetweenNotCapped(t *testing.T) {
	c := &Client{epMu: new(sync.RWMutex), endpoints: []string{"127.0.0.1:2379"}}
	c.lg.Store(zap.NewNop())
	wait := 10 * time.Second
	if got := c.roundRobinQuorumBackoff(wait, 0)(1); got != wait {
		t.Errorf("backoff = %v, want %v", got, wait)
	}
}
