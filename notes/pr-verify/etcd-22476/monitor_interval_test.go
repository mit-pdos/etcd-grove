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

package etcdserver

import (
	"sync"
	"testing"
	"time"

	"go.uber.org/zap/zaptest"

	"go.etcd.io/etcd/server/v3/config"
)

// TestMonitorDowngradeNegativeInterval runs monitorDowngrade with a negative
// --downgrade-check-time, which no configuration check rejects (only 0 is
// special-cased: the monitor is disabled). The member is not the leader, so
// each tick only checks that. The monitor must keep running until the server
// stops, not panic.
func TestMonitorDowngradeNegativeInterval(t *testing.T) {
	s := &EtcdServer{
		lgMu:     new(sync.RWMutex),
		lg:       zaptest.NewLogger(t),
		Cfg:      config.ServerConfig{DowngradeCheckTime: -time.Second},
		stopping: make(chan struct{}),
		memberID: 1,
	}
	s.lead.Store(2) // another member leads
	res := make(chan any, 1)
	go func() {
		defer func() { res <- recover() }()
		s.monitorDowngrade()
	}()
	time.Sleep(50 * time.Millisecond)
	close(s.stopping)
	if r := <-res; r != nil {
		t.Fatalf("monitorDowngrade panicked: %v", r)
	}
}
