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

package tcpproxy

import (
	"testing"
	"time"
)

// TestRunMonitorNegativeInterval runs the endpoint monitor with a negative
// MonitorInterval (`etcd gateway start --retry-delay=-1s`; Run replaces only 0
// with its default). The monitor must keep running until the proxy stops, not
// panic.
func TestRunMonitorNegativeInterval(t *testing.T) {
	tp := &TCPProxy{MonitorInterval: -time.Second, donec: make(chan struct{})}
	res := make(chan any, 1)
	go func() {
		defer func() { res <- recover() }()
		tp.runMonitor()
	}()
	time.Sleep(50 * time.Millisecond)
	close(tp.donec)
	if r := <-res; r != nil {
		t.Fatalf("runMonitor panicked: %v", r)
	}
}
