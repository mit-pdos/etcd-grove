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

package v3compactor

import (
	"testing"
	"time"
)

// TestPeriodicTinyRetentionPanics shows that New in the periodic mode panics
// (integer divide by zero in getRetentions: period/retryDivisor is 0) for a
// retention of 1 to 9 ns, which parseCompactionRetention accepts ("5ns").
func TestPeriodicTinyRetentionPanics(t *testing.T) {
	for _, d := range []time.Duration{5 * time.Nanosecond, -5 * time.Nanosecond} {
		func() {
			defer func() {
				r := recover()
				t.Logf("New(periodic, %v): recovered panic: %v", d, r)
				if r == nil {
					t.Errorf("expected a panic for %v", d)
				}
			}()
			_, _ = New(nil, ModePeriodic, d, &countingRev{}, &negCompactable{})
		}()
	}
}
