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

package embed

import (
	"testing"
	"time"
)

// TestParseCompactionRetentionDurationInRevisionMode shows that a duration
// retention ("5m", "-1h") is accepted, without an error, in the modes that
// interpret the retention as a revision count: "5m" becomes a retention of
// 300,000,000,000 revisions (the duration's nanoseconds), so the compactor
// never compacts, and "-1h" becomes a negative retention, so the compactor asks
// to compact at a revision above the current one, which fails every time.
func TestParseCompactionRetentionDurationInRevisionMode(t *testing.T) {
	modes := []string{CompactorModeRevision}
	if m, ok := any(CompactorModeAutoPeriodic).(string); ok {
		modes = append(modes, m)
	}
	for _, mode := range modes {
		for _, tc := range []struct {
			retention string
			want      time.Duration
		}{
			{"5m", 5 * time.Minute},
			{"-1h", -time.Hour},
		} {
			got, err := parseCompactionRetention(mode, tc.retention)
			if err != nil {
				t.Fatalf("mode %q retention %q: unexpected error %v", mode, tc.retention, err)
			}
			t.Logf("mode %q retention %q: revisions to keep = %d (no error)", mode, tc.retention, int64(got))
			if got != tc.want {
				t.Fatalf("mode %q retention %q: got %d, want %d", mode, tc.retention, int64(got), int64(tc.want))
			}
		}
	}
	// the periodic mode accepts a negative duration too
	got, err := parseCompactionRetention(CompactorModePeriodic, "-1h")
	t.Logf("mode periodic retention -1h: %v, err %v", got, err)
}
