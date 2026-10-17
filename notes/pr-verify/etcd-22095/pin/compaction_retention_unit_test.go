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

// TestParseCompactionRetentionRevisionModeDuration shows that the revision mode
// accepts a duration retention without an error and reads it as a revision
// count: "5m" keeps 300,000,000,000 revisions (the duration's nanoseconds), so
// the compactor never compacts; "-1h" gives a negative retention, so the
// compactor asks to compact above the current revision, which fails at every
// interval. Neither is reported to the operator at startup.
func TestParseCompactionRetentionRevisionModeDuration(t *testing.T) {
	for _, tc := range []struct {
		retention string
		want      time.Duration
	}{
		{"5m", 5 * time.Minute},
		{"-1h", -time.Hour},
	} {
		got, err := parseCompactionRetention(CompactorModeRevision, tc.retention)
		if err != nil {
			t.Fatalf("retention %q: unexpected error %v", tc.retention, err)
		}
		t.Logf("mode revision, retention %q: revisions to keep = %d (no error)", tc.retention, int64(got))
		if got != tc.want {
			t.Fatalf("retention %q: got %d, want %d", tc.retention, int64(got), int64(tc.want))
		}
	}
	got, err := parseCompactionRetention(CompactorModePeriodic, "-1h")
	if err != nil || got >= 0 {
		t.Fatalf("periodic -1h: got %v, %v", got, err)
	}
	t.Logf("mode periodic, retention \"-1h\": %v (no error)", got)
}
