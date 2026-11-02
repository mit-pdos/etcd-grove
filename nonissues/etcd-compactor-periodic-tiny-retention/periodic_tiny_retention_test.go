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

	"go.uber.org/zap/zaptest"

	"go.etcd.io/etcd/server/v3/etcdserver/api/v3compactor"
)

// TestPeriodicTinyRetention follows --auto-compaction-mode=periodic
// --auto-compaction-retention=5ns from the flag to the compactor that
// NewServer creates: the value must be rejected with an error, or the
// compactor created without a panic.
func TestPeriodicTinyRetention(t *testing.T) {
	ret, err := parseCompactionRetention(CompactorModePeriodic, "5ns")
	if err != nil {
		return // rejected
	}
	defer func() {
		if r := recover(); r != nil {
			t.Fatalf("retention %v accepted, then v3compactor.New panicked: %v", ret, r)
		}
	}()
	if _, err := v3compactor.New(zaptest.NewLogger(t), v3compactor.ModePeriodic, ret, nil, nil); err != nil {
		return // rejected
	}
}
