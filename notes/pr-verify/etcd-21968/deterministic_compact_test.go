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

package model

import (
	"testing"
)

// TestModelCompactLatestRevisionTwice: with etcd-io/etcd#21968 the server answers
// a second compaction at the current revision with success. The robustness
// model must accept that answer, or a history containing it fails to linearize.
func TestModelCompactLatestRevisionTwice(t *testing.T) {
	m := NonDeterministicModel([]string{"key"})
	state := m.Init()
	steps := []struct {
		req  EtcdRequest
		resp MaybeEtcdResponse
	}{
		{putRequest("key", "1"), putResponse(2)},
		{compactRequest(2), compactResponse()},
		// What the server returns with the PR: success, no write in between.
		{compactRequest(2), compactResponse()},
	}
	for i, s := range steps {
		ok, next := m.Step(state, s.req, s.resp)
		if !ok {
			t.Fatalf("step %d (%s -> %s) rejected by the model; state %s", i,
				describeEtcdRequest(s.req), describeEtcdResponse(s.req, s.resp), m.DescribeState(state))
		}
		state = next
	}
}
