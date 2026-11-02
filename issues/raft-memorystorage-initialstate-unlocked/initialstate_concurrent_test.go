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

package raft

import (
	"testing"

	"github.com/stretchr/testify/require"

	pb "go.etcd.io/raft/v3/raftpb"
)

// TestStorageInitialStateConcurrent checks that InitialState does not race
// with a concurrent SetHardState (the race detector reports it).
func TestStorageInitialStateConcurrent(t *testing.T) {
	s := NewMemoryStorage()
	errc := make(chan error)
	go func() {
		errc <- s.SetHardState(&pb.HardState{Term: new(uint64(1))})
	}()
	_, _, err := s.InitialState()
	require.NoError(t, err)
	require.NoError(t, <-errc)
}
