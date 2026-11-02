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

package integration

import (
	"testing"
	"time"

	"github.com/stretchr/testify/require"

	"go.etcd.io/etcd/server/v3/etcdserver"
	"go.etcd.io/etcd/server/v3/etcdserver/api/v3compactor"
	"go.etcd.io/etcd/tests/v3/framework/integration"
)

// TestAutoCompactorNotRunBeforeStart checks that a server built by NewServer with auto-compaction
// on does not run the compactor until Start: the compactor's Compact calls go through the wait
// registry and the other fields start() sets, so a compaction proposed before Start dereferenced
// a nil wait registry and panicked.
func TestAutoCompactorNotRunBeforeStart(t *testing.T) {
	integration.BeforeTest(t)
	m := integration.MustNewMember(t, integration.MemberConfig{Name: "compactorBeforeStart"})
	m.AutoCompactionMode = v3compactor.ModePeriodic
	m.AutoCompactionRetention = time.Second

	srv, err := etcdserver.NewServer(m.ServerConfig)
	require.NoError(t, err)
	// Past the compactor's first period (one second, sampled every 100ms): a compactor running
	// from NewServer would have called Compact by now.
	time.Sleep(2 * time.Second)

	srv.Start()
	srv.HardStop()
}
