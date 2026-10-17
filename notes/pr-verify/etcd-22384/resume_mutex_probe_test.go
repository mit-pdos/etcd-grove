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

package concurrency_test

import (
	"context"
	"testing"
	"time"

	"github.com/stretchr/testify/require"

	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/client/v3/concurrency"
	integration2 "go.etcd.io/etcd/tests/v3/framework/integration"
)

// TestProbeMutexHeaderRevisionIsNotMyRev: after a contended Lock, Header().Revision is the revision
// of Lock's last Get, not the key's create revision, so a caller cannot take the myRev argument of
// ResumeMutex from the Mutex itself (it has no Rev(), unlike Election); it needs an extra Get.
func TestProbeMutexHeaderRevisionIsNotMyRev(t *testing.T) {
	const prefix = "/probe-hdr"
	cli, err := integration2.NewClient(t, clientv3.Config{Endpoints: exampleEndpoints()})
	require.NoError(t, err)
	defer cli.Close()

	s1, err := concurrency.NewSession(cli)
	require.NoError(t, err)
	defer s1.Close()
	s2, err := concurrency.NewSession(cli)
	require.NoError(t, err)
	defer s2.Close()

	m1 := concurrency.NewMutex(s1, prefix)
	require.NoError(t, m1.Lock(t.Context()))

	m2 := concurrency.NewMutex(s2, prefix)
	done := make(chan error, 1)
	go func() { done <- m2.Lock(t.Context()) }()
	time.Sleep(200 * time.Millisecond)
	// some unrelated writes, so that revisions move on
	for i := 0; i < 3; i++ {
		_, err = cli.Put(t.Context(), "/probe-other", "x")
		require.NoError(t, err)
	}
	require.NoError(t, m1.Unlock(t.Context()))
	require.NoError(t, <-done)

	g, err := cli.Get(t.Context(), m2.Key())
	require.NoError(t, err)
	require.Len(t, g.Kvs, 1)
	createRev := g.Kvs[0].CreateRevision
	t.Logf("m2.Header().Revision = %d, create revision of m2.Key() = %d", m2.Header().Revision, createRev)
	require.NotEqual(t, createRev, m2.Header().Revision)

	// Resuming with the header's revision gives a handle that is not the owner.
	bad := concurrency.ResumeMutex(s2, prefix, m2.Key(), m2.Header().Revision)
	tr, err := cli.Txn(t.Context()).If(bad.IsOwner()).Commit()
	require.NoError(t, err)
	require.False(t, tr.Succeeded)
}

// TestProbeLockAlreadyResumes: a restarted process with the surviving lease (WithLease) gets its
// lock back with a fresh NewMutex + Lock, without waiting, even while another session is queued:
// tryAcquire finds its key and its create revision. ResumeMutex is not needed for that; what it adds
// is a handle without an RPC (and one whose IsOwner can be checked without Lock blocking when the
// process is not the owner).
func TestProbeLockAlreadyResumes(t *testing.T) {
	const prefix = "/probe-relock"
	cli, err := integration2.NewClient(t, clientv3.Config{Endpoints: exampleEndpoints()})
	require.NoError(t, err)
	defer cli.Close()

	s1, err := concurrency.NewSession(cli)
	require.NoError(t, err)
	defer s1.Close()
	m1 := concurrency.NewMutex(s1, prefix)
	require.NoError(t, m1.Lock(t.Context()))

	// another session queued behind m1
	s3, err := concurrency.NewSession(cli)
	require.NoError(t, err)
	defer s3.Close()
	m3 := concurrency.NewMutex(s3, prefix)
	ctx3, cancel3 := context.WithCancel(t.Context())
	defer cancel3()
	go m3.Lock(ctx3)
	time.Sleep(200 * time.Millisecond)

	// "restart": a new session on the same lease, a new mutex
	s1b, err := concurrency.NewSession(cli, concurrency.WithLease(s1.Lease()))
	require.NoError(t, err)
	m1b := concurrency.NewMutex(s1b, prefix)
	ctx, cancel := context.WithTimeout(t.Context(), 2*time.Second)
	defer cancel()
	require.NoError(t, m1b.Lock(ctx))
	require.Equal(t, m1.Key(), m1b.Key())
	tr, err := cli.Txn(t.Context()).If(m1b.IsOwner()).Commit()
	require.NoError(t, err)
	require.True(t, tr.Succeeded)
}

// TestProbeResumeMutexSlashedPrefix: ResumeMutex adds "/" to pfx, as NewMutex does (ResumeElection
// does not). A caller that passes the prefix with the "/" (e.g. taken from the key) gets a handle
// whose Unlock refuses the key, and whose Lock would use another prefix ("pfx//").
func TestProbeResumeMutexSlashedPrefix(t *testing.T) {
	const prefix = "/probe-slash"
	cli, err := integration2.NewClient(t, clientv3.Config{Endpoints: exampleEndpoints()})
	require.NoError(t, err)
	defer cli.Close()

	s1, err := concurrency.NewSession(cli)
	require.NoError(t, err)
	defer s1.Close()
	m1 := concurrency.NewMutex(s1, prefix)
	require.NoError(t, m1.Lock(t.Context()))
	g, err := cli.Get(t.Context(), m1.Key())
	require.NoError(t, err)
	rev := g.Kvs[0].CreateRevision

	ok := concurrency.ResumeMutex(s1, prefix, m1.Key(), rev)
	bad := concurrency.ResumeMutex(s1, prefix+"/", m1.Key(), rev)
	err = bad.Unlock(t.Context())
	require.Error(t, err)
	t.Logf("Unlock with a slashed prefix: %v", err)
	require.NoError(t, ok.Unlock(t.Context()))
}
