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

package recipes_test

import (
	"testing"
	"time"

	"github.com/stretchr/testify/require"

	"go.etcd.io/etcd/client/v3/concurrency"
	recipe "go.etcd.io/etcd/client/v3/experimental/recipes"
	"go.etcd.io/etcd/tests/v3/framework/integration"
)

// TestBarrierWaitClientClosed checks that Barrier.Wait returns an error, not
// nil (released), when its client is closed while the barrier is held.
func TestBarrierWaitClientClosed(t *testing.T) {
	integration.BeforeTest(t)
	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 1})
	defer clus.Terminate(t)

	require.NoError(t, recipe.NewBarrier(clus.Client(0), "test-barrier").Hold())

	cli, err := clus.NewClientV3(0)
	require.NoError(t, err)
	errc := make(chan error, 1)
	go func() { errc <- recipe.NewBarrier(cli, "test-barrier").Wait() }()

	time.Sleep(500 * time.Millisecond)
	select {
	case err := <-errc:
		t.Fatalf("Wait returned %v while the barrier is held", err)
	default:
	}
	require.NoError(t, cli.Close())

	select {
	case err = <-errc:
	case <-time.After(10 * time.Second):
		t.Fatal("Wait did not return")
	}
	resp, gerr := clus.Client(0).Get(t.Context(), "test-barrier")
	require.NoError(t, gerr)
	require.Lenf(t, resp.Kvs, 1, "barrier key should still be held")
	require.Errorf(t, err, "Wait returned nil (released) while the barrier is held")
}

// TestDoubleBarrierEnterClientClosed checks that DoubleBarrier.Enter returns
// an error, not nil (barrier full), when its client is closed before the
// barrier is full.
func TestDoubleBarrierEnterClientClosed(t *testing.T) {
	integration.BeforeTest(t)
	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 1})
	defer clus.Terminate(t)

	cli, err := clus.NewClientV3(0)
	require.NoError(t, err)
	s, err := concurrency.NewSession(cli)
	require.NoError(t, err)
	errc := make(chan error, 1)
	go func() { errc <- recipe.NewDoubleBarrier(s, "test-barrier", 2).Enter() }()

	time.Sleep(500 * time.Millisecond)
	select {
	case err := <-errc:
		t.Fatalf("Enter returned %v with 1 of 2 entrants", err)
	default:
	}
	require.NoError(t, cli.Close())

	select {
	case err = <-errc:
	case <-time.After(10 * time.Second):
		t.Fatal("Enter did not return")
	}
	require.Errorf(t, err, "Enter returned nil with 1 of 2 entrants")
}
