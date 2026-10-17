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
	"errors"
	"net"
	"testing"
	"time"

	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/client/v3/concurrency"
)

// unreachableClient returns a client whose only endpoint refuses connections.
func unreachableClient(t *testing.T) *clientv3.Client {
	t.Helper()
	l, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	addr := l.Addr().String()
	l.Close()
	cli, err := clientv3.New(clientv3.Config{Endpoints: []string{addr}})
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { cli.Close() })
	return cli
}

func newSessionWithin(cli *clientv3.Client, d time.Duration, opts ...concurrency.SessionOption) (err error, returned bool) {
	errc := make(chan error, 1)
	go func() {
		s, err := concurrency.NewSession(cli, opts...)
		if s != nil {
			s.Orphan()
		}
		errc <- err
	}()
	select {
	case err := <-errc:
		return err, true
	case <-time.After(d):
		return nil, false
	}
}

// TestNewSessionNoCreationTimeoutBlocks: without the option, NewSession blocks while
// no endpoint is reachable (etcd-io/etcd#14631).
func TestNewSessionNoCreationTimeoutBlocks(t *testing.T) {
	if _, returned := newSessionWithin(unreachableClient(t), 2*time.Second); returned {
		t.Fatal("NewSession returned while no endpoint was reachable")
	}
}

// TestNewSessionCreationTimeout: with WithCreationTimeout, it returns DeadlineExceeded.
func TestNewSessionCreationTimeout(t *testing.T) {
	err, returned := newSessionWithin(unreachableClient(t), 5*time.Second,
		concurrency.WithCreationTimeout(500*time.Millisecond))
	if !returned || !errors.Is(err, context.DeadlineExceeded) {
		t.Fatalf("returned=%v err=%v, want DeadlineExceeded", returned, err)
	}
}

// TestNewSessionCreationTimeoutNonPositiveKeepsEarlier: WithCreationTimeout(0) after
// WithCreationTimeout(500ms) keeps the 500ms timeout (and logs a warning), although the
// option's documentation says "If timeout is <= 0, no timeout will be used".
func TestNewSessionCreationTimeoutNonPositiveKeepsEarlier(t *testing.T) {
	err, returned := newSessionWithin(unreachableClient(t), 5*time.Second,
		concurrency.WithCreationTimeout(500*time.Millisecond), concurrency.WithCreationTimeout(0))
	if !returned || !errors.Is(err, context.DeadlineExceeded) {
		t.Fatalf("returned=%v err=%v, want DeadlineExceeded (the earlier timeout kept)", returned, err)
	}
}

// TestNewSessionCreationTimeoutWithLease: with an existing lease (WithLease), NewSession
// does not call Grant, so the creation timeout bounds nothing; NewSession returns at once
// even though no endpoint is reachable (KeepAlive does not wait for the server).
func TestNewSessionCreationTimeoutWithLease(t *testing.T) {
	err, returned := newSessionWithin(unreachableClient(t), 2*time.Second,
		concurrency.WithLease(clientv3.LeaseID(12345)), concurrency.WithCreationTimeout(time.Hour))
	if !returned || err != nil {
		t.Fatalf("returned=%v err=%v, want an immediate nil", returned, err)
	}
}
