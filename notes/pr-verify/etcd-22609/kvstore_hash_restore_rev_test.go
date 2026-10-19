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

package mvcc

import (
	"testing"

	"go.uber.org/zap/zaptest"

	"go.etcd.io/etcd/server/v3/lease"
	"go.etcd.io/etcd/server/v3/storage/backend"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
)

// gatedHashBackend blocks in Hash until released.
type gatedHashBackend struct {
	backend.Backend
	inHash  chan struct{}
	release chan struct{}
}

func (b *gatedHashBackend) Hash(ignores func(bucketName, keyName []byte) bool) (uint32, error) {
	close(b.inHash)
	<-b.release
	return b.Backend.Hash(ignores)
}

// gatedReadTxBackend blocks in its first ReadTx (Restore's restore() scan) until released.
type gatedReadTxBackend struct {
	backend.Backend
	inReadTx chan struct{}
	release  chan struct{}
	once     bool
}

func (b *gatedReadTxBackend) ReadTx() backend.ReadTx {
	if !b.once {
		b.once = true
		close(b.inReadTx)
		<-b.release
	}
	return b.Backend.ReadTx()
}

// TestHashRevisionDuringRestore shows that Hash can return the revision Restore
// sets transiently (1) together with the hash of the backend Restore replaced:
// hash reads s.b under s.mu but currentRev only under revMu, which Restore
// releases while it still holds s.mu and rebuilds the index.
func TestHashRevisionDuringRestore(t *testing.T) {
	b0, _ := betesting.NewDefaultTmpBackend(t)
	gb := &gatedHashBackend{Backend: b0, inHash: make(chan struct{}), release: make(chan struct{})}
	s := NewStore(zaptest.NewLogger(t), gb, &lease.FakeLessor{}, StoreConfig{})
	for i := 0; i < 10; i++ {
		s.Put([]byte("foo"), []byte("bar"), lease.NoLease)
	}
	wantRev := s.Rev() // 11

	nb, _ := betesting.NewDefaultTmpBackend(t)
	s2 := NewStore(zaptest.NewLogger(t), nb, &lease.FakeLessor{}, StoreConfig{})
	for i := 0; i < 20; i++ {
		s2.Put([]byte("foo"), []byte("bar2"), lease.NoLease)
	}
	s2.Close()
	gnb := &gatedReadTxBackend{Backend: nb, inReadTx: make(chan struct{}), release: make(chan struct{})}

	type res struct {
		rev int64
		err error
	}
	hc := make(chan res, 1)
	go func() {
		_, rev, err := s.hash()
		hc <- res{rev, err}
	}()
	<-gb.inHash // hash has committed under s.mu and released it

	rc := make(chan error, 1)
	go func() { rc <- s.Restore(gnb) }()
	<-gnb.inReadTx // Restore holds s.mu, has set currentRev = 1, is about to rebuild the index

	close(gb.release)
	r := <-hc
	close(gnb.release)
	if err := <-rc; err != nil {
		t.Fatal(err)
	}
	if r.err != nil {
		t.Fatal(r.err)
	}
	t.Logf("hash of the old backend (at revision %d) returned with revision %d; store now at %d",
		wantRev, r.rev, s.Rev())
	if r.rev < wantRev {
		t.Errorf("hash returned revision %d, below the revision %d it hashed (Restore's transient value)", r.rev, wantRev)
	}
	cleanup(s, nb)
	b0.Close()
}
