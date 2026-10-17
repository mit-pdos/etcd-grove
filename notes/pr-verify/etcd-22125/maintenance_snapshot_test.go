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

package v3rpc

import (
	"errors"
	"io"
	"os"
	"path/filepath"
	"testing"
	"time"

	bolt "go.etcd.io/bbolt"
	"go.uber.org/zap/zaptest"
	"google.golang.org/grpc"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/server/v3/storage/backend"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
)

// shortSnapshot reports size bytes but WriteTo writes only written bytes and
// then returns err.
type shortSnapshot struct {
	size    int64
	written int
	err     error
}

func (s *shortSnapshot) Size() int64 { return s.size }
func (s *shortSnapshot) WriteTo(w io.Writer) (int64, error) {
	n, werr := w.Write(make([]byte, s.written))
	if werr != nil {
		return int64(n), werr
	}
	return int64(n), s.err
}
func (s *shortSnapshot) Close() error { return nil }

type snapBackend struct {
	backend.Backend
	snap backend.Snapshot
}

func (b *snapBackend) Snapshot() backend.Snapshot { return b.snap }

type snapBackendGetter struct{ b backend.Backend }

func (g snapBackendGetter) Backend() backend.Backend { return g.b }

type countingSnapshotServer struct {
	grpc.ServerStream
	sends int
}

func (s *countingSnapshotServer) Send(*pb.SnapshotResponse) error {
	s.sends++
	return nil
}

// runSnapshot runs maintenanceServer.Snapshot over a snapshot that writes 4096
// of its 3*snapshotSendBufferSize bytes and then fails with werr, and reports
// whether Snapshot returned within 5 seconds.
func runSnapshot(t *testing.T, werr error) (returned bool, err error) {
	be, _ := betesting.NewDefaultTmpBackend(t)
	defer betesting.Close(t, be)
	ms := &maintenanceServer{
		lg: zaptest.NewLogger(t),
		bg: snapBackendGetter{&snapBackend{Backend: be, snap: &shortSnapshot{
			size: 3 * snapshotSendBufferSize, written: 4096, err: werr,
		}}},
	}
	done := make(chan error, 1)
	go func() { done <- ms.Snapshot(&pb.SnapshotRequest{}, &countingSnapshotServer{}) }()
	select {
	case err = <-done:
		return true, err
	case <-time.After(5 * time.Second):
		return false, nil
	}
}

// The case the PR fixes: WriteTo fails with an I/O error. Fails (Snapshot never
// returns) before the PR; passes with it.
func TestSnapshotWriteToErrorReturns(t *testing.T) {
	returned, err := runSnapshot(t, errors.New("injected I/O error"))
	if !returned {
		t.Fatal("Snapshot did not return after WriteTo failed (busy loop on io.EOF)")
	}
	if err == nil {
		t.Fatal("Snapshot returned nil after WriteTo failed")
	}
}

// The case the PR leaves: WriteTo stops short and returns io.EOF, which is what
// bbolt's Tx.WriteTo returns when the database file is shorter than tx.Size()
// (TestBoltWriteToShortFileReturnsEOF). CloseWithError(io.EOF) is read as a
// normal end of stream. Fails before and after the PR.
func TestSnapshotWriteToEOFReturns(t *testing.T) {
	returned, err := runSnapshot(t, io.EOF)
	if !returned {
		t.Fatal("Snapshot did not return after WriteTo stopped short with io.EOF (busy loop on io.EOF)")
	}
	if err == nil {
		t.Fatal("Snapshot returned nil after a short snapshot")
	}
}

// bbolt's Tx.WriteTo copies tx.Size() bytes with io.CopyN, which returns io.EOF
// when the file holds fewer. Passes (shows the io.EOF), before and after the PR.
func TestBoltWriteToShortFileReturnsEOF(t *testing.T) {
	path := filepath.Join(t.TempDir(), "db")
	db, err := bolt.Open(path, 0o600, nil)
	if err != nil {
		t.Fatal(err)
	}
	defer db.Close()
	if err = db.Update(func(tx *bolt.Tx) error {
		b, err := tx.CreateBucket([]byte("b"))
		if err != nil {
			return err
		}
		for i := 0; i < 100; i++ {
			if err := b.Put([]byte{byte(i)}, make([]byte, 1024)); err != nil {
				return err
			}
		}
		return nil
	}); err != nil {
		t.Fatal(err)
	}
	tx, err := db.Begin(false)
	if err != nil {
		t.Fatal(err)
	}
	defer tx.Rollback()
	size := tx.Size()
	if err = os.Truncate(path, int64(3*db.Info().PageSize)); err != nil {
		t.Fatal(err)
	}
	n, err := tx.WriteTo(io.Discard)
	if !errors.Is(err, io.EOF) {
		t.Fatalf("WriteTo = %d, %v; want io.EOF", n, err)
	}
	t.Logf("tx.Size() = %d, WriteTo wrote %d and returned %v", size, n, err)
}
