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

//go:build linux

package wal

import (
	"errors"
	"os"
	"path/filepath"
	"syscall"
	"testing"

	"github.com/stretchr/testify/require"
	"go.uber.org/zap/zaptest"

	"go.etcd.io/etcd/server/v3/storage/wal/walpb"
	"go.etcd.io/raft/v3/raftpb"
)

// withFDsExhausted runs f with every file descriptor of the process taken, so
// that opening a file or directory fails with EMFILE.
func withFDsExhausted(t *testing.T, f func()) {
	var lim syscall.Rlimit
	require.NoError(t, syscall.Getrlimit(syscall.RLIMIT_NOFILE, &lim))
	low := lim
	low.Cur = 512
	require.NoError(t, syscall.Setrlimit(syscall.RLIMIT_NOFILE, &low))
	defer func() { require.NoError(t, syscall.Setrlimit(syscall.RLIMIT_NOFILE, &lim)) }()
	var held []*os.File
	defer func() {
		for _, h := range held {
			h.Close()
		}
	}()
	for {
		h, err := os.Open(os.DevNull)
		if err != nil {
			require.ErrorIs(t, err, syscall.EMFILE)
			break
		}
		held = append(held, h)
	}
	f()
}

// TestExistReadDirError checks that Exist does not report "no WAL" when the
// WAL directory exists but cannot be read, and that Create then refuses to
// replace it: a transient ReadDir failure at startup must not make etcd
// bootstrap a new member over its WAL.
func TestExistReadDirError(t *testing.T) {
	dir := filepath.Join(t.TempDir(), "wal")
	lg := zaptest.NewLogger(t)
	w, err := Create(lg, dir, []byte("metadata"))
	require.NoError(t, err)
	ents := []*raftpb.Entry{{Index: new(uint64(1)), Term: new(uint64(1)), Data: []byte("data")}}
	require.NoError(t, w.Save(&raftpb.HardState{Term: new(uint64(1)), Commit: new(uint64(1))}, ents))
	require.NoError(t, w.Close())

	require.False(t, Exist(filepath.Join(t.TempDir(), "missing")), "Exist of a missing directory")

	withFDsExhausted(t, func() {
		if _, err := os.ReadDir(dir); err == nil {
			t.Fatal("reading the WAL directory succeeded with no file descriptor left")
		}
		require.True(t, Exist(dir), "Exist of a WAL directory that cannot be read")
		_, err := Create(lg, dir, []byte("other"))
		require.Truef(t, errors.Is(err, os.ErrExist), "Create over an unreadable WAL: err = %v, want os.ErrExist", err)
	})

	require.True(t, Exist(dir))
	w, err = Open(lg, dir, &walpb.Snapshot{})
	require.NoError(t, err)
	defer w.Close()
	md, _, got, err := w.ReadAll()
	require.NoError(t, err)
	require.Equal(t, []byte("metadata"), md)
	require.Len(t, got, 1)
	require.Equal(t, []byte("data"), got[0].GetData())
}
