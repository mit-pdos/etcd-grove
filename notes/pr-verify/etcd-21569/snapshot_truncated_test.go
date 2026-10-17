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

package rafthttp

import (
	"io"
	"testing"

	"go.etcd.io/etcd/server/v3/etcdserver/api/snap"
	"go.etcd.io/raft/v3/raftpb"
)

// TestSnapshotSendTruncatedByEOF mirrors etcdserver's newSnapshotReaderCloser when
// the backend's WriteTo stops early with io.EOF (bbolt's Tx.WriteTo copies the db file
// with io.CopyN, which returns io.EOF when the file is shorter than the transaction's
// size): the pipe writer is closed with io.EOF, so the reader sees a normal end of
// stream after fewer bytes than the declared size. The transfer must fail and the
// receiver must not keep a database file.
func TestSnapshotSendTruncatedByEOF(t *testing.T) {
	const declared = 1 << 20
	pr, pw := io.Pipe()
	go func() {
		pw.Write(make([]byte, declared/4))
		pw.CloseWithError(io.EOF) // what WriteTo returned
	}()
	m := &raftpb.Message{Type: raftpb.MsgSnap.Enum(), To: new(uint64(1)), Snapshot: &raftpb.Snapshot{}}
	sent, files := testSnapshotSend(t, snap.NewMessage(m, pr, declared))
	if sent {
		t.Errorf("a snapshot truncated to %d of %d bytes was reported as sent", declared/4, declared)
	}
	if len(files) != 0 {
		t.Errorf("the receiver kept %d file(s) of a truncated snapshot: %v", len(files), files)
	}
}
