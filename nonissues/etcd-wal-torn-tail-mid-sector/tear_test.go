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

package wal

import (
	"encoding/binary"
	"io"
	"os"
	"path/filepath"
	"testing"

	"github.com/stretchr/testify/require"
	"go.uber.org/zap/zaptest"

	"go.etcd.io/etcd/server/v3/storage/wal/walpb"
	"go.etcd.io/raft/v3/raftpb"
)

// TestReadAllTornTailMidSector: a Save whose write(2) was cut short inside a 512-byte sector,
// with the rest of the segment zero, as Linux can leave it after a power loss (below), reads back
// as a CRC mismatch instead of io.ErrUnexpectedEOF, so the server's bootstrap does not repair it
// and refuses to start.
//
// The image: the encoder's PageWriter flushes its buffer (a 132 KiB heap object, so page-aligned)
// to the file's current offset a, which is mid-page after any earlier Save. The buffer's first page
// boundary is at file offset a+4096, mid-page. Linux copies a write into the page cache with page
// faults disabled; when the second source page is momentarily unmapped (memory compaction migrating
// it), the copy stops there, the prefix is committed and the page cache page is unlocked, dirty,
// with the file's bytes up to a+4096 and zeros after (the preallocated segment), until the copy is
// retried. A writeback taking that page then (the flusher, or any sync of the file other than the
// Save's own fdatasync) writes it so, and a crash before the Save's fdatasync completes leaves it.
func TestReadAllTornTailMidSector(t *testing.T) {
	lg := zaptest.NewLogger(t)
	hs := func(c uint64) *raftpb.HardState {
		return &raftpb.HardState{Term: new(uint64(1)), Vote: new(uint64(1)), Commit: new(c)}
	}
	ent := func(i uint64, n int) *raftpb.Entry {
		d := make([]byte, n)
		for j := range d {
			d[j] = byte(j%251 + 1)
		}
		return &raftpb.Entry{Term: new(uint64(1)), Index: new(i), Data: d}
	}
	// Find sizes for which the record holding a+4096 starts before it and ends inside its sector
	// (with a later all-zero sector in the record, the decoder would call it torn).
	for n := 3000; n < 5000; n += 8 {
		p := t.TempDir()
		w, err := Create(lg, p, nil)
		require.NoError(t, err)
		require.NoError(t, w.Save(hs(0), []*raftpb.Entry{ent(1, 100)}))
		a, err := w.tail().Seek(0, io.SeekCurrent) // the next Save's flush starts here
		require.NoError(t, err)
		require.NoError(t, w.Save(hs(1), []*raftpb.Entry{ent(2, n), ent(3, 50)}))
		b, err := w.tail().Seek(0, io.SeekCurrent)
		require.NoError(t, err)
		require.NoError(t, w.Close())

		c := a + 4096 // the buffer's first page boundary
		if c%minSectorSize == 0 || c >= b {
			continue
		}
		names, err := filepath.Glob(filepath.Join(p, "*.wal"))
		require.NoError(t, err)
		f, err := os.OpenFile(names[0], os.O_RDWR, 0)
		require.NoError(t, err)
		buf := make([]byte, b-a)
		_, err = f.ReadAt(buf, a)
		require.NoError(t, err)
		var start, end int64
		for off := int64(0); off < b-a; {
			rb, pad := decodeFrameSize(int64(binary.LittleEndian.Uint64(buf[off:])))
			e := off + frameSizeBytes + rb + pad
			if a+off <= c && c < a+e {
				start, end = a+off, a+e
				break
			}
			off = e
		}
		if start+frameSizeBytes > c || end > c-c%minSectorSize+minSectorSize {
			f.Close()
			continue
		}
		// The crash image: the second Save's write landed up to c; zeros after.
		_, err = f.WriteAt(make([]byte, b-c), c)
		require.NoError(t, err)
		require.NoError(t, f.Close())
		t.Logf("flush [%d, %d), cut at %d (in its sector: %d), inside the record [%d, %d)", a, b, c, c%minSectorSize, start, end)

		w, err = Open(lg, p, &walpb.Snapshot{})
		require.NoError(t, err)
		_, _, ents, err := w.ReadAll()
		w.Close()
		// What bootstrap (openWALFromSnapshot) needs to repair the tail: io.ErrUnexpectedEOF.
		require.ErrorIs(t, err, io.ErrUnexpectedEOF, "read %d entries", len(ents))
		return
	}
	t.Fatal("no layout found")
}
