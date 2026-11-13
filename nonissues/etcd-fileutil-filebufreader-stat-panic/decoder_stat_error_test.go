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
	"os"
	"path/filepath"
	"testing"

	"github.com/stretchr/testify/require"

	"go.etcd.io/etcd/client/pkg/v3/fileutil"
	"go.etcd.io/etcd/server/v3/storage/wal/walpb"
)

// TestDecoderStatError: a WAL file whose fstat fails (here: its descriptor is already closed, the
// file is the one Open, ValidSnapshotEntries and Repair hand to the decoder) makes the decoder
// report the error from Decode instead of panicking in NewDecoder.
func TestDecoderStatError(t *testing.T) {
	p := filepath.Join(t.TempDir(), walName(0, 0))
	f, err := os.Create(p)
	require.NoError(t, err)
	require.NoError(t, f.Close())

	var d Decoder
	require.NotPanics(t, func() { d = NewDecoder(fileutil.NewFileReader(f)) })
	err = d.Decode(&walpb.Record{})
	require.ErrorIs(t, err, os.ErrClosed)
}
