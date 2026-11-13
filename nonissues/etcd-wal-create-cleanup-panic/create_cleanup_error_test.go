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
	"strings"
	"testing"

	"github.com/stretchr/testify/require"
	"go.uber.org/zap/zaptest"
)

// A WAL directory name of 240 bytes: "<name>.tmp" fits in a file name (255 bytes), but the name
// Create's cleanup renames a failed WAL to, "<name>.broken.<timestamp>", does not, so that rename
// fails with ENAMETOOLONG.
func longWALDirName() string { return strings.Repeat("w", 240) }

// TestCreateFailsAfterRenameWithoutPanic: Create's error path after the WAL directory was renamed
// into place (here: the parent cannot be opened to fsync it, being write-only) moves the WAL to a
// ".broken" name; when that rename fails, Create returns an error instead of panicking.
func TestCreateFailsAfterRenameWithoutPanic(t *testing.T) {
	if os.Geteuid() == 0 {
		t.Skip("root ignores directory permissions")
	}
	parent := filepath.Join(t.TempDir(), "data")
	require.NoError(t, os.Mkdir(parent, 0o300)) // write and search, no read: OpenDir(parent) fails
	defer os.Chmod(parent, 0o700)
	dir := filepath.Join(parent, longWALDirName())

	var err error
	require.NotPanics(t, func() { _, err = Create(zaptest.NewLogger(t), dir, []byte("data")) })
	require.Error(t, err)
}

// TestCleanupWALRenameFails: cleanupWAL, which Create runs when it fails after renaming the WAL
// directory into place, returns the error of its rename instead of panicking.
func TestCleanupWALRenameFails(t *testing.T) {
	dir := filepath.Join(t.TempDir(), longWALDirName())
	lg := zaptest.NewLogger(t)
	w, err := Create(lg, dir, []byte("data"))
	require.NoError(t, err)

	// At the fork's fix (f15d88841) the test also checks the returned error: err = w.cleanupWAL(lg).
	require.NotPanics(t, func() { w.cleanupWAL(lg) })
	require.DirExists(t, dir)
}
