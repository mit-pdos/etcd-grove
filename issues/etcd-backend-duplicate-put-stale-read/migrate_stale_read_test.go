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

package schema

import (
	"testing"
	"time"

	"go.uber.org/zap/zaptest"

	"go.etcd.io/etcd/api/v3/version"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
)

// TestMigrateStaleRead migrates a v3.5 backend (no storage version, a term) to v3.7 in one
// LockOutsideApply session, as the storage-version monitor does (UpdateStorageVersion), after a
// commit that left the meta bucket's read-buffer entry present. The session puts
// meta/storageVersion three times; afterwards ReadTx and BatchTx must agree on its value.
func TestMigrateStaleRead(t *testing.T) {
	lg := zaptest.NewLogger(t)
	be, _ := betesting.NewTmpBackend(t, time.Hour, 10000)
	defer betesting.Close(t, be)

	tx := be.BatchTx()
	tx.LockOutsideApply()
	UnsafeCreateMetaBucket(tx)
	UnsafeUpdateConsistentIndex(tx, 1, 1)
	tx.Unlock()
	be.ForceCommit()

	tx.LockOutsideApply()
	if err := UnsafeMigrate(lg, tx, nil, version.V3_7); err != nil {
		t.Fatal(err)
	}
	tx.Unlock()

	rv, rerr := DetectSchemaVersion(lg, be.ReadTx())
	tx.LockOutsideApply()
	bv := UnsafeReadStorageVersion(tx)
	tx.Unlock()
	if rerr != nil || bv == nil || rv.String() != bv.String() {
		t.Fatalf("ReadTx: %v (err %v); BatchTx: %v", rv, rerr, bv)
	}
}
