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

package version

import (
	"context"
	"testing"

	"github.com/Masterminds/semver/v3"
	"go.uber.org/zap/zaptest"
)

// TestDowngradeValidateAtMinorZero: at a cluster version x.0 (3.0 is MinClusterVersion, which
// the monitor decides while a member's version is unknown) there is no allowed downgrade
// target; allowedDowngradeVersion computes Minor()-1 on a uint64 and allows
// 3.18446744073709551615.
func TestDowngradeValidateAtMinorZero(t *testing.T) {
	cv := semver.New(3, 0, 0, "", "")
	if got := allowedDowngradeVersion(cv); got.Minor() > cv.Minor() {
		t.Errorf("allowedDowngradeVersion(%v) = %v: a higher minor version", cv, got)
	}
	s := &storageMock{clusterVersion: cv}
	m := NewManager(zaptest.NewLogger(t), s)
	target := semver.MustParse("3.18446744073709551615.0")
	if err := m.DowngradeValidate(context.Background(), target); err == nil {
		t.Errorf("DowngradeValidate(%v) at cluster version %v = nil; want an error", target, cv)
	}
}
