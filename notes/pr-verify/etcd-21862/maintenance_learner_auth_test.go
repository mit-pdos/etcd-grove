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

package clientv3test

import (
	"testing"
	"time"

	"github.com/stretchr/testify/require"

	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/tests/v3/framework/integration"
)

// With auth enabled, a client that dials only the learner cannot get a token
// (Authenticate is not served by a learner), so it cannot defragment the
// learner even with etcd-io/etcd#21862.
func TestMaintenanceDefragmentLearnerAuthLearnerOnly(t *testing.T) {
	integration.BeforeTest(t)

	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 3, DisableStrictReconfigCheck: true})
	defer clus.Terminate(t)
	clus.AddAndLaunchLearnerMember(t)
	learner := clus.Members[3]
	<-learner.ReadyNotify()

	authSetupRoot(t, clus.Client(0).Auth)

	_, err := integration.NewClient(t, clientv3.Config{
		Endpoints:   []string{learner.GRPCURL},
		DialTimeout: 5 * time.Second,
		Username:    "root",
		Password:    "123",
	})
	t.Logf("learner-only client with auth: %v", err)
	require.ErrorContains(t, err, "rpc not supported for learner")
}

// With auth enabled, a client that authenticates on a voter can defragment the
// learner through Maintenance.Defragment(ctx, learnerEndpoint).
func TestMaintenanceDefragmentLearnerAuthViaVoter(t *testing.T) {
	integration.BeforeTest(t)

	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 3, DisableStrictReconfigCheck: true})
	defer clus.Terminate(t)
	clus.AddAndLaunchLearnerMember(t)
	learner := clus.Members[3]
	<-learner.ReadyNotify()

	authSetupRoot(t, clus.Client(0).Auth)

	cli, err := integration.NewClient(t, clientv3.Config{
		Endpoints:   []string{clus.Members[0].GRPCURL},
		DialTimeout: 5 * time.Second,
		Username:    "root",
		Password:    "123",
	})
	require.NoError(t, err)
	defer cli.Close()

	_, err = cli.Defragment(t.Context(), learner.GRPCURL)
	require.NoError(t, err)
}
