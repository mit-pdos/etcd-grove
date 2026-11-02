package common

import (
	"context"
	"strings"
	"testing"
	"time"

	"github.com/stretchr/testify/require"

	"go.etcd.io/etcd/tests/v3/framework/config"
	"go.etcd.io/etcd/tests/v3/framework/testutils"
)

// TestRoleAddLongName: adding a role whose name is longer than bbolt's
// MaxKeySize (32768 bytes) should fail with an error, as an empty name does,
// and leave the cluster running.
func TestRoleAddLongName(t *testing.T) {
	testRunner.BeforeTest(t)
	ctx, cancel := context.WithTimeout(t.Context(), 10*time.Second)
	defer cancel()
	clus := testRunner.NewCluster(ctx, t, config.WithClusterSize(1))
	defer clus.Close()
	cc := testutils.MustClient(clus.Client())
	testutils.ExecuteUntil(ctx, t, func() {
		_, err := cc.RoleAdd(ctx, strings.Repeat("a", 32*1024+1))
		require.ErrorContainsf(t, err, "role name", "want an error for a role name longer than the maximum key size")
		_, err = cc.RoleAdd(ctx, "test-role")
		require.NoError(t, err)
	})
}

// TestUserAddLongName: the same for a user name.
func TestUserAddLongName(t *testing.T) {
	testRunner.BeforeTest(t)
	ctx, cancel := context.WithTimeout(t.Context(), 10*time.Second)
	defer cancel()
	clus := testRunner.NewCluster(ctx, t, config.WithClusterSize(1))
	defer clus.Close()
	cc := testutils.MustClient(clus.Client())
	testutils.ExecuteUntil(ctx, t, func() {
		_, err := cc.UserAdd(ctx, strings.Repeat("a", 32*1024+1), "foobar", config.UserAddOptions{})
		require.ErrorContainsf(t, err, "user name", "want an error for a user name longer than the maximum key size")
		_, err = cc.UserAdd(ctx, "test-user", "foobar", config.UserAddOptions{})
		require.NoError(t, err)
	})
}
