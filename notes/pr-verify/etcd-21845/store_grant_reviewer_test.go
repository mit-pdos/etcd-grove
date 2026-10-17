package auth

import (
	"bytes"
	"fmt"
	"math/rand"
	"testing"

	"github.com/stretchr/testify/require"

	"go.etcd.io/etcd/api/v3/authpb"
	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
)

func revSetupRole(t *testing.T, as *authStore) {
	_, err := as.RoleAdd(&pb.AuthRoleAddRequest{Name: "rr"})
	require.NoError(t, err)
	_, err = as.UserGrantRole(&pb.AuthUserGrantRoleRequest{User: "foo", Role: "rr"})
	require.NoError(t, err)
}

func revGetPerms(t *testing.T, as *authStore) []*authpb.Permission {
	tx := as.be.BatchTx()
	tx.Lock()
	defer tx.Unlock()
	return tx.UnsafeGetRole("rr").KeyPermission
}

// Random grants/revokes over few keys and many range ends (so a role holds >12
// permissions and sort.Sort is not insertion sort), against a map model.
func TestReviewerGrantRandomVsModel(t *testing.T) {
	as, tearDown := setupAuthStore(t)
	defer tearDown(t)
	revSetupRole(t, as)
	rng := rand.New(rand.NewSource(1))
	keys := []string{"k1", "k2", "k3"}
	model := map[[2]string]authpb.Permission_Type{}
	for step := 0; step < 3000; step++ {
		k := keys[rng.Intn(len(keys))]
		e := fmt.Sprintf("%s~%02d", k, rng.Intn(20))
		if rng.Intn(4) == 0 {
			e = "" // single key
		}
		var re []byte
		if e != "" {
			re = []byte(e)
		}
		if rng.Intn(5) == 0 {
			_, err := as.RoleRevokePermission(&pb.AuthRoleRevokePermissionRequest{Role: "rr", Key: []byte(k), RangeEnd: re})
			if _, ok := model[[2]string{k, e}]; ok {
				require.NoError(t, err)
				delete(model, [2]string{k, e})
			} else {
				require.ErrorIs(t, err, ErrPermissionNotGranted)
			}
		} else {
			pt := authpb.Permission_Type(rng.Intn(3))
			_, err := as.RoleGrantPermission(&pb.AuthRoleGrantPermissionRequest{Name: "rr",
				Perm: &authpb.Permission{Key: []byte(k), RangeEnd: re, PermType: pt}})
			require.NoError(t, err)
			model[[2]string{k, e}] = pt
		}
		perms := revGetPerms(t, as)
		require.Equal(t, len(model), len(perms), "step %d", step)
		for i, p := range perms {
			if i > 0 {
				require.True(t, bytes.Compare(perms[i-1].Key, p.Key) <= 0, "unsorted at step %d", step)
			}
			pt, ok := model[[2]string{string(p.Key), string(p.RangeEnd)}]
			require.True(t, ok)
			require.Equal(t, pt, p.PermType, "step %d", step)
		}
	}
	t.Logf("final role size %d", len(revGetPerms(t, as)))
}

// nil and empty RangeEnd are the same range.
func TestReviewerGrantNilVsEmptyRangeEnd(t *testing.T) {
	as, tearDown := setupAuthStore(t)
	defer tearDown(t)
	revSetupRole(t, as)
	_, err := as.RoleGrantPermission(&pb.AuthRoleGrantPermissionRequest{Name: "rr",
		Perm: &authpb.Permission{Key: []byte("a"), RangeEnd: nil, PermType: authpb.WRITE}})
	require.NoError(t, err)
	_, err = as.RoleGrantPermission(&pb.AuthRoleGrantPermissionRequest{Name: "rr",
		Perm: &authpb.Permission{Key: []byte("a"), RangeEnd: []byte{}, PermType: authpb.READ}})
	require.NoError(t, err)
	perms := revGetPerms(t, as)
	t.Logf("perms: %v", perms)
	require.Len(t, perms, 1)
	require.ErrorIs(t, as.isOpPermitted("foo", as.Revision(), []byte("a"), nil, authpb.WRITE), ErrPermissionDenied)
}

// Two spellings of one range: [a] (nil range end) and [a, "a\x00").
// The downgrade through the other spelling is a new entry; WRITE stays.
func TestReviewerGrantSemanticDuplicate(t *testing.T) {
	as, tearDown := setupAuthStore(t)
	defer tearDown(t)
	revSetupRole(t, as)
	_, err := as.RoleGrantPermission(&pb.AuthRoleGrantPermissionRequest{Name: "rr",
		Perm: &authpb.Permission{Key: []byte("a"), RangeEnd: nil, PermType: authpb.WRITE}})
	require.NoError(t, err)
	_, err = as.RoleGrantPermission(&pb.AuthRoleGrantPermissionRequest{Name: "rr",
		Perm: &authpb.Permission{Key: []byte("a"), RangeEnd: []byte("a\x00"), PermType: authpb.READ}})
	require.NoError(t, err)
	t.Logf("perms: %v", revGetPerms(t, as))
	t.Logf("write on a after 'downgrade': %v", as.isOpPermitted("foo", as.Revision(), []byte("a"), nil, authpb.WRITE))
}

// A role stored unsorted by key (no etcd writer does this): the search lands
// past the match, the scan misses it, and a duplicate is appended.
func TestReviewerGrantUnsortedStored(t *testing.T) {
	as, tearDown := setupAuthStore(t)
	defer tearDown(t)
	revSetupRole(t, as)
	tx := as.be.BatchTx()
	tx.Lock()
	tx.UnsafePutRole(&authpb.Role{Name: []byte("rr"), KeyPermission: []*authpb.Permission{
		{Key: []byte("b"), PermType: authpb.READ},
		{Key: []byte("a"), RangeEnd: []byte("c"), PermType: authpb.WRITE},
	}})
	as.commitRevision(tx)
	as.refreshRangePermCache(tx)
	tx.Unlock()
	_, err := as.RoleGrantPermission(&pb.AuthRoleGrantPermissionRequest{Name: "rr",
		Perm: &authpb.Permission{Key: []byte("a"), RangeEnd: []byte("c"), PermType: authpb.READ}})
	require.NoError(t, err)
	t.Logf("perms: %v", revGetPerms(t, as))
	t.Logf("write on a after downgrade: %v", as.isOpPermitted("foo", as.Revision(), []byte("a"), nil, authpb.WRITE))
}
