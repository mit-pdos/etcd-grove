// Requirement snippets for server/storage/schema, etcd's buckets and records (batch 4b).
// Each is stated over a backend transaction; the backend (4a) supplies the transaction contracts
// (Schema.txRd, txWr, txRange) for the part of it the caller owns.
package schema

import (
	"github.com/Masterminds/semver/v3"
	"go.uber.org/zap"

	"go.etcd.io/etcd/api/v3/authpb"
	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/client/pkg/v3/types"
	"go.etcd.io/etcd/server/v3/etcdserver/api/membership"
	"go.etcd.io/etcd/server/v3/etcdserver/version"
	"go.etcd.io/etcd/server/v3/lease/leasepb"
	"go.etcd.io/etcd/server/v3/storage/backend"
	eschema "go.etcd.io/etcd/server/v3/storage/schema"
)

// REQ schema/create-buckets: the store, the lessor and bootstrap create their buckets (creating an
// existing one changes nothing).
// Users: storage/mvcc/kvstore.go:121-123 (UnsafeCreateMetaBucket under the store's lock),
// bootstrap.go:266 (CreateMetaBucket), lease/lessor.go:812 (UnsafeCreateLeaseBucket).
// Assumes: tx is be's batch transaction, which this goroutine has locked (txWr of the caller's
// part, its scope holding Meta and Lease whole).
// Specs: Schema.UnsafeCreateMetaBucket.spec, CreateMetaBucket.spec, UnsafeCreateLeaseBucket.spec;
// laws bucketVars_init.
func ReqCreateBuckets(be backend.Backend) {
	eschema.CreateMetaBucket(be.BatchTx())
	tx := be.BatchTx()
	tx.LockOutsideApply()
	eschema.UnsafeCreateMetaBucket(tx)
	eschema.UnsafeCreateLeaseBucket(tx)
	tx.Unlock()
}

// REQ schema/save-then-read: the consistent index saved in a batch is the one read back, from the
// batch and (after the batch's unlock) from a read transaction; a smaller index is never saved
// (with ETCD_VERIFY on, the check holds).
// Users: etcdserver/cindex/cindex.go:97,107,120 (ReadConsistentIndex, UnsafeReadConsistentIndex,
// UnsafeUpdateConsistentIndex in the pre-commit hook), storage/hooks.go:50 (the conf state).
// Assumes: tx is locked by this goroutine (the pre-commit hook); i is at least the stored index;
// Meta exists; no other writer of Meta's consistent index (the indexer is its only writer).
// Specs: UnsafeUpdateConsistentIndex.spec, UnsafeReadConsistentIndex.spec,
// ReadConsistentIndex.spec; ciOf (ciPut ...) = (i, t) for i, t ≠ 0.
func ReqSaveThenRead(be backend.Backend, i, t uint64) {
	tx := be.BatchTx()
	tx.LockOutsideApply()
	eschema.UnsafeUpdateConsistentIndex(tx, i, t)
	if v, w := eschema.UnsafeReadConsistentIndex(tx); i != 0 && t != 0 && (v != i || w != t) {
		panic("save-then-read: index lost in the batch")
	}
	tx.Unlock()
	if v, _ := eschema.ReadConsistentIndex(be.ReadTx()); i != 0 && v != i {
		panic("save-then-read: index not visible after unlock")
	}
}

// REQ schema/lease-recover: the lease records written are the ones read back, each once.
// Users: lease/lease.go:57-60 (persistTo: MustUnsafePutLease), lease/lessor.go:809-814
// (initAndRecover: UnsafeCreateLeaseBucket, MustUnsafeGetAllLeases), lessor.go:359 (Revoke:
// UnsafeDeleteLease).
// Assumes: the caller owns the Lease bucket (the lessor), holds the batch lock between Lock and
// Unlock; id1 != id2.
// Specs: MustUnsafePutLease.spec, UnsafeDeleteLease.spec, MustUnsafeGetAllLeases.spec;
// leaseBktIs.
func ReqLeaseRecover(be backend.Backend, id1, id2, ttl int64) {
	tx := be.BatchTx()
	tx.LockInsideApply()
	eschema.UnsafeCreateLeaseBucket(tx)
	eschema.MustUnsafePutLease(tx, &leasepb.Lease{ID: id1, TTL: ttl})
	eschema.MustUnsafePutLease(tx, &leasepb.Lease{ID: id2, TTL: ttl})
	eschema.UnsafeDeleteLease(tx, &leasepb.Lease{ID: id2})
	lpbs := eschema.MustUnsafeGetAllLeases(tx)
	tx.Unlock()
	n := 0
	for _, lpb := range lpbs {
		if lpb.ID == id2 {
			panic("lease-recover: deleted lease read back")
		}
		if lpb.ID == id1 {
			if lpb.TTL != ttl {
				panic("lease-recover: wrong TTL")
			}
			n++
		}
	}
	if n != 1 {
		panic("lease-recover: written lease not read back exactly once")
	}
}

// REQ schema/auth-write-read: the auth store's writes (enabled flag, revision, a user, a role)
// are read back from the batch, and from a read transaction after Unlock (which commits).
// Users: auth/store.go (AuthEnable, UserAdd, RoleAdd, commitRevision under tx.Lock(); the checks'
// reads through ReadTx; GetUser, GetAllRoles), auth/store.go:972 (CreateAuthBuckets).
// Assumes: the caller is the auth buckets' only writer; the user and role are made here (read-only
// afterwards); their names are non-empty and the role's name below 0xff.
// Specs: NewAuthBackend.spec, authBackend.{CreateAuthBuckets,BatchTx,ReadTx,GetUser,GetAllRoles}.spec,
// authBatchTx.{Lock,UnsafeSaveAuthEnabled,UnsafeSaveAuthRevision,UnsafePutUser,UnsafePutRole,
// UnsafeReadAuthEnabled,UnsafeReadAuthRevision,UnsafeGetUser,Unlock}.spec,
// authReadTx.{RLock,UnsafeReadAuthRevision,RUnlock}.spec.
func ReqAuthWriteRead(lg *zap.Logger, be backend.Backend, rev uint64) {
	abe := eschema.NewAuthBackend(lg, be)
	abe.CreateAuthBuckets()
	tx := abe.BatchTx()
	tx.Lock()
	tx.UnsafeSaveAuthEnabled(true)
	tx.UnsafeSaveAuthRevision(rev)
	tx.UnsafePutUser(&authpb.User{Name: []byte("alice")})
	tx.UnsafePutRole(&authpb.Role{Name: []byte("reader")})
	if !tx.UnsafeReadAuthEnabled() || tx.UnsafeReadAuthRevision() != rev {
		panic("auth-write-read: flags lost in the batch")
	}
	if u := tx.UnsafeGetUser("alice"); u == nil || string(u.Name) != "alice" {
		panic("auth-write-read: user lost in the batch")
	}
	tx.Unlock()
	rtx := abe.ReadTx()
	rtx.RLock()
	r := rtx.UnsafeReadAuthRevision()
	rtx.RUnlock()
	if r != rev {
		panic("auth-write-read: revision not visible after unlock")
	}
	if abe.GetUser("alice") == nil {
		panic("auth-write-read: user not visible after unlock")
	}
	found := false
	for _, r := range abe.GetAllRoles() {
		if string(r.Name) == "reader" {
			found = true
		}
	}
	if !found {
		panic("auth-write-read: role not listed")
	}
}

// REQ schema/alarm-put-get: an alarm put is listed; a deleted one is not.
// Users: etcdserver/api/v3alarm/alarms.go (NewAlarmStore: CreateAlarmBucket, GetAllAlarms;
// Activate: MustPutAlarm; Deactivate: MustDeleteAlarm), server.go:2425, 1118.
// Assumes: the caller owns the Alarm bucket (the alarm store); a member id and type.
// Specs: NewAlarmBackend.spec, alarmBackend.{CreateAlarmBucket,MustPutAlarm,MustDeleteAlarm,
// GetAllAlarms}.spec (alarmBkt).
func ReqAlarmPutGet(lg *zap.Logger, be backend.Backend, id uint64) {
	ab := eschema.NewAlarmBackend(lg, be)
	ab.CreateAlarmBucket()
	a := &pb.AlarmMember{MemberID: id, Alarm: pb.AlarmType_NOSPACE}
	ab.MustPutAlarm(a)
	has := func() bool {
		ms, err := ab.GetAllAlarms()
		if err != nil {
			panic("alarm-put-get: alarms not decoded")
		}
		for _, m := range ms {
			if m.MemberID == id && m.Alarm == pb.AlarmType_NOSPACE {
				return true
			}
		}
		return false
	}
	if !has() {
		panic("alarm-put-get: alarm not listed")
	}
	ab.MustDeleteAlarm(a)
	if has() {
		panic("alarm-put-get: deleted alarm listed")
	}
}

// REQ schema/members-save-read: a member saved is read back; a member deleted is recorded as
// removed.
// Users: membership/cluster.go (AddMember, RemoveMember with shouldApplyV3; Recover and
// ValidateConfigurationChange read the backend), bootstrap.go:133.
// Assumes: the caller owns the member buckets (the cluster); m's id is not id2.
// Specs: NewMembershipBackend.spec, membershipBackend.{MustSaveMemberToBackend,
// MustDeleteMemberFromBackend,MustReadMembersFromBackend}.spec (memberBkts).
func ReqMembersSaveRead(lg *zap.Logger, be backend.Backend, m *membership.Member, id2 types.ID) {
	mb := eschema.NewMembershipBackend(lg, be)
	mb.MustSaveMemberToBackend(m)
	mb.MustDeleteMemberFromBackend(id2)
	members, removed := mb.MustReadMembersFromBackend()
	if members[m.ID] == nil || !removed[id2] || members[id2] != nil {
		panic("members-save-read: members not as written")
	}
}

// REQ schema/list-users-readtx: the users listed through a read transaction are each stored user
// once (in some order: bolt's entries then the read buffer's).
// Users: auth/store.go:602 (UserList: GetAllUsers), auth/store.go (RoleDelete's scan).
// Assumes: the caller owns the auth buckets (no concurrent writer); "alice" was stored.
// Specs: authBackend.GetAllUsers.spec (entsAny), authReadTx.UnsafeGetAllUsers.spec.
func ReqListUsersReadTx(lg *zap.Logger, be backend.Backend) {
	abe := eschema.NewAuthBackend(lg, be)
	n := 0
	for _, u := range abe.GetAllUsers() {
		if string(u.Name) == "alice" {
			n++
		}
	}
	if n != 1 {
		panic("list-users-readtx: stored user not listed exactly once")
	}
}

// REQ schema/delete-user-role: a deleted user or role is gone from the batch.
// Users: auth/store.go (UserDelete: UnsafeDeleteUser; RoleDelete: UnsafeDeleteRole).
// Assumes: the caller owns the auth buckets.
// Specs: authBatchTx.{Lock,UnsafeDeleteUser,UnsafeDeleteRole,UnsafeGetUser,UnsafeGetRole,Unlock}.spec.
func ReqDeleteUserRole(lg *zap.Logger, be backend.Backend, user, role string) {
	tx := eschema.NewAuthBackend(lg, be).BatchTx()
	tx.Lock()
	tx.UnsafeDeleteUser(user)
	tx.UnsafeDeleteRole(role)
	if tx.UnsafeGetUser(user) != nil || tx.UnsafeGetRole(role) != nil {
		panic("delete-user-role: deleted record read back")
	}
	tx.Unlock()
}

// REQ schema/ci-read-under-batch-lock: the post-lock hook reads the stored consistent index through
// the shared read transaction without RLock, the batch lock held.
// Users: etcdserver/cindex/cindex.go:107 (UnsafeConsistentIndex, from the post-lock hook,
// server.go:2478-2484).
// Assumes: this goroutine holds be's batch lock (the hook runs under it); Meta exists.
// Specs: UnsafeReadConsistentIndex.spec (txRd of the shared ReadTx under the batch lock: 4a's).
func ReqCIReadUnderBatchLock(be backend.Backend) uint64 {
	tx := be.BatchTx()
	tx.LockInsideApply()
	v, _ := eschema.UnsafeReadConsistentIndex(be.ReadTx())
	tx.Unlock()
	return v
}

// REQ schema/lease-delete-under-txn: the lessor deletes its record while another component (mvcc's
// write transaction) holds the batch lock.
// Users: lease/lessor.go:340-360 (Revoke: UnsafeDeleteLease inside the range deleter's txn).
// Assumes: the lock's holder lends "held" to the lease part's owner (4a); the lessor owns Lease.
// Specs: UnsafeDeleteLease.spec, MustUnsafeGetAllLeases.spec.
func ReqLeaseDeleteUnderTxn(be backend.Backend, id int64) {
	tx := be.BatchTx()
	tx.LockInsideApply() // mvcc's Write()
	eschema.UnsafeDeleteLease(be.BatchTx(), &leasepb.Lease{ID: id})
	for _, l := range eschema.MustUnsafeGetAllLeases(tx) {
		if l.ID == id {
			panic("lease-delete-under-txn: deleted lease read back")
		}
	}
	tx.Unlock() // mvcc's End()
}

// REQ schema/cluster-version-save-read: the cluster version and downgrade info saved are read back.
// Users: membership/cluster.go:610-614 (SetVersion), :814 (SetDowngradeInfo), :249-259 (Recover).
// Assumes: the caller owns the membership buckets; v is a major.minor.0 version (it parses back).
// Specs: membershipBackend.{MustCreateBackendBuckets,MustSaveClusterVersionToBackend,
// MustSaveDowngradeToBackend,ClusterVersionFromBackend,DowngradeInfoFromBackend}.spec;
// Semver.Version.LessThan.spec, laws parse_plain, preLtb_irrefl.
func ReqClusterVersionSaveRead(lg *zap.Logger, be backend.Backend, v *semver.Version) {
	mb := eschema.NewMembershipBackend(lg, be)
	mb.MustCreateBackendBuckets()
	mb.MustSaveClusterVersionToBackend(v)
	mb.MustSaveDowngradeToBackend(&version.DowngradeInfo{Enabled: false})
	if w := mb.ClusterVersionFromBackend(); w == nil || w.LessThan(v) || v.LessThan(w) {
		panic("cluster-version-save-read: version lost")
	}
	if d := mb.DowngradeInfoFromBackend(); d == nil || d.Enabled {
		panic("cluster-version-save-read: downgrade info lost")
	}
}
