/-
**The client port's access-control table** (auth-mediation M1, 2026-11-20;
`notes/auth-mediation-scope.md` §2.2, (b-table)): one row per gRPC method registered on etcd's client
port, with its access class, its verification status and the specs that carry its check, as the
Lean form of `etc/auth-table.txt` (whose gRPC rows `etc/auth-mediation-check.py` checks it against:
the same names, classes, statuses and specs). `client_port_mediated` (`v3rpc/Results.lean`) states
that every registration of `v3rpc.Server` has a row and that every row's specs hold.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Server
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__AuthDisable
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__AuthEnable
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Authenticate
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Compact
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__DeleteRange
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__LeaseGrant
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__LeaseLeases
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__LeaseRenew
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__LeaseRevoke
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__LeaseTimeToLive
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__MemberList
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Put
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Range
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__RemoveMember
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__RoleAdd
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__RoleDelete
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__RoleGet
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__RoleGrantPermission
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__RoleList
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__RoleRevokePermission
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Txn
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__UserAdd
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__UserDelete
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__UserGet
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__UserGrantRole
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__UserList
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__UserRevokeRole
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__checkLeaseLeases
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__checkLeaseRenew
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__checkLeaseTimeToLive
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__checkMembershipOperationPermission
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__doSerialize
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__requireAuthInfo
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthAdmin__isPermitted
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer__AuthDisable
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer__AuthEnable
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer__AuthStatus
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer__Authenticate
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer__RoleAdd
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer__RoleDelete
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer__RoleGet
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer__RoleGrantPermission
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer__RoleList
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer__RoleRevokePermission
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer__UserAdd
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer__UserChangePassword
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer__UserDelete
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer__UserGet
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer__UserGrantRole
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer__UserList
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer__UserRevokeRole
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.LeaseServer__LeaseGrant
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.LeaseServer__LeaseKeepAlive
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.LeaseServer__LeaseLeases
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.LeaseServer__LeaseRevoke
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.LeaseServer__LeaseTimeToLive
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.LeaseServer__leaseKeepAlive
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.authMaintenanceServer__Alarm
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.authMaintenanceServer__Defragment
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.authMaintenanceServer__Downgrade
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.authMaintenanceServer__Hash
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.authMaintenanceServer__HashKV
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.authMaintenanceServer__MoveLeader
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.authMaintenanceServer__Snapshot
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.authMaintenanceServer__Status
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.authMaintenanceServer__isPermitted
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.authMaintenanceServer__requireAuthInfo
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer__Compact
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer__Range
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.serverWatchStream__isWatchPermitted
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.watchServer__Watch
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.CheckTxnAuth
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.authApplierV3__Apply
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.authApplierV3__DeleteRange
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.authApplierV3__LeaseRevoke
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.authApplierV3__Put
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.authApplierV3__RoleGet
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.authApplierV3__Txn
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.authApplierV3__UserGet
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.checkPutAuth

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.etcd.server.v3.etcdserver
  go_etcd_io.etcd.api.v3

/-- A row's access class (`notes/auth-matrix.md`): `pub` (public: no token), `authenticated` (a valid
token), `rbac` (the permission of the keys the request reads or writes), `admin` (the root role),
`mixed` (the class depends on the request's fields: the strongest is checked where it applies). -/
inductive v3rpc.PortClass where
  | pub | authenticated | rbac | admin | mixed
  deriving DecidableEq

/-- A row's verification status (`etc/auth-table.txt`'s header): `e2e` (the handler's proved spec
states the row's check for the request's principal, at the server's entry point), `e2eApply` (the
same, with the check stated at the apply layer), `contract` (the wrapper is proved, its effect an
inner operation taken as a contract that needs the guard's token), `server` (the server's entry
point is proved, the gRPC wrapper names-only), `guard` (only the guard is proved), `none` (nothing
past the request check), `pub` (public by design), `excluded` (not covered, by decision). -/
inductive v3rpc.PortStatus where
  | e2e | e2eApply | contract | server | guard | none | pub | excluded
  deriving DecidableEq

/-- The statuses that claim a proof. -/
def v3rpc.PortStatus.proved : v3rpc.PortStatus → Bool
  | .e2e | .e2eApply | .contract | .server | .guard | .pub => true
  | .none | .excluded => false

/-- **A row of the table**: the full name `key` (a prefix of full names when `isPrefix`: grpc's
health service, whose registrations are known by their prefix only), the class, the status, the
specs that carry the row's check (`True` when none) and why (for `none` and `excluded`, the decision
and where it is recorded). -/
structure v3rpc.PortRow where
  key : GoString
  isPrefix : Bool
  cls : v3rpc.PortClass
  status : v3rpc.PortStatus
  specs : Prop
  why : String

/-- The row covers the full name `n`. -/
def v3rpc.PortRow.covers (r : v3rpc.PortRow) (n : GoString) : Prop :=
  if r.isPrefix then r.key <+: n else r.key = n

section table
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]
variable [go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **The client port's table**: the gRPC rows of `etc/auth-table.txt`, in its order (the KV, Watch,
Lease, Cluster, Maintenance and Auth services `v3rpc.Server` registers, grpc's health service, then
the Lock and Election services `embed` registers, excluded by name: D3). -/
def v3rpc.clientPortTable : List v3rpc.PortRow :=
  [
    { key := go!"/etcdserverpb.KV/Range", isPrefix := false, cls := .rbac, status := .e2e,
      specs :=
          EtcdServer.doSerialize.spec (GF := GF) (hG := hG) ∧
          EtcdServer.Range.spec (GF := GF) (hG := hG) ∧
          v3rpc.kvServer.Range.spec (GF := GF) (hG := hG),
      why := "checked by doSerialize's chk after the read index (linearizable or not)" },
    { key := go!"/etcdserverpb.KV/RangeStream", isPrefix := false, cls := .rbac, status := .none,
      specs :=
          True,
      why := "stage M3: kvServer.RangeStream is translated, not proved; EtcdServer.RangeStream is names-only (notes/auth-mediation-scope.md §3.2); margin issues/etcd-rangestream-auth-revoked-midstream.md" },
    { key := go!"/etcdserverpb.KV/Put", isPrefix := false, cls := .rbac, status := .e2eApply,
      specs :=
          apply.checkPutAuth.spec (GF := GF) (hG := hG) ∧
          apply.authApplierV3.Put.spec (GF := GF) (hG := hG) ∧
          EtcdServer.Put.spec (GF := GF) (hG := hG),
      why := "checked at apply (checkPutAuth)" },
    { key := go!"/etcdserverpb.KV/DeleteRange", isPrefix := false, cls := .rbac, status := .e2eApply,
      specs :=
          apply.authApplierV3.DeleteRange.spec (GF := GF) (hG := hG) ∧
          EtcdServer.DeleteRange.spec (GF := GF) (hG := hG),
      why := "checked at apply" },
    { key := go!"/etcdserverpb.KV/Txn", isPrefix := false, cls := .rbac, status := .e2e,
      specs :=
          apply.CheckTxnAuth.spec (GF := GF) (hG := hG) ∧
          apply.authApplierV3.Txn.spec (GF := GF) (hG := hG) ∧
          EtcdServer.Txn.spec (GF := GF) (hG := hG),
      why := "read-only: chk at the server; writes: at apply" },
    { key := go!"/etcdserverpb.KV/Compact", isPrefix := false, cls := .admin, status := .contract,
      specs :=
          v3rpc.AuthAdmin.isPermitted.spec (GF := GF) (hG := hG) ∧
          v3rpc.kvServer.Compact.spec (GF := GF) (hG := hG) ∧
          EtcdServer.Compact.spec (GF := GF) (hG := hG),
      why := "checked when served: nonissues/etcd-compact-admin-check-lagging-member.md" },
    { key := go!"/etcdserverpb.Watch/Watch", isPrefix := false, cls := .rbac, status := .e2e,
      specs :=
          v3rpc.serverWatchStream.isWatchPermitted.spec (GF := GF) (hG := hG) ∧
          v3rpc.watchServer.Watch.spec (GF := GF) (hG := hG),
      why := "checked per created watcher (watchStreamSpec: each create's watchAuthed); live watchers are not re-checked (etcd's documented behaviour)" },
    { key := go!"/etcdserverpb.Lease/LeaseGrant", isPrefix := false, cls := .authenticated, status := .e2e,
      specs :=
          EtcdServer.requireAuthInfo.spec (GF := GF) (hG := hG) ∧
          EtcdServer.LeaseGrant.spec (GF := GF) (hG := hG) ∧
          v3rpc.LeaseServer.LeaseGrant.spec (GF := GF) (hG := hG),
      why := "" },
    { key := go!"/etcdserverpb.Lease/LeaseRevoke", isPrefix := false, cls := .mixed, status := .e2e,
      specs :=
          EtcdServer.requireAuthInfo.spec (GF := GF) (hG := hG) ∧
          apply.authApplierV3.LeaseRevoke.spec (GF := GF) (hG := hG) ∧
          EtcdServer.LeaseRevoke.spec (GF := GF) (hG := hG) ∧
          v3rpc.LeaseServer.LeaseRevoke.spec (GF := GF) (hG := hG),
      why := "the lease's keys checked at apply" },
    { key := go!"/etcdserverpb.Lease/LeaseTimeToLive", isPrefix := false, cls := .mixed, status := .e2e,
      specs :=
          EtcdServer.checkLeaseTimeToLive.spec (GF := GF) (hG := hG) ∧
          EtcdServer.LeaseTimeToLive.spec (GF := GF) (hG := hG) ∧
          v3rpc.LeaseServer.LeaseTimeToLive.spec (GF := GF) (hG := hG),
      why := "margin: issues/etcd-lease-timetolive-keys-toctou.md" },
    { key := go!"/etcdserverpb.Lease/LeaseLeases", isPrefix := false, cls := .mixed, status := .e2e,
      specs :=
          EtcdServer.checkLeaseLeases.spec (GF := GF) (hG := hG) ∧
          EtcdServer.LeaseLeases.spec (GF := GF) (hG := hG) ∧
          v3rpc.LeaseServer.LeaseLeases.spec (GF := GF) (hG := hG),
      why := "" },
    { key := go!"/etcdserverpb.Lease/LeaseKeepAlive", isPrefix := false, cls := .mixed, status := .e2e,
      specs :=
          EtcdServer.checkLeaseRenew.spec (GF := GF) (hG := hG) ∧
          EtcdServer.LeaseRenew.spec (GF := GF) (hG := hG) ∧
          v3rpc.LeaseServer.leaseKeepAlive.spec (GF := GF) (hG := hG) ∧
          v3rpc.LeaseServer.LeaseKeepAlive.spec (GF := GF) (hG := hG),
      why := "checked per renewal (each response's kaDn); margins: nonissues/etcd-lease-renew-keys-follower-lag.md, nonissues/etcd-lease-checks-lagging-member.md" },
    { key := go!"/etcdserverpb.Cluster/MemberAdd", isPrefix := false, cls := .admin, status := .guard,
      specs :=
          EtcdServer.checkMembershipOperationPermission.spec (GF := GF) (hG := hG),
      why := "stage M2: EtcdServer.AddMember and ClusterServer.MemberAdd are names-only" },
    { key := go!"/etcdserverpb.Cluster/MemberRemove", isPrefix := false, cls := .admin, status := .server,
      specs :=
          EtcdServer.checkMembershipOperationPermission.spec (GF := GF) (hG := hG) ∧
          EtcdServer.RemoveMember.spec (GF := GF) (hG := hG),
      why := "stage M2: the wrapper ClusterServer.MemberRemove is names-only" },
    { key := go!"/etcdserverpb.Cluster/MemberUpdate", isPrefix := false, cls := .admin, status := .guard,
      specs :=
          EtcdServer.checkMembershipOperationPermission.spec (GF := GF) (hG := hG),
      why := "stage M2: EtcdServer.UpdateMember and ClusterServer.MemberUpdate are names-only" },
    { key := go!"/etcdserverpb.Cluster/MemberList", isPrefix := false, cls := .authenticated, status := .server,
      specs :=
          EtcdServer.requireAuthInfo.spec (GF := GF) (hG := hG) ∧
          EtcdServer.MemberList.spec (GF := GF) (hG := hG),
      why := "stage M2: the wrapper ClusterServer.MemberList is names-only" },
    { key := go!"/etcdserverpb.Cluster/MemberPromote", isPrefix := false, cls := .admin, status := .guard,
      specs :=
          EtcdServer.checkMembershipOperationPermission.spec (GF := GF) (hG := hG),
      why := "stage M2: EtcdServer.PromoteMember and ClusterServer.MemberPromote are names-only" },
    { key := go!"/etcdserverpb.Maintenance/Defragment", isPrefix := false, cls := .admin, status := .contract,
      specs :=
          v3rpc.authMaintenanceServer.isPermitted.spec (GF := GF) (hG := hG) ∧
          v3rpc.authMaintenanceServer.Defragment.spec (GF := GF) (hG := hG),
      why := "" },
    { key := go!"/etcdserverpb.Maintenance/Snapshot", isPrefix := false, cls := .admin, status := .contract,
      specs :=
          v3rpc.authMaintenanceServer.isPermitted.spec (GF := GF) (hG := hG) ∧
          v3rpc.authMaintenanceServer.Snapshot.spec (GF := GF) (hG := hG),
      why := "" },
    { key := go!"/etcdserverpb.Maintenance/Hash", isPrefix := false, cls := .admin, status := .contract,
      specs :=
          v3rpc.authMaintenanceServer.isPermitted.spec (GF := GF) (hG := hG) ∧
          v3rpc.authMaintenanceServer.Hash.spec (GF := GF) (hG := hG),
      why := "" },
    { key := go!"/etcdserverpb.Maintenance/HashKV", isPrefix := false, cls := .admin, status := .contract,
      specs :=
          v3rpc.authMaintenanceServer.isPermitted.spec (GF := GF) (hG := hG) ∧
          v3rpc.authMaintenanceServer.HashKV.spec (GF := GF) (hG := hG),
      why := "" },
    { key := go!"/etcdserverpb.Maintenance/MoveLeader", isPrefix := false, cls := .admin, status := .contract,
      specs :=
          v3rpc.authMaintenanceServer.isPermitted.spec (GF := GF) (hG := hG) ∧
          v3rpc.authMaintenanceServer.MoveLeader.spec (GF := GF) (hG := hG),
      why := "" },
    { key := go!"/etcdserverpb.Maintenance/Downgrade", isPrefix := false, cls := .admin, status := .contract,
      specs :=
          v3rpc.authMaintenanceServer.isPermitted.spec (GF := GF) (hG := hG) ∧
          v3rpc.authMaintenanceServer.Downgrade.spec (GF := GF) (hG := hG),
      why := "" },
    { key := go!"/etcdserverpb.Maintenance/Alarm", isPrefix := false, cls := .mixed, status := .contract,
      specs :=
          v3rpc.authMaintenanceServer.isPermitted.spec (GF := GF) (hG := hG) ∧
          v3rpc.authMaintenanceServer.requireAuthInfo.spec (GF := GF) (hG := hG) ∧
          v3rpc.authMaintenanceServer.Alarm.spec (GF := GF) (hG := hG),
      why := "GET authenticated; ACTIVATE and DEACTIVATE admin" },
    { key := go!"/etcdserverpb.Maintenance/Status", isPrefix := false, cls := .authenticated, status := .contract,
      specs :=
          v3rpc.authMaintenanceServer.requireAuthInfo.spec (GF := GF) (hG := hG) ∧
          v3rpc.authMaintenanceServer.Status.spec (GF := GF) (hG := hG),
      why := "" },
    { key := go!"/etcdserverpb.Auth/Authenticate", isPrefix := false, cls := .pub, status := .pub,
      specs :=
          EtcdServer.Authenticate.spec (GF := GF) (hG := hG) ∧
          v3rpc.AuthServer.Authenticate.spec (GF := GF) (hG := hG),
      why := "releases a token for a correct password (the store's contract)" },
    { key := go!"/etcdserverpb.Auth/AuthStatus", isPrefix := false, cls := .pub, status := .pub,
      specs :=
          v3rpc.AuthServer.AuthStatus.spec (GF := GF) (hG := hG),
      why := "public on purpose (etcd-io/etcd#20802)" },
    { key := go!"/etcdserverpb.Auth/AuthEnable", isPrefix := false, cls := .admin, status := .e2eApply,
      specs :=
          apply.authApplierV3.Apply.spec (GF := GF) (hG := hG) ∧
          v3rpc.AuthServer.AuthEnable.spec (GF := GF) (hG := hG) ∧
          EtcdServer.AuthEnable.spec (GF := GF) (hG := hG),
      why := "checked at apply; refusal reason at the proposer: stage M4" },
    { key := go!"/etcdserverpb.Auth/AuthDisable", isPrefix := false, cls := .admin, status := .e2eApply,
      specs :=
          apply.authApplierV3.Apply.spec (GF := GF) (hG := hG) ∧
          v3rpc.AuthServer.AuthDisable.spec (GF := GF) (hG := hG) ∧
          EtcdServer.AuthDisable.spec (GF := GF) (hG := hG),
      why := "checked at apply; refusal reason at the proposer: stage M4" },
    { key := go!"/etcdserverpb.Auth/UserAdd", isPrefix := false, cls := .admin, status := .e2eApply,
      specs :=
          apply.authApplierV3.Apply.spec (GF := GF) (hG := hG) ∧
          v3rpc.AuthServer.UserAdd.spec (GF := GF) (hG := hG) ∧
          EtcdServer.UserAdd.spec (GF := GF) (hG := hG),
      why := "checked at apply; refusal reason at the proposer: stage M4" },
    { key := go!"/etcdserverpb.Auth/UserDelete", isPrefix := false, cls := .admin, status := .e2eApply,
      specs :=
          apply.authApplierV3.Apply.spec (GF := GF) (hG := hG) ∧
          v3rpc.AuthServer.UserDelete.spec (GF := GF) (hG := hG) ∧
          EtcdServer.UserDelete.spec (GF := GF) (hG := hG),
      why := "checked at apply; refusal reason at the proposer: stage M4" },
    { key := go!"/etcdserverpb.Auth/UserChangePassword", isPrefix := false, cls := .admin, status := .e2eApply,
      specs :=
          apply.authApplierV3.Apply.spec (GF := GF) (hG := hG) ∧
          v3rpc.AuthServer.UserChangePassword.spec (GF := GF) (hG := hG),
      why := "checked at apply; EtcdServer.UserChangePassword is names-only (its wrapper is proved over the inner contract)" },
    { key := go!"/etcdserverpb.Auth/UserGrantRole", isPrefix := false, cls := .admin, status := .e2eApply,
      specs :=
          apply.authApplierV3.Apply.spec (GF := GF) (hG := hG) ∧
          v3rpc.AuthServer.UserGrantRole.spec (GF := GF) (hG := hG) ∧
          EtcdServer.UserGrantRole.spec (GF := GF) (hG := hG),
      why := "checked at apply; refusal reason at the proposer: stage M4" },
    { key := go!"/etcdserverpb.Auth/UserRevokeRole", isPrefix := false, cls := .admin, status := .e2eApply,
      specs :=
          apply.authApplierV3.Apply.spec (GF := GF) (hG := hG) ∧
          v3rpc.AuthServer.UserRevokeRole.spec (GF := GF) (hG := hG) ∧
          EtcdServer.UserRevokeRole.spec (GF := GF) (hG := hG),
      why := "checked at apply; refusal reason at the proposer: stage M4" },
    { key := go!"/etcdserverpb.Auth/UserList", isPrefix := false, cls := .admin, status := .e2eApply,
      specs :=
          apply.authApplierV3.Apply.spec (GF := GF) (hG := hG) ∧
          v3rpc.AuthServer.UserList.spec (GF := GF) (hG := hG) ∧
          EtcdServer.UserList.spec (GF := GF) (hG := hG),
      why := "checked at apply; refusal reason at the proposer: stage M4" },
    { key := go!"/etcdserverpb.Auth/RoleAdd", isPrefix := false, cls := .admin, status := .e2eApply,
      specs :=
          apply.authApplierV3.Apply.spec (GF := GF) (hG := hG) ∧
          v3rpc.AuthServer.RoleAdd.spec (GF := GF) (hG := hG) ∧
          EtcdServer.RoleAdd.spec (GF := GF) (hG := hG),
      why := "checked at apply; refusal reason at the proposer: stage M4" },
    { key := go!"/etcdserverpb.Auth/RoleDelete", isPrefix := false, cls := .admin, status := .e2eApply,
      specs :=
          apply.authApplierV3.Apply.spec (GF := GF) (hG := hG) ∧
          v3rpc.AuthServer.RoleDelete.spec (GF := GF) (hG := hG) ∧
          EtcdServer.RoleDelete.spec (GF := GF) (hG := hG),
      why := "checked at apply; refusal reason at the proposer: stage M4" },
    { key := go!"/etcdserverpb.Auth/RoleGrantPermission", isPrefix := false, cls := .admin, status := .e2eApply,
      specs :=
          apply.authApplierV3.Apply.spec (GF := GF) (hG := hG) ∧
          v3rpc.AuthServer.RoleGrantPermission.spec (GF := GF) (hG := hG) ∧
          EtcdServer.RoleGrantPermission.spec (GF := GF) (hG := hG),
      why := "checked at apply; refusal reason at the proposer: stage M4" },
    { key := go!"/etcdserverpb.Auth/RoleRevokePermission", isPrefix := false, cls := .admin, status := .e2eApply,
      specs :=
          apply.authApplierV3.Apply.spec (GF := GF) (hG := hG) ∧
          v3rpc.AuthServer.RoleRevokePermission.spec (GF := GF) (hG := hG) ∧
          EtcdServer.RoleRevokePermission.spec (GF := GF) (hG := hG),
      why := "checked at apply; refusal reason at the proposer: stage M4" },
    { key := go!"/etcdserverpb.Auth/RoleList", isPrefix := false, cls := .admin, status := .e2eApply,
      specs :=
          apply.authApplierV3.Apply.spec (GF := GF) (hG := hG) ∧
          v3rpc.AuthServer.RoleList.spec (GF := GF) (hG := hG) ∧
          EtcdServer.RoleList.spec (GF := GF) (hG := hG),
      why := "checked at apply; refusal reason at the proposer: stage M4" },
    { key := go!"/etcdserverpb.Auth/UserGet", isPrefix := false, cls := .mixed, status := .e2eApply,
      specs :=
          apply.authApplierV3.UserGet.spec (GF := GF) (hG := hG) ∧
          v3rpc.AuthServer.UserGet.spec (GF := GF) (hG := hG) ∧
          EtcdServer.UserGet.spec (GF := GF) (hG := hG),
      why := "admin or the user itself, checked at apply" },
    { key := go!"/etcdserverpb.Auth/RoleGet", isPrefix := false, cls := .mixed, status := .e2eApply,
      specs :=
          apply.authApplierV3.RoleGet.spec (GF := GF) (hG := hG) ∧
          v3rpc.AuthServer.RoleGet.spec (GF := GF) (hG := hG) ∧
          EtcdServer.RoleGet.spec (GF := GF) (hG := hG),
      why := "admin or a role the user has, checked at apply" },
    { key := go!"/grpc.health.v1.Health/", isPrefix := true, cls := .pub, status := .pub,
      specs :=
          True,
      why := "grpc's health service, every method: the serving status only, no data (notes/auth-mediation-scope.md §1)" },
    { key := go!"/v3lockpb.Lock/Lock", isPrefix := false, cls := .mixed, status := .excluded,
      specs :=
          True,
      why := "D3: a waiting Lock's watch is checked as another user, etcd-io/etcd#17502 (issues/etcd-v3election-shared-watch-wrong-user.md, issues/etcd-v3lock-watch-shared-stream-principal.md)" },
    { key := go!"/v3lockpb.Lock/Unlock", isPrefix := false, cls := .rbac, status := .excluded,
      specs :=
          True,
      why := "D3: excluded with its service; runs through the untranslated in-process client (notes/auth-mediation-scope.md §3.1)" },
    { key := go!"/v3electionpb.Election/Campaign", isPrefix := false, cls := .mixed, status := .excluded,
      specs :=
          True,
      why := "D3: a waiting Campaign's watch is checked as another user, etcd-io/etcd#17502 (issues/etcd-v3election-shared-watch-wrong-user.md)" },
    { key := go!"/v3electionpb.Election/Proclaim", isPrefix := false, cls := .rbac, status := .excluded,
      specs :=
          True,
      why := "D3: excluded with its service; runs through the untranslated in-process client (notes/auth-mediation-scope.md §3.1)" },
    { key := go!"/v3electionpb.Election/Leader", isPrefix := false, cls := .rbac, status := .excluded,
      specs :=
          True,
      why := "D3: excluded with its service; runs through the untranslated in-process client (notes/auth-mediation-scope.md §3.1)" },
    { key := go!"/v3electionpb.Election/Observe", isPrefix := false, cls := .rbac, status := .excluded,
      specs :=
          True,
      why := "D3: its watch is checked as another user, etcd-io/etcd#17502 (issues/etcd-v3election-shared-watch-wrong-user.md)" },
    { key := go!"/v3electionpb.Election/Resign", isPrefix := false, cls := .rbac, status := .excluded,
      specs :=
          True,
      why := "D3: excluded with its service; runs through the untranslated in-process client (notes/auth-mediation-scope.md §3.1)" }]

end table

end EtcdGrove
end Perennial
