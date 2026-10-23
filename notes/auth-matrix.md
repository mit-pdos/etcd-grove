# The auth matrix: every gRPC method on the client port and the privilege it requires

Re-derived from the handlers at the etcd pin (`.lake/go-src/etcd`, `upamanyus/etcd` `188113160`,
upstream main of 2026-10 plus the fork's fixes) for the auth plan's track A
(`notes/auth-plan.md`, D-AU4), not copied from etcd-io/etcd#22541 (whose counts it reproduces:
49 methods; public 2, authenticated 6, RBAC 32, admin 27, counting a method under the strongest
class it needs for some request shape). The classes:

- **public**: served with no token (`Authenticate`, `AuthStatus`);
- **authenticated**: with auth enabled, a valid token (`requireAuthInfo`: `AuthInfoFromCtx`
  returns a non-nil `AuthInfo`), no permission looked at;
- **RBAC**: `auth.permitted` of the keys the request reads or writes (D-AU1), at the API layer
  (`doSerialize`'s `chk`, the watch's `isWatchPermitted`, the lease checks) and, for the writes that
  go through raft, at apply (`authApplierV3`, `checkPutAuth`, `checkTxnReqsPermission`);
- **admin**: `IsAdminPermitted` (the root role), at the API layer (`AuthAdmin.isPermitted`,
  `checkMembershipOperationPermission`) or at apply (`needAdminPermission`, the auth requests).

Where a method's class depends on the request's fields, both are listed. "Keys" are what
`auth.permitted` must cover; the request-shape probes of #22541 are the rows' second column.

| service / method | class and keys | where the check is |
|---|---|---|
| **KV** `Range` | RBAC read `[Key, RangeEnd)` (open-ended `"\x00"` is to the end of the key space) | serializable: `doSerialize`'s `chk` (`v3_server.go`); linearizable: apply, `authApplierV3.Range` |
| `RangeStream` | as `Range` | as `Range` (`v3_server.go`, the stream variant) |
| `Put` | RBAC write `Key`; with `PrevKv`, also read `Key`; with a lease, also write every key the lease holds (`checkLeasePuts`) | apply, `authApplierV3.Put` → `checkPutAuth` |
| `DeleteRange` | RBAC write `[Key, RangeEnd)`; with `PrevKv`, also read it | apply, `authApplierV3.DeleteRange` |
| `Txn` | RBAC: read each compare's `[Key, RangeEnd)`; each op of **both** branches as the op's own row, nested `Txn`s recursively (`checkTxnReqsPermission`) | apply, `authApplierV3.Txn` → `checkTxnAuth` (and the pre-check of a serializable read-only `Txn` through `chk`) |
| `Compact` | admin | API, `kvServer.Compact` → `AuthAdmin.isPermitted` |
| **Watch** `Watch` (each `WatchCreateRequest`) | RBAC read `[Key, RangeEnd)` (`WithFromKey`: `RangeEnd = "\x00"`, to the end) | API, `serverWatchStream.isWatchPermitted` |
| **Lease** `LeaseGrant` | authenticated | API, `EtcdServer.LeaseGrant` → `requireAuthInfo` |
| `LeaseRevoke` | authenticated; RBAC write every key the lease holds | API `requireAuthInfo`; apply, `authApplierV3.LeaseRevoke` → `checkLeasePuts` |
| `LeaseTimeToLive` | authenticated; admin, or RBAC read every key the lease holds (`WithKeys` returns them) | API, `checkLeaseTimeToLive` |
| `LeaseLeases` | authenticated; admin, or RBAC read every key of every lease | API, `checkLeaseLeases` |
| `LeaseKeepAlive` (stream) | authenticated; admin, or RBAC write every key the lease holds, per renewal | API, `checkLeaseRenew` |
| **Cluster** `MemberAdd`, `MemberRemove`, `MemberUpdate`, `MemberPromote` | admin | API, `checkMembershipOperationPermission` (`server.go`: the check at the API layer, the effect at apply, the TOCTOU its comment names) |
| `MemberList` | authenticated | API, `EtcdServer.MemberList` → `requireAuthInfo` |
| **Maintenance** `Defragment`, `Snapshot`, `Hash`, `HashKV`, `MoveLeader`, `Downgrade` | admin | API, `authMaintenanceServer` → `AuthAdmin.isPermitted` |
| `Alarm` | `GET`: authenticated; `ACTIVATE`/`DEACTIVATE`: admin | API, `authMaintenanceServer.Alarm` |
| `Status` | authenticated | API, `authMaintenanceServer.Status` → `requireAuthInfo` |
| **Auth** `Authenticate` | public | — |
| `AuthStatus` | public (made so on purpose, etcd-io/etcd#20802) | — |
| `AuthEnable`, `AuthDisable` | admin | apply, `authApplierV3.Apply` (`needAdminPermission`) |
| `UserAdd`, `UserDelete`, `UserChangePassword`, `UserGrantRole`, `UserRevokeRole`, `UserList` | admin | apply, `needAdminPermission` |
| `RoleAdd`, `RoleDelete`, `RoleGrantPermission`, `RoleRevokePermission`, `RoleList` | admin | apply, `needAdminPermission` |
| `UserGet` | admin, or the user itself (`r.Name == authInfo.Username`) | apply, `authApplierV3.UserGet` |
| `RoleGet` | admin, or a role the user has (`HasRole`) | apply, `authApplierV3.RoleGet` |
| **Lock** `Lock` | the class of the calls it makes with the caller's context: `LeaseGrant` (authenticated), then the `concurrency.Mutex`'s `Txn`/`Put`/`Get`/`Watch` on the lock's prefix (RBAC write and read of `<name>/<lease>` and the prefix) | `v3lock/lock.go` through the embedded client |
| `Unlock` | RBAC write `Key` (`Delete`) | `v3lock/lock.go` |
| **Election** `Campaign` | as `Lock`: `LeaseGrant`, then `Txn`/`Put`/`Get`/`Watch` on the election's prefix | `v3election/election.go` |
| `Proclaim` | RBAC write the leader key (`Txn` with `Put`) and read it | `v3election/election.go` |
| `Leader` | RBAC read the prefix | `v3election/election.go` |
| `Observe` (stream) | RBAC read the prefix (`Get`, `Watch`) | `v3election/election.go` |
| `Resign` | RBAC write the leader key (`Txn` with `Delete`) | `v3election/election.go` |

Counting: KV 6, Watch 1, Lease 5, Cluster 5, Maintenance 8, Auth 17, Lock 2, Election 5: 49.
Public 2 (`Authenticate`, `AuthStatus`); authenticated-only 6 (`LeaseGrant`, `MemberList`,
`Status`, `Alarm` GET counted with `Alarm`'s admin, and the lease methods whose RBAC part is
"admin or keys": #22541 counts `LeaseTimeToLive`, `LeaseLeases`, `LeaseKeepAlive` with
`LeaseRevoke` as RBAC); the rest RBAC or admin as above.

What the plan's track A proves per row: the handler performs its effect (the apply step, the
read's reply, the watch's registration, the lease's change) only if the row's oracle allows the
principal, and with auth disabled always (`notes/auth-plan.md`, A1-A4). What the verified code
covers today (A0): the KV rows, `Watch`, `Compact`'s admin check (the `v3rpc` KV service is
proved; the auth checks are proved for memory safety in the mode `off`), `LeaseRevoke`'s apply
part; the other services' handlers are names-only.

## What is proved of the table (A1, 2026-10-23)

`Proof/go_etcd_io/etcd/server/v3/etcdserver/apply/AuthClass.lean` states the "keys" column as a
class per request shape (`putClass`, `deleteClass`, `rangeClass`, `txnClass`), and the checks'
specs say a passed check establishes it of the principal it checked (`notes/decisions.md`, "A1 of
the auth plan"):

- `Put`: `checkPutAuth` (the key's write, with `PrevKv` its read; the lease's keys are checked but
  not stated: the lessor has no key model);
- `Txn`: `checkTxnReqsPermission` (each op of both branches, nested transactions recursively),
  `checkTxnPermission`/`CheckTxnAuth` (the comparisons' reads, then both branches);
- `Range`, serializable: `doSerialize`'s `chk`, and `EtcdServer.Range`'s success post gives the
  class of some auth info (the token's principal, or the empty one);
- `Watch`: `serverWatchStream.isWatchPermitted` (the read of `[Key, RangeEnd)`).

Not yet: the method-level statement for the principal the request's header names
(`authApplierV3.Put`/`DeleteRange`/`Txn`/`Range`: the principal is hidden in the chain model's
auth case), `RangeStream`, the lease rows, and everything outside the KV and watch services (A2,
A3).

## What is proved of the table (A2, 2026-10-23)

The API layer's two guards and the entry points they guard (`notes/decisions.md`, "A2 of the auth
plan"; `Proof/go_etcd_io/etcd/server/v3/etcdserver/AuthGuard.lean`, `v3rpc/InvAuthAdmin.lean`):
a passing guard's token (`adminRes`: the admin check passed for the request's auth info, in the
mode `on γa` a recorded state at which it is admin; `authedRes`: auth disabled at a recorded
state, or the request carried an auth info), and the entry point's inner operation (names only)
as a contract whose precondition carries the token, so the operation runs only after a passing
check, and with auth off always:

- `Compact`: `kvServer.Compact` over the server's `Compact` (`compactOk`, admin);
- `Defragment`, `Snapshot`, `Hash`, `HashKV`, `MoveLeader`, `Downgrade`: the
  `authMaintenanceServer` wrappers over the `maintenanceServer`'s (admin; `Snapshot` on the
  stream's context);
- `Alarm`: authenticated for `GET`, admin otherwise (`alarmTok`, over `GetAction` as a contract);
- `Status`: authenticated;
- `MemberRemove`: `EtcdServer.RemoveMember` over `mayRemoveMember` and `configure` (admin,
  `checkMembershipOperationPermission`); `MemberAdd`, `MemberUpdate`, `MemberPromote`: the
  guard's theorem only (`AddMember`/`UpdateMember`/`promoteMember` marshal JSON, which Perennial
  has no model of);
- `MemberList`: `EtcdServer.MemberList` (authenticated, after the linearizable read's notify);
- the lease rows: `requireAuthInfo`'s theorem (the entry points' proofs wait for the leases unit:
  `raftRequest` has no lease request; `LeaseTimeToLive`/`LeaseLeases`'s key checks need a lessor
  with a key model).

The admin guards take `IsAdminPermitted(nil)` as a premise (`srvAdminNilOk`: the store's spec
covers a non-`nil` auth info only; track S).
