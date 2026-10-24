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

Not yet (as of A1): the method-level statement for the principal the request's header names
(done 2026-10-24, below), `RangeStream`, the lease rows, and everything outside the KV and watch
services (A2, A3).

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

The admin guards take `IsAdminPermitted(nil)` as a premise (`srvAdminNilOk`); since S3
(2026-10-24) the store's spec covers a `nil` auth info and `apply.isAuthStore` states it, so the
premise is derivable (`srvAdminNilOk_of_srvAuthAt`) and its removal from the 12 specs is a
mechanical follow-up.

## What is proved of the store (S3, 2026-10-24)

The checks the table's RBAC and admin rows call return the model's verdicts in every mode
(`notes/decisions.md`, "S3 of the auth plan"): `IsPutPermitted`/`IsRangePermitted`/
`IsDeleteRangePermitted` `auth.permVerdict` (in `on γa`: on a pass a recorded state at which the
principal is granted the key or range -- the root role, or coverage for a request of the shape the
cache decides -- or auth is disabled, and a recorded state whose revision admits the token; on a
refusal the four states read, in which the check refuses), `IsAdminPermitted` `auth.adminVerdict`
(a `nil` auth info covered), `IsAuthEnabled`/`Revision` theirs. The apply layer's contract is
derived of the real store in its own mode (`isAuthStore_of_authInv`); the mode `on γa` reaches the
contract once S4 produces the store's invariant with the history.

## What is proved of the table (A3, the apply layer, 2026-10-24)

The request's principal (`apply.principalOf rq`: the raft request header's `Username` and
`AuthRevision`, what `authApplierV3.Apply` puts in its `authInfo`) is an index of the chain's
resources, and the KV methods' posts state the row's class for it through the whole chain
(`apply.chainClass`; `notes/decisions.md`, "A3 of the auth plan, the apply layer"):

- `Put`, `DeleteRange`, `Range`, `Txn` at apply: `authApplierV3.{Put, DeleteRange, Range, Txn}`
  (the auth layer rejected, or `reqClass` of the principal: `putClass`, `deleteClass`,
  `rangeClass`, `txnClass`), through `quotaApplierV3`, `applierV3Capped`, `applierV3Corrupt`
  (`Results.lean`: `chain_put`, `chain_deleteRange`, `chain_range`, `chain_txn`: an outcome that
  passed the auth layer has the class), `uberApplier.dispatch`, `uberApplier.Apply` and the
  package's `Apply` (`applyAuthRes`: dispatched with `shouldApplyV3`, the class for
  `principalOf rq`);
- `AuthEnable`, `AuthDisable`, `UserAdd`, …, `RoleList` (the admin rows at apply):
  `authApplierV3.Apply`'s admin check passed for `principalOf rq` (`adminPass`: `IsAdminPermitted`'s
  verdict at `nil`, A0) whenever the `applyFunc` ran, up to the package's `Apply`;
- `UserGet`: `authApplierV3.UserGet`'s `nil` error says the principal is an admin or the user
  itself (`userGetClass`; at the method level: the generic triple does not carry it).

Not stated: `RoleGet`'s "or a role the user has" (`HasRole` has no model in `isAuthStore`),
`LeaseRevoke`'s keys (the lessor's key model), the server-level statement over the decoded
entry (`applyEntryNormal`: E).

## What is proved of the table (A4, the watch shapes, 2026-10-24)

The `Watch` row at the API layer, over every request shape (`notes/decisions.md`, "A4 of the
auth plan"; `Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/WatchClass.lean`): a created
control response's watcher (`v3rpc.ctrlWatcher`, the stream specification's) carries
`v3rpc.watchAuthed`, the class `apply.watchClass M info key rangeEnd` (RBAC read of `[Key,
RangeEnd)`: the key normalized, `"\x00"` for an empty one; the range end as the request gave it:
empty, a point; `"\x00"`, from the key on, `WithFromKey`; else the range, `WithPrefix` included)
in the server's auth mode (named by the watchable store's owner tag, `auth.modeTag`) for the
principal the check saw; and every key the registered mvcc range covers is in that interval
(`createRangeOk_inRange`). `watch_registered_authorized` (`v3rpc/Results.lean`): in `on γa`, a
recorded state at which auth was disabled, or the principal a root user, or one whose READ
permissions cover every covered key. `ProgressRequest`/`CancelRequest` register nothing;
`Fragment` and the filters change no class. GHSA-xg4h-6gfc-h4m8 (the advisory table above) is
the statement's negative: at the pinned revision the check sees the interval mvcc registers.
Not stated: the token's binding to the principal (S5), a re-check of live watchers (there is
none: etcd's documented behaviour).


## What is proved of the table (A3, the API layer, 2026-10-24)

The Auth service's seventeen rows at the API layer (`notes/decisions.md`, "A3 of the auth plan,
the API layer"): the gRPC wrappers (`v3rpc/AuthServer__*.lean`) call the server's method and pass
its error through `togRPCError`; the server's entry points (`etcdserver/EtcdServer__*.lean`) are
`raftRequest` on the request with the one field, taken as a contract (`authRaftOk`: the proposal
path's model has no auth request), the response asserted to its type. Nothing of auth is checked
on this path: the rows' class (admin at apply, `UserGet`'s "or the user itself") is the apply
layer's statement (`adminPass`, `userGetClass`, above). Fourteen entry points are proved;
`Authenticate` is translated and not (`auth.ErrAuthNotEnabled` is not in the auth package's
fact); `UserAdd`, `UserChangePassword` are names only (they hash with bcrypt and base64). The
"`UserChangePassword` of oneself" exception is not in the pinned code: `needAdminPermission` names
the request unconditionally (the row above is right).

Stated at the API layer so far: A2's twelve (`Compact`, the eight maintenance wrappers,
`MemberRemove`, `MemberList`, the lease rows' guard) and these seventeen. Remaining: `Lock`,
`Unlock`, the five `Election` rows (the client's `concurrency` package over the in-process client),
the lease rows' key checks (a lessor with a key model), `MemberAdd`/`MemberUpdate`/`MemberPromote`
(`encoding/json`).

## What is proved of the table (S4, the store's admin side, 2026-10-24)

The store's `AuthEnable`, `AuthDisable`, `UserAdd`, `UserDelete`, `UserChangePassword`, `RoleAdd` and
`Recover` perform the model's step on the latest recorded state (`auth/Steps.lean`, `adminOut`): the
state appended to the history, or the model's refusal. The admin rows' class at apply is unchanged:
`apply.isAuthStore`'s admin clauses are still the `isAuthStoreAdmin` contract (stating them as steps
needs the authority in the apply environment); `UserGrantRole`, `UserRevokeRole`, `RoleDelete`,
`RoleGrantPermission`, `RoleRevokePermission`, `UserGet`, `RoleGet`, `UserList`, `RoleList` are
translated, not proved.


**At apply** (S4's apply part, 2026-10-24; `notes/decisions.md`, "S4's apply part";
`apply/AuthSteps.lean`): `applierV3backend.AuthEnable`, `AuthDisable`, `UserAdd`, `UserDelete`,
`UserChangePassword`, `RoleAdd` perform the store's step (`apply_AuthEnable_step`, ...,
`etcdserver/Results.lean`), from the auth store's `isAuthSteps` (of the real store:
`auth_apply_steps`), the admin side's authority and the store's write resource; with A3's
`adminPass`, an applied one is a step of the history made by an admin. The other admin rows at
apply (`UserGrantRole`, `UserRevokeRole`, `RoleDelete`, `RoleGrantPermission`,
`RoleRevokePermission`, the reads) keep the contract clause.

## What is proved of the table (S5 in part, the token binding, 2026-10-24)

Every row's principal at the API layer is `AuthInfoFromCtx`'s, and since S5 it is bound to the
request's token in the mode (`auth.ctxBound`: in `on γa`, its user is one the token was issued to,
`tokIssued`), over the token provider's contract (`tokenProviderOk`); the server's
`isReqAuthBound` states it of the real store (`etcdserver/AuthReqDerive.lean`). The `Authenticate`
row: the store's `Authenticate` is proved (a token issued to the user, the user present in the
latest state, auth enabled at a recorded state); the server's entry point and `CheckPassword` are
not. No real token provider is proved to meet the contract yet (the no-op one does); the rows'
statements of A2 and A4 still name the unbound info (`isReqAuth`).

## What is proved of the table (S4b, 2026-10-24)

The store's `UserRevokeRole`, `RoleRevokePermission` and `RoleDelete` perform the model's step
(`auth/Steps.lean`), and `applierV3backend`'s three perform it at the apply layer
(`apply/AuthSteps.lean`, `apply_*_step` in `etcdserver/Results.lean`); `hasRootRole` (every check's
root shortcut) is proved. Left: `UserGrantRole`, `RoleGrantPermission` (they write into the
messages the read contract gives read-only: `notes/decisions.md`, "S4b of the auth plan").

## What is proved of the table (S5b in part, the simple provider, 2026-10-24)

The binding every row's principal rests on (S5's `ctxBound`) is now met by etcd's default provider
for the tokens it accepts and issues: `tokenSimple`'s `info` returns a user only for a token the
map holds, each issued to that user, and `assign` issues the token it stores
(`auth/TokenSimple.lean`). Not yet: the provider's `enable`, `disable` and `invalidateUser`
(so not yet `tokenProviderOk` of `tokenSimple` as a whole), and the guards' statements (A2, A4)
naming the bound principal.

## What is proved of the table (S4c, 2026-10-24)

`UserGrantRole` performs the model's step at the store and at the apply layer
(`apply_UserGrantRole_step`), from the user message the decoder gives the caller (the two
`proto.Unmarshal` axioms' posts restated: `notes/decisions.md`, "S4c of the auth plan"). The
store's `HasRole` answers the latest state's (with the admin side's authority). Left:
`RoleGrantPermission` (its contract clause), `UserGet`, `RoleGet`, `UserList`, `RoleList`.

## What is proved of the table (S4d, 2026-10-24)

`RoleGrantPermission` performs the model's step at the store and at the apply layer
(`auth/authStore__RoleGrantPermission.lean`, `apply_RoleGrantPermission_step`): every admin
operation of the store is a proved step. Its spec takes the read-only ownership of
`authpb.Permission_Type_name` (an untranslated initializer) as a premise (`auth.typeNamesOk`).
