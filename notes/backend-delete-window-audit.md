# The backend's delete window: an audit of the trusted texts over backend reads (2026-11-16)

Branch `backend-window`, for etcd-grove-02. Read-only audit: no trusted text, spec or proof changed.

## The window

`batchTxBuffered.Unlock` (`server/storage/backend/batch_tx.go:328-357`, fork pin 6e8f0c004) writes the
session's puts back into the read buffer under `readTx.Lock()`, releases it, and only then commits the
bbolt transaction when a delete is pending (`commit` takes `readTx.Lock()` again). A read transaction
(`ReadTx().RLock()`, or `ConcurrentReadTx`, which copies the read buffer under the same lock) taken in
between reads the session's puts from the buffer over bbolt's last committed snapshot, which still has
the session's deletes undone: a state no step recorded, **when the session both puts and deletes**.
A delete-only session shows the state before it (nothing to write back); a put-only session commits
nothing, and the buffer over the snapshot is the state after it. Per bucket the effect is limited to
the buckets the session wrote: the write-back merges only the session's buffer, and an earlier
session's buffered puts stay in the read buffer until the commit resets it.

The finding generalized here is R1 (auth: `nonissues/etcd-auth-readtx-delete-window-mixed-state.md`
on branch `auth-schema-srv`, `notes/auth-schema-srv-scope.md` §3 risk (3), Q9).

## The writers that put and delete in one session (every `UnsafeDelete` of `server/`)

| Session | Deletes | Puts in the same session | A concurrent reader of both in etcd |
|---|---|---|---|
| auth `UserDelete`/`RoleDelete` (+ `UserRevokeRole`, ...) | `authUsers`/`authRoles` | the auth revision (`auth`) | yes: `CheckPassword` (R1) |
| `membershipBackend.MustDeleteMemberFromBackend` | `members/<id>` | `members_removed/<id>` | no (apply thread / boot only) |
| `lessor.Revoke` | `lease/<id>` | the keys' tombstones (`key`) | no (`lease` read only under the batch lock) |
| `store.scheduleCompaction`, last batch | compacted revisions (`key`) | `meta/finishedCompactRev` | no |
| `schema.UnsafeMigrate`, a multi-step downgrade to 3.5 | `meta/storageVersion` | `meta/storageVersion` (intermediate steps) | no modeled reader (maintenance `Status`, names-only) |
| `alarmBackend.MustDeleteAlarm` | `alarm/<a>` | none (the cindex is written by the pre-commit hook inside the commit, under `readTx.Lock()`) | no window state |
| `TrimMembershipFromBackend`, `TrimClusterFromBackend` | `members`, `members_removed`, `cluster` | none | no window state |

Go tests reproducing the window at the fork pin (all fail, i.e. the mixed state is observed, within
0.03 s): `nonissues/etcd-membership-readtx-delete-window-mixed-state/`,
`nonissues/etcd-lease-revoke-readtx-delete-window-mixed-state/`,
`nonissues/etcd-mvcc-compaction-readtx-delete-window-mixed-state/` (and auth's on `auth-schema-srv`).
Each is a nonissue: no etcd reader is in the window.

## The trusted texts over backend reads

Found by: every axiom of `etc/tcb-baseline.txt` whose spec mentions the backend's read side
(`rbOwnIn`, `rbOwn`, `bkRPool`, `rdTok`, `rtHeld`, `bView`, `dget`, `KBReal`), every named hypothesis
of the `Results.lean` files (only `authSchemaSrv`), the opaque `Prop`s of the server's proofs, and every
Go call of `ReadTx()`/`ConcurrentReadTx()` in `server/` mapped to its spec.

| Text | Verdict | Why | Closed theorems resting on it |
|---|---|---|---|
| `auth.authReadTxOk` (in D22's `authSchemaSrv`, `authSchemaSnap`, `authSchemaBoot`) | **false** (R1, known) | every `RLock` promised a recorded auth state; `CheckPassword` in `UserDelete`'s window reads none | `etcd_auth_safe`, `etcd_auth3_safe`, `etcd_authN_safe` (named hypothesis) |
| `schema.membershipBackend.MustReadMembersFromBackend` | true | pre: the idle part `rbOwnIn d.γB memberBkts bk`, which every writer of those buckets needs as `rbPart` and which `MustDeleteMemberFromBackend`'s axiom returns only after its `Unlock` (commit done); Go: every caller (boot, `Recover`, `ValidateConfigurationChange`) is on the removing thread | 25 collections (`server`, `putget*`, `auth3`, `authN`, `lease*`, `k8s*`, `restart*`, ...) |
| `schema.membershipBackend.MustDeleteMemberFromBackend`, `MustSaveMemberToBackend` | true | writes; their post (`rbOwnIn`, idle) is after the commit | same |
| `membership.RaftCluster.Recover`, `SetBackend`, `clusterImageOk_restModel`, `membersOf_decode`, `membersOfBk_empty`, opaque `memBucketsOk` | true | `Recover` takes `rbOwnIn` of the three cluster buckets (as above); the others are writes or pure facts about images (bbolt committed data) | same |
| `schema.MustUnsafeGetAllLeases`, `lease.NewLessor` | true | read the batch transaction under the batch lock (the writer's contents `st.S`, bbolt's write transaction), not the read side | 26 collections |
| `schema.UnsafeDeleteLease`, `MustUnsafePutLease`, the lessor's `lessorBackend` contract | true | writes only; no trusted text gives a read transaction the `lease` bucket | same |
| `v3alarm.AlarmStore.restore`, `v3alarm.NewAlarmStore` | true | pre: `rbPart` of a set containing `alarm` (exclusive with alarm writers), the bucket empty; Go: boot or `applySnapshot` on the apply thread; and alarm sessions are delete-only or put-only (no window state) | 24 collections |
| `backend.backend.Snapshot` (and `snapshot.WriteTo`/`Size`/`Close`) | true | observes bbolt's committed data, in which a session's puts and deletes are one atomic commit (every commit is at a session's end, under the batch lock) | 27 collections |
| `EtcdServer.monitorStorageVersion` (`srvSVRes`) | true (vacuous for the window) | its sessions write only `meta/storageVersion`, which is in no modeled reader's view (`viewSame`); a multi-step downgrade's window shows an intermediate version to a reader the model does not have | 24 collections |
| `mvcc.kvHasher.Hash`, `EtcdServer.monitorKVHash`/`monitorCompactHash`, `backend.VerifyBackendConsistency` | true | no content promised (`True` posts, or the check off / `ETCD_VERIFY` off) | many |
| `auth.NewAuthStore` | true | boot read on the creating thread, no auth writer yet | 21 collections |
| bbolt's contract axioms (`rtxSnap`, `ownWTxG`, ...) | true | a bbolt read transaction sees one committed snapshot | all backend users |

Not trusted, so outside this audit's question but checked for how they meet the window: the backend's
read side is **proved** with it (`InvBackend.lean`: the readers' view `γ.view` is the read buffer over
the committed data, `RdSt` records whether an `Unlock`'s window is open; the safe-range buckets' deleted entries `dls`;
`notes/decisions.md`, "The backend's `Snapshot` axiom sees the safe-range bucket exactly"), and mvcc's
reads (`kvstore_txn.go`, `watchable_store.go`, `HashByRev`), cindex's `ReadConsistentIndex` and the
auth reads below `authReadTxOk` are proved over that read side.

## Result

No trusted text other than R1's `authReadTxOk` promises a reader a state the window refutes. Every
other trusted reader of a bucket that is written with puts and deletes in one session either holds the
bucket's idle part (`rbOwnIn`, exclusive with its writers: membership, alarm), reads under the batch
lock (lease), or reads bbolt's committed data (`Snapshot`). The Go-level behavior is recorded as
three nonissues (membership, lease revoke, compaction; `blocks-proof: no`).

A caution for the R1 restatement and any future trusted reader: a contract that gives a reader without
the bucket's idle part (a gRPC goroutine, a monitor) "one recorded state" across two buckets, or across
a put key and a deleted key of one bucket, is false for every session in the table above. Per key it
holds (the key's value before or after the session) only when the session writes the key once: a
session that puts a key and then deletes it (the multi-step downgrade) shows the intermediate put.
