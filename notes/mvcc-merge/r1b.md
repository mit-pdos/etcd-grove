# Repair track R1b: mvcc's reader tokens through txn, apply and lease (2026-11-07)

After `de9d792365` (mvcc's API: `mvccReaders γ n`, taken by every reading contract beside
`threadTok` and given back; `notes/decisions.md`'s last entry). Scope: `etcdserver/{txn,apply}`,
`lease`, `auth`.

## Build

- **txn**: all 118 modules (`Spec`/`Proof` of `etcdserver/txn`), `Link.lean` (regenerated:
  unchanged) and `Results.lean` included. No `sorryAx` printed.
- **apply**: all 191 modules (R2's set: `M2ApplyDraft`, `CompactArm` left out), including the 11
  that R2 left red (`applierV3backend__{Compaction,DeleteRange,LeaseGrant,LeaseRevoke,Put,Range,Txn,
  newHeader}`, `Link`, `Results`). No `sorryAx` printed in `Results`.
- **lease, auth**: all 243 modules, including the ten R1 left blocked by `InvBoot`, which the
  server track has since made build (`NewLessor`, `lessor__Recover`, `leasehttp/RenewHTTP`,
  `NewAuthStore`, `NewTokenProvider`).
- `etc/api-check.py etc/api/mvcc.txt --check`: the one error is the server's (`NewServer` imports
  `mvcc.ReaderRetire`).
- No `sorry`, no axiom added or removed. `etc/tcb-report.py --check` not run (the server is red).

## Where the apply chain's token lives

It sits beside `threadTok`, as one name: **`apply.applyTok E := threadTok ∗ mvcc.api.mvccReaders
E.γ 1`** (`Chain.lean`, before `kvOwn`). Every chain triple that took `threadTok` now takes and
gives back `applyTok E`. That covers the Spec files, `Chain`'s `applierTriples`/`cmpTriple`, and the
internal step statements (`AuthSteps`, `AuthStepsX`, `AuthFuel`, `AuthApplyLatest*`, `DispatchKVL`,
`DispatchAdmin`, `ApplyKVL`, `ApplyAdmin*`, `ApplyFn*`, `ApplyRec`, `AdminChain`, `Results`).

Why this placement:
- Every chain method reads the store. `newHeader`'s `KV.Rev` needs the token, and almost every
  method calls `newHeader`. So the token goes everywhere `threadTok` goes.
- The pair is opaque to IPM. The wrapper layers (auth, quota, corrupt, capped, uber, dispatch,
  KVL/admin) pass it on unchanged, so none of their proofs needed edits.
- Only the leaves unfold it: `newHeader`, `Compaction`, `Put`, `DeleteRange`, `Range`, `Txn` and
  `LeaseRevoke`.
- `kvOwn` (and `mPre`, `kvOwnPre`) were rejected as the place. The server unfolds `kvOwn` in nine
  files and holds it across snapshots. The server hands `applyTok` per call instead, and keeps its
  tokens outside the apply thread's resources for `Close`.

## Spec changes (old → new)

**txn** (each a reading spec: `mvccReaders γ 1` beside `threadTok`, in and out):
- `txn.Count.spec`, `txn.Range.spec`, `txn.Put.spec`, `txn.DeleteRange.spec`, `txn.Txn.specSole`,
  `txn.Txn.specRead`: pre `… ∗ threadTok ∗ …` → `… ∗ threadTok ∗ mvcc.api.mvccReaders γ 1 ∗ …`;
  post `threadTok ∗ …` → `threadTok ∗ mvcc.api.mvccReaders γ 1 ∗ …`.
- `ApiLemmas`: `txn.end_read`'s post `threadTok` → `threadTok ∗ mvccReaders γ 1`; `txn.end_write`'s
  post `threadTok ∗ mvccBackend … ∗ Q` → `threadTok ∗ mvccReaders γ 1 ∗ mvccBackend … ∗ Q`
  (`Txn.End`'s new post).
- `Results`: `range_rangeSel` and `txn_runTxn` gain the same token, in and out.

**lease**:
- `lease.lessor.Revoke.spec`: pre `… ∗ threadTok ∗ lease.rdOwn γl rd ∗ …` → `… ∗ threadTok ∗
  mvccReaders γ 1 ∗ lease.rdOwn γl rd ∗ …`; post `threadTok ∗ lease.rdOwn …` → `threadTok ∗
  mvccReaders γ 1 ∗ lease.rdOwn …`. The deleter's transaction holds the token until `End`.

**apply**:
- New definition `apply.applyTok E` (above).
- In each of these 48 specs, `threadTok` → `apply.applyTok E` in the pre and the post:
  `applierV3backend__{AuthDisable, AuthEnable, AuthStatus, Authenticate, Compaction, DeleteRange,
  LeaseCheckpoint, LeaseGrant, LeaseRevoke, Put, Range, RoleAdd, RoleDelete, RoleGet,
  RoleGrantPermission, RoleList, RoleRevokePermission, Txn, UserAdd, UserChangePassword,
  UserDelete, UserGet, UserGrantRole, UserList, UserRevokeRole, newHeader}`,
  `applierV3Capped__{LeaseGrant, Put, Txn}`,
  `applierV3Corrupt__{DeleteRange, LeaseGrant, LeaseRevoke, Put, Range, Txn}`,
  `authApplierV3__{DeleteRange, LeaseRevoke, Put, Range, RoleGet, Txn, UserGet}`,
  `quotaApplierV3__{LeaseGrant, Put, Txn}`, `uberApplier__{Alarm, Apply, dispatch}`.
- `Chain`: the same change in the triples of `applierTriples` and in `cmpTriple`.
- `Contracts.revokeClause` (`isApplyLessor`'s Revoke clause, a component contract at `γ`): pre and
  post `threadTok ∗ …` → `threadTok ∗ mvcc.api.mvccReaders γ 1 ∗ …`, matching `lessor.Revoke.spec`.
- `Results`: `chain_put`, `chain_deleteRange`, `chain_range`, `chain_txn` and `chain_revoke` have
  `apply.applyTok E` in place of `threadTok`.

## Other changes

- `applierV3backend__LeaseGrant`: an `imodintro` before `iapply HΦ`. This finishes R2's
  `wp_fupd` fix, which R2 had never checked.
- **Link**: `etc/link-lean-first-apply.txt` drops mvcc's internal callees (`mvcc_store__Rev`,
  `mvcc_store__Compact`, `mvcc_readView__Range`). `newHeader` and `Compaction` now take
  `=mvcc.api.mvccApi_shapes_law`, as their proofs had since strict M1.
- `etc/gen-link.py`: `EXTRA_IMPORTS["--apply"]` adds mvcc's `ApiResults`, as for `--txn`.
- `apply/Link.lean` regenerated:
  - It imports `ApiResults` instead of mvcc's `Link`.
  - It no longer declares `raftAsm`.
  - The linked results that reach `shapes.law` take `[go_etcd_io.etcd.cache.v3.Assumptions]`
    (the generator's `eq_needs_cache`, as in txn's Link).

## What the server must pass

- **Callers of `uberApplier.Apply`** and its variants (`Apply.wp_kvL`, `wp_adminL`, `ApplyRec`,
  `ApplyFnKVL`/`ApplyFnAdminL`, `dispatch`) must pass `apply.applyTok E` where they passed
  `threadTok`, and get it back.
  - To build it: `iunfold apply.applyTok; iframe Htt Hrd`, from `threadTok ∗ mvccReaders E.γ 1`.
  - The token comes from `New`/`NewStore`'s `mvccReaders γ mvccReaderN`, split by
    `mvccReaders_split.law`.
  - The server keeps it outside `kvOwn` and returns it before `Close`, whose
    `mvccClosed_rest.law` needs all `mvccReaderN` tokens.
- **`EtcdServer__Range`** (`txn.Range.spec`) and **`EtcdServer__Txn`** (`txn.Txn.specRead`): pass
  `mvccReaders γ 1` beside `threadTok`, and get it back.
- **`isApplyLessor`'s Revoke clause** and **`lessor.Revoke.spec`** take and give `mvccReaders γ 1`.
  - The server's derivation goes through `LessorDerive.revokeClause_of_lessorInv`, whose statement
    text is unchanged.
  - The modules that mention `lessor.Revoke.spec` may need nothing more than a rebuild:
    `SnapApplyOpts`, `SnapApplyOptsLemmas`, `SnapApplyPost`, `EtcdServer__applySnapshot`,
    `NewServer` and `etcdserver/Link`.
- **The server's `Link`**, where it links apply's results: those results that reach `shapes.law`
  now take the cache's assumptions as an instance argument.

## Not this track's

- `examples/mvccrand` (`writer__revoke` calls `lessor.Revoke.spec`) is red upstream of it:
  `WriterLease.lean:157` and `TxnEnd.lean:127` fail on mvcc's new API, before this track's change.
  It needs the token like `lessor__Revoke`'s proof (`$Htt $Hrdr` into the deleter, `End`'s
  continuation with `mvccReaders γ 1`).
- `notes/STATUS.md` not updated: left to the coordinator, as in R1 and R2.
