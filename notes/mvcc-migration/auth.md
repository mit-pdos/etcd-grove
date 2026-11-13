# The auth package's migration onto mvcc's API (strict M1): hand-off

Scope: `server/v3/auth` (`Spec/go_etcd_io/etcd/server/v3/auth/`, `Proof/go_etcd_io/etcd/server/v3/auth/`).
The task: the store's specs over the API's vocabulary in place of mvcc's internals, re-proved, meeting
the server's restated `apply/Contracts.lean` and `apply/AuthSteps.lean`, so that the server's bridge
`AuthSteps.csContractA_old` can go.

## Done (2026-11-05)

- **What auth used of mvcc's internals** was small: the critical-section contract
  `mvcc.csContract P (f : val) Pre Q Post` (in the write side's contracts and in every admin spec),
  `InvAuth`'s import of `mvcc.InvStore`, and `NewAuthStore.spec`'s `mvcc.KBReal`. Nothing in auth
  names `storeWT`/`storeRT` (the write token is the abstract `T`, the server's instantiation).
- **The contract is the API's** `srvApi.csContractA P f` (`lease/MvccShapes.lean`, over
  `mvcc.api.hookRun`), at the hook `f : GoFunc` (not its value): `InvAuth`'s write side
  (`authBatchTxLk`, `authBatchTxLkR`, `authBatchTxOk(R)`, `authBackendReads`, `authWBackendOk(R)`,
  `authWR`), `TieRes.authWB`, `LatestTie.authWRx`/`authWRxB` and the `specT`/`specTB` variants,
  `NewAuthStoreOn.newAuthStore_on`/`authWRAt`, `Boot.newAuthStore_boot`, and the specs of
  `AuthEnable`, `AuthDisable`, `Authenticate`, `HasRole`, `Recover`, `RoleAdd`, `RoleDelete`, `RoleGet`,
  `RoleGrantPermission`, `RoleList`, `RoleRevokePermission`, `UserAdd` (both), `UserChangePassword`,
  `UserDelete`, `UserGet`, `UserGrantRole`, `UserList`, `UserRevokeRole`, `commitRevision`: each
  `(f : val)` became `(f : GoFunc)` and `mvcc.csContract P f` became `srvApi.csContractA P f`, nothing
  else. `csContract_noWrite` is over `csContractA` (same statement otherwise).
- **`HasLC`.** The API's `hookRun` is at `HeapGS HasLC.hasLC`, so the write side is too:
  `InvAuth`'s write side is its own section `wdefs` at `hasLC` (the rest of `InvAuth` stays generic in
  `hlc`), likewise `TieRes`'s `authWB`/`authWRx_split`/`_join` (section `resW`) and `LatestTie`'s
  `authWRx`.. `authWR_to_x` (`resW`) and its `spec`/`derive` sections; the spec files above and their
  proofs, `NewAuthStoreOn`, `Boot` are at `hasLC`. The read side (`authInv`, the permission checks,
  `adminOutX`, ...) stays generic, so the server's generic users (`ApplyTieOn`, `InvAuthBackend`,
  `InvRequest`, authkv's `ClientAuth`) are unaffected. Every server user of the write side was at
  `hasLC` already.
- **`InvAuth` imports `lease.MvccShapes`** (which imports only `mvcc.Api`) in place of `mvcc.InvStore`.
- **Proved**: every auth module but `NewAuthStore`/`NewTokenProvider` builds (`lake build` of the
  137 modules of `Spec/.../auth` and `Proof/.../auth`, 2026-11-05), no `sorry`, no new axiom; the
  proofs needed no change beyond the statements (the contract is passed through to `Lock()`, never
  run by auth's own code; `csContract_noWrite` is the only lemma over its body).
- **The two meet**: `apply.isAuthSteps st P (f : GoFunc) M W` (the server's) is met by the restated
  specs directly, at `W := auth.authWR st M P f T ∗ auth.tpAdmin st M`, **without `hf : f ≠ func.nil`
  and without `csContractA_old`**: checked in a scratch copy of `isAuthSteps_of_authInv` with `hf`
  and the eleven `ihave Hcs := csContractA_old P f _ _ _ hf $$ Hcs` lines removed and `#f` → `f`,
  which elaborates against the restated specs with no error.
- **`auth.NewAuthStore.spec`** (the trust-boundary axiom; its statement is over the server's
  `authApplyOk`, `isReqAuth`, `authRecoverOk`): the backend is a `mvcc.api.BkRef` `d` (`d.γB`, `d.P`,
  `d.b`) in place of `mvcc.KBReal`, and the three premises `d.P.has mvcc.auth{,Users,Roles}BI` are one,
  `auth.authParams d.P` (new, `InvAuth.lean`: each auth bucket in the table, a hook bucket, not
  safe-range, tracked, no hook key: the auth buckets' rows of `KBReal.P`). **A generalization of an
  axiom** (to review): it was stated at `KBReal.P` only, whose rows for the other buckets and `FV`
  it now leaves free; the code `NewAuthStore` runs touches only the auth buckets (the docstring's
  argument), so the rows kept are those its truth uses. Checked (scratch): for every `KBReal d`, the
  old three premises imply `authParams d.P`, so every old instance is an instance of the new one.
  **Not built**: it imports `etcdserver.InvBoot`, red under strict M1 (`InvRead.olean` missing,
  the server's track); `NewTokenProvider.spec` has nothing of mvcc to restate and waits on the same
  import.

## For the server track (what can go, what must follow)

Delete, in `Proof/.../etcdserver/apply/AuthSteps.lean`:
- `csContractA_old` (the bridge);
- `isAuthSteps_of_authInv`'s `(hf : f ≠ func.nil)`, its eleven `ihave Hcs := csContractA_old …`
  lines, and `#f` → `f` in its statement (`auth.authWR st M P f T`); its users
  (`Results.lean:1170`, `AuthSrv`, `ApplyNormalOn`) drop the `hf` argument.

Follow (they name the old shapes and break on this change; all at `hasLC` already):
- `apply/AuthStepsX.lean`: `isAuthStepsX`'s `(f : val)` → `GoFunc`, its `mvcc.csContract P f` →
  `srvApi.csContractA P f` (lines 73-128); `auth.authWRx_join`/`_split` now take `f : GoFunc`.
- `StoreLatest.lean` (`authWBackendAt`, `adminW`, the two `∃ … (f0 : val)` at 155, 184,
  `adminW_of_beOn`, `beOn_of_adminW`), `AuthApplyRes.lean` (44, 62): `f : val` → `GoFunc` in
  `auth.authWBackendOk`'s argument.
- `AuthSrv.lean` (150-165: `(f : val)`, `#f'`, `mvcc.csContract`; 344: `newAuthStore_on`'s `f` is a
  `GoFunc`), `Results.lean` (1968-1978: `authWBackendOkR … P f T`, `mvcc.csContract`).
- `SnapRO.authApplyOk`/`authApplyOkM`/`authRecoverOk` and `InvBoot` (382: `d.P.has mvcc.authBI ∧ …`):
  over `BkRef` and `auth.authParams d.P` to meet the restated `NewAuthStore.spec` (`authApplyOk` is
  already ill-typed against the restated `isAuthStore`, `Pk : BkRef → IProp`, `f : GoFunc`).

## Placeholders

None (no `sorry`, no axiom added; one axiom restated: `auth.NewAuthStore.wp_proof`'s statement, above).

## Found

Nothing false. No frozen API statement was too weak for auth: auth uses of the API only
`csContractA`/`hookRun` (as a value it passes on) and `BkRef`.
