# auth-schema-fix: handoff (2026-11-12)

Stage of etcd-grove-81: make the auth results non-vacuous (S1: remove `auth.ValidSpec`; S0's F1-F4
in `authSchemaSrv`). Worktree `/shared/etcd-grove-authfix`, branch `auth-schema-fix` (from lean
`2f8cf80b7e`). Plan: `/shared/tmp/auth-safe/fix-plan.md`; Freeze package (in progress):
`/shared/tmp/auth-safe/freeze-fix.md`. Not landed; STOP for 81's axiom re-review once the targeted
builds pass.

## Done (committed, targeted builds pass)

- F3 (`e450457d89`): `auth.roleListed n := n ≠ [] ∧ GoStringLt n [0xff]`; `rolesOut` and
  `roleListOut` (RoleList's reply) list only those roles. nonissues F3 and F4 written.
- F2 (`350380537e`): `authBkLend` hands an abstract observation `RL` with the law
  `□ ∀ r, RL -∗ backend.rbOwn d.γB r -∗ ⌜authBucketsAt st r⌝ ∗ RL ∗ backend.rbOwn d.γB r`
  (no `rbPart`: no write authority); `bkLendW` the same shape; `srvAuthApplyResB_lend`,
  `acRes_lend`, `bkLendW_none`, the window (SnapSendBranch: the law applied inside the
  snapshot's observation, then `snapObsA` at no lent bucket) adapted. Built: SnapSendBranch,
  StoreLatest, AuthComp, AuthSrv, SnapAuthRecover, ApplyAllSnap.
- Go evidence for F4's supply: `/shared/tmp/auth-safe/fix-tests/irr_utf8_test.go` (passes at the
  server pin: `pbutil.MustUnmarshalMessage` panics on an InternalRaftRequest whose UserGrantRole
  role/user, UserAdd name or RoleAdd name is not valid UTF-8).

## S1 in progress (stashed: `git stash list`; same diff in /shared/tmp/auth-safe/s1-wip.patch)

The WIP restates the token contract's `info` clause over `auth.ctxDoneAny`, `tokenSimple_isValid`
over it (with `chan.wp_select_blocking_nil` + `chan.nilClausePre_recv` for a nil Done), deletes
`ValidSpec`/`tokenSimple_info`/`tokenProviderOkCtx`/`tokenSimple_okCtx`, adds `ctxDoneAny` to the
store specs `authInfoFromToken` (ctx now `GoInterfaceOk`) and `AuthInfoFromCtx`, and threads it in
AuthReqDerive. Two blockers found:
1. **`tokenProviderOkA`/`tokenProviderOk` are in a section generic in `hlc`** (InvAuth.lean ~740),
   but k8s 7f-4's `auth.ctxDoneAny` is at `HasLC.hasLC` (it names `context.isContextDone`, which is
   hasLC-only). Build error "failed to synthesize HeapGS HasLC.hasLC GF" at InvAuth 749/778.
   Recommended fix (form-level): an hlc-generic `auth.ctxDoneRecv ci` ("Done() returns nil or a
   channel a receive may complete on with any outcome", i.e. `anyRecv`, moved before InvAuth), used
   in the contract, with a law `auth.ctxDoneAny ci ⊢ auth.ctxDoneRecv ci` at hasLC (from
   `isContextDone_is_chan`/`isContextDone_receive`), so isReqAuth keeps `ctxDoneAny`.
2. **`ValidSpec` also covered the provider's index waiter**: `tokenSimple_okA` now needs
   `simpleWaitOk p` (iw's channels `anyRecv`), which `authSrvTP_on` does not have
   (NewTokenProvider's post gives only `tsF "indexWaiter" p ↦□ iw`). Needs `authSrvTP`'s pre (on
   mode) to carry `□ ∀ idx, {{True}} iw idx {{ch; anyRecv ch}}`, discharged in NewServer from
   `wait.timeList.Wait.spec` (`waitBcast ch Q`) plus a law `waitBcast ⊢ anyRecv`. No trust change;
   not foreseen by the Scope (its "no new trust, the request side has a context" covered only the
   context half). Ask 81 whether to take this route.

## Next, in order

1. S1: resolve blocker 1 (ctxDoneRecv), unstash, finish (TokenSimpleAdmin/TokenKeeperRun/Results
   `token_simple_ok`, AuthSrv `authSrvTP_on` drops `hValid`, needs blocker 2), etcdserver Results
   `srv_auth_tp_on`/`server_new_auth_on`, authkv Results (exported: CP).
2. F4 (plan step 4): UnsafePutUser `∀ x ∈ ur.roles, utf8Valid x` in authBatchTxLkR and
   authBatchTxLk; state invariant `rolesUtf8` beside permKeysOk; `apply.irrDecode_utf8` (new
   trust-boundary law, Go test above).
3. F1 (plan step 5): `Wb` parameter; the boot budget question (plan) for 81.
4. Notes (`notes/auth-validspec-false.md`, `notes/auth-schema-srv-refuted.md` status, decisions.md
   entry, STATUS.md), interfaces (`etc/gen-interface.py etc/api/<pkg>.txt`), tcb collections,
   Freeze package complete; STOP.

## Pitfalls

- InvAuth's write/read contracts sit in hlc-generic sections in places; check the section before
  using hasLC-only vocabulary.
- `rbPart_none` takes the map explicitly: `backend.rbPart_none d.γB ∅`.
- Build: `export TMPDIR=/shared/tmp; systemd-run --scope -q -p MemoryMax=64G lake build
  --packages=/shared/tmp/manifest-ddc.json <modules>`; full build under flock with etc/timed-build.py.
