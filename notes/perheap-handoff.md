# perheap handoff

## START HERE (2026-11-18, C1a in progress: draft `bf4de1328e` on branch `perheap-c1a-wip`, UNCOMPILED)

- Branch `perheap-scope` (worktree `/shared/etcd-grove-incomingof`), head `a1adfde31e` + this note. Pin 6d365ee1a:
  `--packages=/shared/tmp/manifest-6d3.json`. Builds only via `/shared/tmp/build-slot.sh` (`LEAN_NUM_THREADS=4`).
- **First:** the post-merge full build of `cd350b3c75` (log `/shared/tmp/perheap/s/full-m1.log`; launched 2026-11-18,
  waited for a slot the whole session). If it is not green, fix on `perheap-scope` before bringing C1a over.
- **C1a draft** (written in the detached scratch worktree `/shared/tmp/perheap/c1a/wt`, no `.lake`, so never compiled):
  bring it over with `git -C /shared/etcd-grove-incomingof cherry-pick bf4de1328e` (or merge the branch), then compile
  bottom-up: LibKeys → InvAuth → WhyDefs → `Spec/…/auth/authStore__AuthInfoFromCtx` → its proof → InvRequest →
  AuthReqDerive → AuthBound → AuthWhy → ReadWhy → `EtcdServer__AuthInfoFromCtx` → `requireAuthInfo` (targeted builds).
  Done in the draft: `FromIncomingContext.spec` restated (`∀ ctx md`, pre `ctxInMD ctx md`; attacked SOUND,
  `/shared/tmp/perheap/c1a/attack-fic.md`, its two docstring fixes applied; moved here from 1b, its only users the
  store and the two interceptors, which take `libCtxOk`'s `md`); `auth.ctxToken` (+`ctxToken_of_ctxInMD`, InvAuth);
  `ctxBound`/`noPrincipalFrom`/`tokRefusedFrom` by token; store `AuthInfoFromCtx.spec` = the probe's (FreshCtx.lean
  deleted; `IsAuthEnabled.wp_lb` used outright, so the link list drops that callee); server `AuthInfoFromCtx.spec` =
  old `specLb` + `tok` + gated premise (old `wp_proof` deleted; `+Lb` link entries renamed); `isReqAuthBound` one row
  (`∀ n ctx tok`); `isReqAuthBound_ctx`, `isReqAuth_ctxM` deleted; `principalBound`, `adminOutB`, `authedOutB`,
  `ctxBoundOrTLS`, the `*Why` family, `rangeWhy(Out)`, `txnWhy(Out)` by token; `principalBoundI` deleted (its users
  take `v3rpc.infoBoundT`, same body); `rangeWhy_ctx`/`txnWhy_ctx` deleted; `requireAuthInfo.spec(C)` with `tok`.
- **Next, in order** (Scope §4.2): users of the above (`grep -rn "principalBoundI\|specLb\|ctxTokenOf" Proof Spec`):
  `checkMembershipOperationPermission`, `doSerialize`, `checkLease*`, `processInternalRaftRequestOnce`, `ReqOn`
  (830, 867), `LeaseCheck` (`leaseCheckFrom` by token; v3rpc's `leaseCheckT`/`principalBoundT` then merge into it),
  `AdminOn`/`ProposeOn`/`LeaseReqOn`, `hdrBoundM`→`hdrBoundT`, `infoBoundM`→`infoBoundT`, the request specs with `tok`
  (Range/Txn: the inner contexts get `ctxToken` by `WithValue`'s transfer and `ctxInMD_cancel`), v3rpc (§4.2), the
  auth-off theorems (`tok := none`). File list: `/shared/tmp/perheap/c1a/files.txt` (152 files naming the chain).
- Forms decided (report at C1a's end): `auth.ctxToken (ctx : GoInterface)` as the Scope; `tokRefusedFrom` keeps its
  unused `M n` (less churn); gates written `E.authMode.isOn` in internal check specs (`E.authOn` unfolds to it);
  `auth_ctx_lb` (etcdserver `Results.lean`) kept, its type `.specLb` → `.spec` (to add to Q9's list).
- Pitfalls: `iframe #` may not match `E.authOn` against `E.authMode.isOn` syntactically; `authPubLbM_zero` is a `|==>`.
- Scans: `/shared/tmp/perheap/closure2.py` (`closure2.txt`), `scan4.py`, `scan-text.txt`/`scan-meaning.txt`.

## History

- C0 START HERE (2026-11-18, `a1adfde31e`): step 0 done `be6b6ca8c6` (full build green, interfaces unchanged,
  tcb 892/4); lean merged `cd350b3c75`.

- Scope revision 3 (2026-11-18, `a822edbc16`), START HERE then: probes `/shared/tmp/perheap/Probe.lean`,
  `ProbeAuth.lean` (the auth chain by token, proved), `ProbeErr.lean`.

- Revision 2 (2026-11-18, `3b10ff2b93`): answered review 1 (B1, B2, M1, M2, SpecPlan names, H0 hot fix, Q1–Q16);
  errors probe `ProbeErr.lean`; two Pending ledger entries.
- Revision 1 (2026-11-18, `dda8f5f7d8`): Scope written; Q1–Q10.
