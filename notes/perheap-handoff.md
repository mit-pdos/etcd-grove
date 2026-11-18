# perheap handoff

## START HERE (2026-11-18, C1a compiling: draft cherry-picked onto `perheap-scope`, server chain lean-checked)

- Branch `perheap-scope` (worktree `/shared/etcd-grove-incomingof`). Pin 6d365ee1a: `--packages=/shared/tmp/manifest-6d3.json`.
  Builds only via `/shared/tmp/build-slot.sh` (`LEAN_NUM_THREADS=4`). Post-merge full build of `cd350b3c75`: GREEN
  (`/shared/tmp/perheap/s/full-m1-1.log`). Check loop: `/shared/tmp/perheap/s/chk.sh FILE...` (lean-check `--fast -q -a`).
- **Done (C1a, lean-checked, 0 errors):** LibKeys, InvAuth (`ctxToken`, `ctxToken_transfer(_gate)`, `ctxToken_of_libCtxOk`),
  WhyDefs, `FromIncomingContext.spec`, the store's and the server's `AuthInfoFromCtx` (one spec each), InvRequest,
  AuthReqDerive, AuthBound, AuthWhy, ReadWhy, requireAuthInfo, ReqOn (`hdrBoundM`/`infoBoundM` by token; `wpM`/`wpMLb`
  gated on `on`), LeaseCheck (`leaseCheckFrom` by token, v3rpc `leaseCheckT`/`principalBoundT` merged in), the checks,
  doSerialize, processInternalRaftRequestOnce, raftRequest, ModeSpecs (admin `specOn` texts by token, `spec_off`s at
  `tok := none`), Put, DeleteRange, Range, Txn, LeaseGrant/Revoke/Renew/TimeToLive/Leases, RemoveMember, MemberList,
  revokeExpiredLeases, Compact, AdminOn (`adminPreOn` + tok and gate; `adminHistAu`/`adminOutOn` by tok), AuthnOn
  (token from `libCtxOk`), Authenticate, traceutil (`Tracer.Start` post = the ctxInMD transfer, moved from 1b;
  StartLaws, EnsureTrace). Drafted, not yet checked: etcdserver Link/Results, restart examples (`tok := none`), v3rpc
  `ServerKVOn` (call contracts carry the gated `ctxToken`), `LeaseOn` (`lessorGrantOkGM`/`lessorRevokeOkM` + tok), the
  server lease proofs.
- **Next, in order:** etcdserver `Link`/`Results`; restart examples; the rest of etcdserver's importers
  (`etc/importers.py`); then v3rpc (ServerKVOn, LeaseOn, ServerLease*, AuthService, InvLease*, InvWatch, isWatchPermitted,
  recvLoop, sendLoop, AuthAdmin__*, Results) and 1b (grpcAccepted supplies `ctxToken`; remove `incomingOf`, the two
  axioms, `WithValue`'s old equation, `ctxTokenOf`); client Results; examples auth (§4.3); full build at C1.
- Forms decided this session (report at C1a's end): `hdrBoundM`/`infoBoundM` kept as the mode-gated wrappers,
  re-indexed by token (not renamed to `hdrBoundT`: less churn; their `*_ctx` transfer lemmas deleted); `wpM`/`wpMLb`
  gate the token premise on their `on`; `RemoveMember`/`MemberList`/`checkLease*`/`checkMembership` gate on
  `E.authMode.isOn` (frames straight into their callees), the other request specs on `E.authOn` (Scope text);
  `leaseCheckFrom` merged with `leaseCheckT`; `Tracer.Start`'s restatement moved from 1b into C1a (Scope §4.1 text).
- Pitfalls: `$$ [$H]` framing is syntactic (`E.authOn` ≠ `E.authMode.isOn`): convert with `iintro !> %h; iapply H;
  ipureintro; exact h`; after `cases hon : E.authOn` the Iris context's gates become `⌜true = true⌝` (use
  `first | rfl | exact hon`), and a later `simp` can turn them into `True → …` (frame by hand); `authPubLbM_zero` is
  unqualified (outside `namespace auth`) and a `|==>`; name clash `Htok` (kvResTok) → the token premise is `HtokC`.

## History

- C1a mid-point (2026-11-18, `e39906a4a4`): draft `bf4de1328e` written uncompiled in a scratch worktree; post-merge build queued.

- C0 START HERE (2026-11-18, `a1adfde31e`): step 0 done `be6b6ca8c6` (full build green, interfaces unchanged,
  tcb 892/4); lean merged `cd350b3c75`.

- Scope revision 3 (2026-11-18, `a822edbc16`), START HERE then: probes `/shared/tmp/perheap/Probe.lean`,
  `ProbeAuth.lean` (the auth chain by token, proved), `ProbeErr.lean`.

- Revision 2 (2026-11-18, `3b10ff2b93`): answered review 1 (B1, B2, M1, M2, SpecPlan names, H0 hot fix, Q1–Q16);
  errors probe `ProbeErr.lean`; two Pending ledger entries.
- Revision 1 (2026-11-18, `dda8f5f7d8`): Scope written; Q1–Q10.
