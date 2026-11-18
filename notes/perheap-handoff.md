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
  revokeExpiredLeases, Compact, AdminOn, AuthnOn (token from `libCtxOk`), Authenticate, traceutil (`Tracer.Start` post =
  the ctxInMD transfer, moved from 1b; StartLaws, EnsureTrace), etcdserver `Link.lean` (632 s). Targeted build 1
  (`/shared/tmp/perheap/s/c1a-t1-1.log`): three of the four auth-off theorems built; the fourth (txn_applied's premise
  form) and InvAuthAdmin/ServerKVOn/InvLeaseRead fixed after it. Targeted build 2 (`c1a-t2-*.log`, targets
  `/shared/tmp/perheap/s/t2-targets.txt`): etcdserver Results, restart examples, the v3rpc modules drafted (guards,
  ServerKVOn, LeaseOn, ServerLease*, InvLeaseRead, LeaseServer TTL/Leases).
- **v3rpc state:** AuthAdmin/authMaintenanceServer/kvServer.Compact specs and proofs take `tok` + the gate
  (`E.authMode.isOn`); `srvKVAnsOn/M` call carries `□ (⌜on⌝ → ctxToken ctx tok)`; `lessorGrantOkGM`/`lessorRevokeOkM`/
  `lessorTTLOk`/`lessorLeasesOk` gain `∀ tok` + the gate; `ttlAns`/`leasesAns`/`leaseTTLOut`/`leaseLeasesOut`/
  `leaseGrantResM`/`leaseRevokeResM` by token. Not yet: the watch chain (`swsIs` uses `auth.ctxTokenOf (ok ci)`;
  `isWatchPermitted.spec` still names the deleted `principalBoundI`: make it `v3rpc.infoBoundT … tok` with `swsIs`
  taking `tok`), AuthService (`hdrBoundM_tok s E (ok ci)`), InvLease*/LeaseServer grant/revoke handlers, Results;
  these consume the handler contracts, so they go with 1b (grpcAccepted supplies `ctxToken ci (mdTokenOf md)`).
- Build 2 (`/shared/tmp/perheap/s/c1a-t2-1.log`): etcdserver `Results` BUILT (the four auth-off theorems), ServerKVOn,
  InvAuthAdmin, the maintenance guards, kvServer.Compact built; failures fixed after it (renewAns/raftLeaseRenew by
  token, lessorGrantOkGM_mono, AuthService's adminOutOn_reply/authWrapOut_admin) except `isWatchPermitted.spec`
  (watch chain). The restart examples wait on the v3rpc modules they import.
- **Next, in order:** rebuild build 2's targets; the watch chain (`swsIs` by `tok`, `isWatchPermitted`, recvLoop,
  sendLoop, `watchServer.Watch`) + AuthService handlers + the lease grant/revoke/keepalive handlers; 1b (§4.1); client
  Results; examples auth (§4.3); full build at C1; tcb `--check --update`; interfaces; attack of new trusted text
  (Tracer.Start's restatement: agent report `/shared/tmp/perheap/attack-tracer.md`).
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
