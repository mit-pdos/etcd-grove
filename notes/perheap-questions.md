# perheap: decisions (the Scope's §11; `notes/perheap-scope.md`)

- **Approved by the user, 2026-11-18, via etcd-grove-03:** the redesign "incoming first, then decide": step 0 and
  the incoming part only (the two refuted `incomingOf` axioms become theorems); errors/outgoing come back to the
  user later. Independent review 3 (`/shared/tmp/perheap/review-3.md`): GO for step 0, GO for the incoming part
  with MAJOR 1 folded in (Scope revision 4).
- **Decided by etcd-grove-03, 2026-11-18** (as the Scope recommends):
  - Q2: no agreement law; SpecPlan's `ctxInMD_agree.spec` deleted (ledger entry 1, accepted).
  - Q3: `ctxInMD` over Perennial's chain, at `HasLC.hasLC` (the `{hlc}`-generic files move).
  - Q13: the auth chain by token, the twins merged (one `AuthInfoFromCtx` spec each, the `Lb` form).
  - Q14: `libCtxOk` keeps the anonymous incoming part `∃ md, ctxInMD ctx md`; `grpcAccepted` is the only source
    of a reasoned-about `md`.
  - Q15: leaves take the heap's names (`[hG : HeapGS HasLC.hasLC GF]`).
  - Q17: the mode gate `□ (⌜M.isOn = true⌝ → auth.ctxToken ctx tok)`.
- **The user's, at the land stop:** Q9 (exported text changes, the exact old → new; Scope §7, including the six
  admin-family statements revision 4 found).
- **Decided by etcd-grove-03, 2026-11-18 (at C0):** C0 ACCEPTED. Forms ACCEPTED: `auth.ctxToken` and the
  token-indexed `ctxBound` moved to C1a; `WithValue`'s transfer in step 0 beside the old `incomingOf` equation
  until 1b; `k8sCtxOk_of_nil` taking `libCtxOk`; `chanCtx_libCtxOk` with `[context.Assumptions]`. The six more
  exported text changes (`authEnable`/`roleAdd`/`userGrantRole`/`roleGrantPermission`/`userAdd_end_to_end_on`,
  `authWrapOut_userAdd_nn`) are added to the Q9 list for the user at the land stop.
- **Decided by etcd-grove-03, 2026-11-18 (at the C1a mid-point):** the C1a forms ACCEPTED (`auth.ctxToken (ctx :
  GoInterface)`; `tokRefusedFrom` keeps its unused `M n`; internal check specs gate on `E.authMode.isOn`);
  `metadata.FromIncomingContext.spec`'s restatement moved from 1b into C1a ACCEPTED (independent attack SOUND,
  `/shared/tmp/perheap/c1a/attack-fic.md`); the store's `AuthInfoFromCtx` proof using `IsAuthEnabled.wp_lb`
  directly ACCEPTED; `auth_ctx_lb` (`etcdserver/Results.lean`, its type `.specLb` → `.spec`) added to the Q9
  list for the user. The C1a/1b seam: targeted builds for C1a, the full build at C1.
- **Forms decided by the agent, reviewed at the C1a checkpoint (2026-11-18):** `hdrBoundM`/`infoBoundM` kept as the
  mode-gated wrappers, re-indexed by the token (not renamed to `hdrBoundT`/`infoBoundT`), their `*_ctx` transfer lemmas
  deleted; `wpM`/`wpMLb` gate the token premise on their `on`; `RemoveMember`/`MemberList`/`checkLease*`/
  `checkMembershipOperationPermission` and the v3rpc guards (`AuthAdmin.*`, `authMaintenanceServer.*`,
  `kvServer.Compact`) gate on `E.authMode.isOn` (frames straight into their callees), the request specs on
  `E.authOn` (the Scope's text; `AEnv.authOn` unfolds to it); v3rpc's `leaseCheckT`/`principalBoundT` merged into
  `leaseCheckFrom`/`principalBound`; `Tracer.Start.spec`'s restatement (Scope §4.1's text) moved from 1b into C1a,
  with `StartLaws`/`EnsureTrace` (independent attack SOUND: `/shared/tmp/perheap/attack-tracer.md`);
  `authnRaft_on`/`revokeExpiredLeases` take some token from `libCtxOk` (`ctxToken_of_libCtxOk`: Authenticate reads
  none, the revoke's internal context carries whatever it carries).
