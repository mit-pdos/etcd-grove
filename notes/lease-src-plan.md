# The lease discharges' sources and the Lease service's registration (2026-11-02)

Spec-first, as `notes/lease-keepalive-plan.md`. Branch `lease-src`. After the lessor/auth list
(items 1-6 done), the first of the gaps they left (`notes/STATUS.md`, the keep-alive stream's
"Gaps"): no proof supplies the lease discharges' premises, and no served client can reach the
lease handlers.

## Scope (2026-11-02; the user's choices)

**What is missing.** `raftLeaseRead_server` and `raftLeaseRenew_server` (`v3rpc/Results.lean`)
discharge the handlers' contracts from the linked entry points, over:
- `srvAuthLeaseLb s E` (`LeaseCheck.lean`): the auth store's `IsAuthEnabled`, `Revision`,
  `IsAdminPermitted`, `IsPutPermitted`, `IsRangePermitted` with their verdicts no older than any
  lower bound of the published index. **No source.** `IsAdminPermitted` has no lower-bound spec.
- per call, `lessorRdOf γl` (a reader slot of the lessor's lock). `NewLessor` gives `2^30`, and
  `NewServer` keeps two (the store's and the apply thread's lease owners) and **drops the rest**.
- `srvLessorRd`, `srvPeerRt`, `srvHeaderFacts`: given since the keep-alive stage.

And `v3rpc.Server.spec` registers the KV, Watch and Auth services but **not the Lease service**:
its proof calls `NewQuotaLeaseServer` and `RegisterLeaseServer` and drops what they give.

**The user's choices (2026-11-02):**
- **"Sources + registration"**: both sources, and `v3rpc.Server.spec` restated to give the Lease
  service's registrations (`TimeToLive`, `Leases`, the `KeepAlive` stream) over the
  `*quotaLeaseServer`/`*LeaseServer` objects, as `kvRegs` does. A client example calling a lease
  read through a served server is the next stage.
- **"Both modes"**: `srvAuthLeaseLb` with auth off (from the store's exact triples) and with auth
  on (the store's invariant; a new `IsAdminPermitted.specLb` in the auth package, over the existing
  `lockedReadTx.specLb`).
- **"Thread pool"**: the lessor's remaining reader slots in a Perennial thread pool
  (`threadPool.init`), borrowed with the caller's thread token, as `lgMu`'s (J8a), following
  `notes/bounds-plan.md`; nothing added to the bounds count.

## The design

**The pool.** `lease.lessorRdPool γl` (persistent): `∃ γp, threadPool.isThreadPool N γp (lessorRdOf
γl)`. `NewServer`'s proof makes it from `NewLessor`'s slots less the two it keeps (`2^30 - 2 ≥
threadBound GF` since `threadBound GF ≤ 2^28`). No axiom changes: `NewLessor.spec` already gives the
`2^30` slots.

**Who borrows.** A request's goroutine has one thread token, and the lease checks already need it:
`Keys()` borrows a slot of the lease's own lock with it. So the slot can't be borrowed for the whole
call. The checks borrow it around each lessor call instead (`Lookup`, `Leases`): borrow (the token
for a slot), call, give back (the slot for the token), then `Keys()` with the token. The checks'
specs and the three entry points' specs take `lessorRdPool γl` (persistent) in place of
`lessorRdOf γl` (owned), and the discharges' per-call `S` loses `lessorRdOf γl`:
- `EtcdServer.checkLeaseTimeToLive.spec`, `checkLeaseRenew.spec`, `checkLeaseLeases.spec`;
- `EtcdServer.LeaseTimeToLive.spec`, `LeaseLeases.spec`, `LeaseRenew.spec`;
- `raftLeaseRead_of_server`, `raftLeaseRenew_of_server` and their `Results.lean` restatements.

`EtcdServer.leaseTimeToLive.spec` (the trust-boundary contract approved in item 2, an **axiom**) takes
`lessorRdOf γl ∗ threadTok` too: `LeaseTimeToLive` cannot borrow around it, since the contract needs
the token as well. So it takes the pool in place of the slot (a weaker premise, a stronger axiom:
true of Go, whose leader path calls `Lookup` and then `Keys()`, one after the other). **A trusted
statement**, for the user at Freeze.

The handler specs (`LeaseServer.*`) are over a contract at any `S` and do not change. **These are
frozen statements** (the lease-read, lease-renew and lease-grpc stages'): the restatement is for the
user's review at Freeze, with a `notes/decisions.md` entry.

Alternative rejected: `srvLessorRd` absorbing the pool (one fewer premise), because `srvLessorRd` is
the server's view of its lessor field, and the pool is the lease package's.

**`srvAuthLeaseLb`'s source.**
- *Auth off*: from `isServerReadM`'s `isAuthStore … .off` (the exact triples): `enabledVerdictFrom
  .off` is `b = false`, `adminVerdictFrom .off` is `err = nil` (`isAuthStore`'s `M.isOn = false →
  err = nil`), the permission checks the same. A lemma `srvAuthLeaseLb_off`, as `srvAuthLb_off`.
- *Auth on*: as `authStoreLbM` (E3s) comes from `IsRangePermitted.specLb` in `EtcdServer.start`
  (`srvUberBase`), an `authStoreLeaseLbM` from the five `specLb`s, in `srvUberBase` beside it, and
  `srvAuthLeaseLb_of_uberBase`. New: `auth.authStore.IsAdminPermitted.specLb` and its proof.
  `srvUberBase` is internal to the server (not a frozen spec); `EtcdServer.start`'s proof builds it.

**The registration.** `v3rpc.Server.spec`'s post gains `∀ x ∈ v3rpc.leaseRegs ql, x ∈ regs`,
`v3rpc.leaseKASReg ql ∈ sregs`, `quotaLeaseServerAt ql ⟨…LeaseServer…, #pl⟩ s ∗ leaseServerAt pl
s …` (what `NewQuotaLeaseServer` gives). A frozen spec too (the server start's item 4), the same
kind of change as the KV's and Auth's registrations.

## Draft (2026-11-02)

- `lease/InvLessor.lean`: `lessorPoolN`, `lessorRdPool γl`, `lessorRdPool_init` (`n` slots,
  `threadBound GF ≤ n + 1`), `lessorRdPool_borrow` (`pool ∗ threadTok ⊢ |={E}=> ▷ lessorRdOf γl ∗
  (lessorRdOf γl ={E}=∗ threadTok)`).
- The seven specs (`checkLease{TimeToLive,Renew,Leases}`, `Lease{TimeToLive,Leases,Renew}`, the
  axiom `leaseTimeToLive`): `lessorRdPool γl` in the pre in place of `lessorRdOf γl`, which leaves
  the post. The discharges (`ServerLeaseRead.lean`, `Results.lean`): `lessorRdPool γl` a premise, `S :=
  E.RD ∗ threadTok`, `S' := E.RD ∗ threadTok ∗ srvLgReader s ∗ srvReadReader s γr`.
- `NewServer.spec`/`specM`/`specG`: the posts end with `lease.lessorRdPool E.γ.leases`.
- `auth/FreshAdmin.lean` (new): `auth.adminVerdictFrom` (the body of `LeaseCheck.lean`'s, moved to the
  auth package) and `auth.authStore.IsAdminPermitted.specLb` (a non-nil `authInfo`; the passing
  verdict at a state no older than `n`), `wp_lb` over `IsAuthEnabled.specLb`, `lockedReadTx.specLb`,
  `hasRootRole.spec`.
- `etcdserver/AuthLeaseLb.lean` (new): `adminVerdictFrom` (now `auth.adminVerdictFrom`),
  `permCheck2Lb`, `isAuthStoreLeaseLb` moved from `LeaseCheck.lean` (unchanged otherwise), and
  `isAuthStoreLeaseLb_of_authInv` (from the five `specLb`s).
- `StoreLatest.lean`: `authStoreLbM`'s mode-on body gains `isAuthStoreLeaseLb st RD (.on γa) n`.
  `srvAuthLb` (which `Start.specOn` exports) carries it, so no spec of `Start` changes.
- `etcdserver/LeaseSrc.lean` (new): `srvAuthLeaseLb_of_server (hM : E.authMode = .off ∨ ∃ γa,
  E.authMode = .on γa) : isServerReadM E.authOn s E γr ∗ srvAuthLb s E ⊢ srvAuthLeaseLb s E`. (Drafted
  over `isServerReqM`, whose fields have only `AuthInfoFromCtx`: the store's exact triples are the
  read view's `isAuthStore`. Not in the mode `any`, whose checks may fail with errors that are not
  the auth package's: `isAuthStoreLeaseLb` asks `authApplyErrIs`.)
- The registration: `etcdserverpbDescs` (`cache/v3/Base.lean`) and `svcDescsOk` (`BaseStart.lean`)
  state the Lease descriptor's methods and stream exactly (`v3rpc.leaseDescMethods`, the
  generated literal of `rpc_grpc.pb.go:695-725`), as the Auth service's (E3zb); `InvGrpcStart.lean`:
  `v3rpc.leaseRegs ql` (the four methods), `v3rpc.leaseSReg ql` (`LeaseKeepAlive`), with
  `leaseRegs_sub`, `leaseSReg_mem`; `v3rpc.Server.spec`'s post: `ql pl lcid lmid`, both
  registrations, `quotaLeaseServerAt ql … s ∗ leaseServerAt pl s C.A lcid lmid` (both persistent).
- Left to the served stage: the generated `_Lease_LeaseTimeToLive_Handler` and
  `_Lease_LeaseLeases_Handler` are names only (`etcdserverpb.toml` translates Grant, Revoke and
  KeepAlive's), so a served client cannot run them yet.

## Probe (2026-11-02)

- **The hard one, `checkLeaseTimeToLive`** (proved over the restated spec): the slot borrowed from
  the pool before the steps that resolve `s.lessor.Lookup` (they strip the borrow's later), `Lookup`
  at it, the slot given back for the token, then `Keys()` with the token. The three returns no
  longer frame a slot. The pattern the other five proofs take.
- **The easy one, `srvAuthLeaseLb_of_server` with auth off**, by inspection: the lower-bound
  verdicts' mode-off bodies are the exact verdicts' (`enabledVerdictFrom .off` is `⌜b = false⌝`, as
  `enabledVerdict .off`; `permVerdictFrom`, `adminVerdictFrom` likewise), the permission checks
  already give `authApplyErrIs`, and `IsAdminPermitted`'s mode-off `err = nil` gives it by
  `authApplyErrIs_nil`. It found the Draft's premise wrong: the store's triples are the read view's
  (`isServerReadM`), not the request view's (restated above).
- **Cross-package unfolds**: `lease.lessorRdPool` (the lease package's, unfolded only in
  `InvLessor.lean`'s two lemmas; the checks use the lemma), `authStoreLbM` (two projection lemmas,
  `authStoreLbM_range`/`_lease`, replace the `rfl` unfolds in `Range`, `Txn`, `ReadOn`).
- **What remains for Prove**: the other five proofs (as the hard one); `IsAdminPermitted.wp_lb`;
  `isAuthStoreLeaseLb_of_authInv` and its five `specLb`s threaded through `AuthSrv`'s construction
  (its Draft `sorry`) up to the linking files; `srvAuthLeaseLb_of_server`; `NewServer`'s pool
  (`lessorRdPool_init` of `NewLessor`'s `2^30 - 2` spare slots) and its callers' patterns; the
  `v3rpc.Server` proof's export (`leaseRegs_sub`, `leaseSReg_mem`).

## Review (2026-11-02; `notes/lease-src-review.md`)

An independent spec reviewer, given the targets, their Go code and callers. No Go bug found.

- **F1 (fixed).** `lessor.Leases` (`lessor.go:472-477`) and `lessor.Renew` (`lessor.go:396-414`)
  take `le.mu` and then the lease locks, under one token: a slot held for the call and the token at
  once was a second thread's resource. Both now take the pool (`lessorRdPool γl`) and return
  nothing of it; `Renew` is an axiom, so this is a trusted restatement (Freeze).
- **F2 (fixed in the Probe).** The source is over `isServerReadM`, with the mode premise `hM`.
- **F3 (fixed).** The pool's `init` is a `threadBound` stock: `lessorRdPool_init` moved to
  `RdPool.lean`, an owner's match in `etc/bounds-allow.txt` (bounds 390, at the baseline).
- **F4 (open, the served stage).** The grpc model gives a served lease call no `threadTok` of its
  own; the run goroutine's token in `grpcHandlerOk` is the likely source.
- **F5 (fixed).** `leaseTimeToLive`'s docstring: the three lessor calls (`Remaining`, `Keys`,
  `Demoted`, `v3_server.go:636-675`) take the token one after another; a follower takes no lessor
  lock. The old and new premises are incomparable: a different trusted claim, not a weaker one.
- **F6 (fixed).** `checkLeaseLeases` takes no pool (it calls no lessor method under a slot).
- **F7 (partly).** `leaseDesc_nodup` added; merging `etcdserverpbDescs`' stream clause with the old
  `ClientStreams` one not done.
- **F8 (noted).** `AuthSrv`'s Draft `sorry` sits under every auth-on result until Prove threads the
  `specLb`s: no merge and no baseline update with it.
- **F9 (optional, not done).**

## Stages

Draft → Review (an independent spec reviewer) → Test → Probe (the hard proof: one check's borrow
and give-back around `Lookup`; the easy one: `srvAuthLeaseLb_off`) → Freeze (the user) → Prove. Draft, Review, Probe, Freeze (the user, 2026-11-02), Prove: done.
